use std::panic::catch_unwind;

use rowscript_core::{Ctx, Out};

use clap::{Parser, Subcommand};
use dashmap::DashMap;
use tokio::io::{stdin, stdout};
use tokio::runtime::Builder;
use tower_lsp::jsonrpc::Result as JsonRpcResult;
use tower_lsp::lsp_types::{
    DidChangeTextDocumentParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
    DidSaveTextDocumentParams, InitializeParams, InitializeResult, InitializedParams, MessageType,
    ServerCapabilities, ServerInfo, TextDocumentSyncCapability, TextDocumentSyncKind, Url,
};
use tower_lsp::{Client, LspService, Server};
use tower_lsp::{LanguageServer, async_trait};

fn main() {
    let app = App::parse();
    if let Some(Command::Server) = app.command {
        Builder::new_multi_thread()
            .enable_all()
            .build()
            .unwrap()
            .block_on(async {
                let (service, socket) = LspService::new(Service::new);
                Server::new(stdin(), stdout(), socket).serve(service).await;
            })
    }
}

#[derive(Parser)]
struct App {
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand)]
enum Command {
    Server,
}

#[allow(dead_code)]
struct Document {
    out: Out<()>,
}

struct Service {
    client: Client,
    docs: DashMap<Url, Document>,
}

#[async_trait]
impl LanguageServer for Service {
    async fn initialize(&self, _: InitializeParams) -> JsonRpcResult<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                // diagnostic_provider: Some(DiagnosticServerCapabilities::Options(
                //     DiagnosticOptions {
                //         identifier: Some(env!("CARGO_PKG_NAME").to_string()),
                //         inter_file_dependencies: true,
                //         ..Default::default()
                //     },
                // )),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: env!("CARGO_PKG_NAME").to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "Server successfully initialized")
            .await;
    }

    async fn shutdown(&self) -> JsonRpcResult<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.check(params.text_document.uri, params.text_document.text)
            .await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let Some(e) = params.content_changes.into_iter().next() else {
            return;
        };
        self.check(params.text_document.uri, e.text).await;
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        let Some(text) = params.text else { return };
        self.check(params.text_document.uri, text).await;
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        self.client
            .log_message(
                MessageType::INFO,
                format!("close: {}", params.text_document.uri),
            )
            .await;
        self.docs.remove(&params.text_document.uri);
    }
}

impl Service {
    fn new(client: Client) -> Self {
        Self {
            client,
            docs: Default::default(),
        }
    }

    async fn check(&self, uri: Url, text: String) {
        self.client
            .log_message(MessageType::INFO, format!("Checking file: {uri}"))
            .await;
        match catch_unwind(|| check(&text)) {
            Ok(out) => {
                self.docs.insert(uri, Document { out });
            }
            Err(..) => {
                self.client
                    .log_message(MessageType::ERROR, "check panics")
                    .await;
            }
        }
    }
}

fn check(text: &str) -> Out<()> {
    Ctx::new(text).parse()?.resolve()?.check()?;
    Ok(())
}
