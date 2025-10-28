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

struct Document {}

struct Service {
    client: Client,
    documents: DashMap<Url, Document>,
}

impl Service {
    fn new(client: Client) -> Self {
        Self {
            client,
            documents: Default::default(),
        }
    }
}

#[async_trait]
impl LanguageServer for Service {
    async fn initialize(&self, _: InitializeParams) -> JsonRpcResult<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
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
            .log_message(MessageType::INFO, "server successfully initialized")
            .await;
    }

    async fn shutdown(&self) -> JsonRpcResult<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.client
            .log_message(
                MessageType::INFO,
                format!("open: {}", params.text_document.uri),
            )
            .await;
        self.documents.insert(params.text_document.uri, Document {});
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        self.client
            .log_message(
                MessageType::INFO,
                format!("change: {}", params.text_document.uri),
            )
            .await;
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        self.client
            .log_message(
                MessageType::INFO,
                format!("save: {}", params.text_document.uri),
            )
            .await;
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        self.client
            .log_message(
                MessageType::INFO,
                format!("close: {}", params.text_document.uri),
            )
            .await;
        self.documents.remove(&params.text_document.uri);
    }
}
