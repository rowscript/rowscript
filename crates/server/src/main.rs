use std::panic::catch_unwind;

use rowscript_core::{Error, LineCol, Source, State};

use clap::{Parser, Subcommand};
use dashmap::DashMap;
use tokio::io::{stdin, stdout};
use tokio::runtime::Builder;
use tower_lsp::jsonrpc::Result as JsonRpcResult;
use tower_lsp::lsp_types::{
    Diagnostic, DiagnosticOptions, DiagnosticServerCapabilities, DiagnosticSeverity,
    DidChangeTextDocumentParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
    DidSaveTextDocumentParams, DocumentDiagnosticParams, DocumentDiagnosticReport,
    DocumentDiagnosticReportResult, FullDocumentDiagnosticReport, InitializeParams,
    InitializeResult, InitializedParams, MessageType, Position, Range,
    RelatedFullDocumentDiagnosticReport, ServerCapabilities, ServerInfo,
    TextDocumentSyncCapability, TextDocumentSyncKind, Url,
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
                diagnostic_provider: Some(DiagnosticServerCapabilities::Options(
                    DiagnosticOptions {
                        identifier: Some(env!("CARGO_PKG_NAME").to_string()),
                        inter_file_dependencies: true,
                        ..Default::default()
                    },
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

    async fn diagnostic(
        &self,
        params: DocumentDiagnosticParams,
    ) -> JsonRpcResult<DocumentDiagnosticReportResult> {
        Ok(DocumentDiagnosticReportResult::Report(
            DocumentDiagnosticReport::Full(RelatedFullDocumentDiagnosticReport {
                related_documents: None,
                full_document_diagnostic_report: self
                    .docs
                    .get(&params.text_document.uri)
                    .map(|doc| FullDocumentDiagnosticReport {
                        result_id: None,
                        items: doc.diags.clone(),
                    })
                    .unwrap_or_default(),
            }),
        ))
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
        match catch_unwind(|| check_text(&text)) {
            Ok(diags) => {
                self.docs.insert(uri, Document { diags });
            }
            Err(..) => {
                self.client
                    .log_message(MessageType::ERROR, "Check panics")
                    .await;
            }
        }
    }
}

#[allow(dead_code)]
struct Document {
    diags: Vec<Diagnostic>,
}

fn new_diag(lc: LineCol, severity: DiagnosticSeverity, message: String) -> Diagnostic {
    Diagnostic {
        range: lc.into_lsp(),
        severity: Some(severity),
        source: Some("RowScript".to_string()),
        message,
        ..Default::default()
    }
}

fn check_text(text: &str) -> Vec<Diagnostic> {
    let mut src = Source::new(text);
    let Err(e) = State::parse_with(&mut src)
        .and_then(State::resolve)
        .and_then(State::check)
    else {
        return Default::default();
    };
    match e {
        Error::Lexing(errs) => errs
            .into_iter()
            .map(|(span, msg)| new_diag(src.text_range(span), DiagnosticSeverity::ERROR, msg))
            .collect(),
        Error::Parsing(errs) => errs
            .into_iter()
            .map(|(span, msg)| new_diag(src.token_range(span), DiagnosticSeverity::ERROR, msg))
            .collect(),
        Error::UndefName(span, n) => {
            vec![new_diag(
                src.token_range(span),
                DiagnosticSeverity::ERROR,
                format!("Undefined variable \"{n}\""),
            )]
        }
        Error::TypeMismatch { span, got, want } => {
            vec![new_diag(
                src.token_range(span),
                DiagnosticSeverity::ERROR,
                format!(
                    r#"Type mismatch:

Expected:
    {want}
Actual:
    {got}"#
                ),
            )]
        }
        Error::ArityMismatch { span, got, want } => {
            vec![new_diag(
                src.token_range(span),
                DiagnosticSeverity::ERROR,
                format!(
                    r#"Arity mismatch:

Expected:
    {want}
Actual:
    {got}"#
                ),
            )]
        }
        Error::Jit(..) => unreachable!(),
    }
}

trait LspRange {
    fn into_lsp(self) -> Range;
}

impl LspRange for LineCol {
    fn into_lsp(self) -> Range {
        Range {
            start: Position::new(self.start.0, self.start.1),
            end: Position::new(self.end.0, self.end.1),
        }
    }
}
