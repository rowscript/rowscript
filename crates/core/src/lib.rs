pub(crate) mod semantics;
pub mod syntax;
#[cfg(test)]
mod tests;

use std::path::Path;

use chumsky::Parser;
use chumsky::extra::ParserExtra;
use chumsky::input::{Input, MapExtra};
use chumsky::prelude::SimpleSpan;
use cranelift::codegen::gimli::write::Error as DebugInfoError;
use cranelift_module::ModuleError;
use object::read::Error as ModifyObjectError;
use object::write::Error as WriteObjectError;
use ustr::Ustr;

use crate::semantics::Functions;
use crate::semantics::check::Checker;
use crate::semantics::jit::{Code, Jit};
use crate::semantics::vm::Vm;
use crate::syntax::parse::file::file;
use crate::syntax::parse::lex::lex;
use crate::syntax::resolve::Resolver;
use crate::syntax::{Def, Expr, File, Ident, Stmt};

pub type Span = SimpleSpan;

#[derive(Debug, Clone)]
pub struct Spanned<T> {
    span: Span,
    item: T,
}

impl<T> Spanned<T> {
    fn map<F, U>(self, f: F) -> Spanned<U>
    where
        F: FnOnce(T) -> U,
    {
        Spanned {
            span: self.span,
            item: f(self.item),
        }
    }

    fn from_map_extra<'src, 'b, I, E>(item: T, e: &mut MapExtra<'src, 'b, I, E>) -> Self
    where
        I: Input<'src, Span = Span>,
        E: ParserExtra<'src, I>,
    {
        Self {
            span: e.span(),
            item,
        }
    }

    fn stdin(item: T) -> Self {
        Self {
            span: Span::new(0, 0),
            item,
        }
    }
}

#[derive(Debug)]
pub enum Error {
    Lexing(Box<[(Span, String)]>),
    Parsing(Box<[(Span, String)]>),

    UndefName(Span, Ustr),

    TypeMismatch {
        span: Span,
        got: String,
        want: String,
    },
    ArityMismatch {
        span: Span,
        got: usize,
        want: usize,
    },

    ExpectedMain,

    Jit(Box<ModuleError>),
    WriteObject(WriteObjectError),
    ModifyObject(ModifyObjectError),
    EmitDebugInfo(DebugInfoError),
}

impl Error {
    fn jit(e: ModuleError) -> Self {
        Self::Jit(Box::new(e))
    }
}

pub type Out<T> = Result<T, Error>;

#[derive(Default)]
pub struct LineCol {
    pub start: (u32, u32),
    pub end: (u32, u32),
}

#[derive(Debug)]
pub struct Source<'src> {
    text: &'src str,
    spans: Box<[Span]>,
    lines: Box<[usize]>,
}

impl<'src> Source<'src> {
    pub fn new(text: &'src str) -> Self {
        let mut lines = vec![0];
        for (i, ch) in text.char_indices() {
            if ch == '\n' {
                lines.push(i + 1);
            }
        }
        Self {
            text,
            spans: Default::default(),
            lines: lines.into(),
        }
    }

    pub fn explain(&self, e: Error) -> Vec<(Option<LineCol>, String)> {
        match e {
            Error::Lexing(errs) => errs
                .into_iter()
                .map(|(span, msg)| (Some(self.text_range(span)), msg))
                .collect(),
            Error::Parsing(errs) => errs
                .into_iter()
                .map(|(span, msg)| (Some(self.token_range(span)), msg))
                .collect(),
            Error::UndefName(span, n) => {
                vec![(
                    Some(self.token_range(span)),
                    format!("Undefined variable '{n}'"),
                )]
            }
            Error::TypeMismatch { span, got, want } => {
                vec![(
                    Some(self.token_range(span)),
                    format!("Type mismatch: Expected '{want}', but got '{got}'"),
                )]
            }
            Error::ArityMismatch { span, got, want } => {
                vec![(
                    Some(self.token_range(span)),
                    format!("Arity mismatch: Expected '{want}', but got '{got}'"),
                )]
            }
            Error::ExpectedMain => vec![(None, "No 'main' function to run or compile".into())],
            Error::Jit(e) => vec![(None, format!("Compile error: {e}"))],
            Error::WriteObject(e) => vec![(None, format!("Serialize object error: {e}"))],
            Error::ModifyObject(e) => vec![(None, format!("Modify object error: {e}"))],
            Error::EmitDebugInfo(e) => vec![(None, format!("Emit debug info error: {e}"))],
        }
    }

    pub fn print(&self, file: &Path, e: Error) {
        self.explain(e).iter().for_each(|(span, msg)| match span {
            None => eprintln!("{}: {msg}", file.display()),
            Some(span) => eprintln!(
                "{}:{}:{}: {msg}",
                file.display(),
                span.start.0 + 1,
                span.start.1 + 1
            ),
        })
    }

    fn text_range(&self, span: Span) -> LineCol {
        let search = |pos| match self.lines.binary_search(&pos) {
            Ok(line) => (line as _, 0),
            Err(line) => {
                let start = self.lines[line - 1];
                ((line - 1) as _, (pos - start) as _)
            }
        };
        LineCol {
            start: search(span.start),
            end: search(span.end),
        }
    }

    fn token_range(&self, token: Span) -> LineCol {
        let span = if token.start < self.spans.len() {
            self.spans[token.start]
        } else if let Some(last) = self.spans.last() {
            Span::new(last.end, last.end)
        } else {
            Span::new(0, 0)
        };
        self.text_range(span)
    }
}

#[derive(Debug)]
pub struct State<'src> {
    pub src: Source<'src>,
    file: File,
    fs: Functions,
}

impl<'src> State<'src> {
    pub fn new(text: &'src str) -> Self {
        Self {
            src: Source::new(text),
            file: Default::default(),
            fs: Default::default(),
        }
    }

    pub fn parse(&mut self) -> Out<()> {
        let token_set = lex().parse(self.src.text).into_result().map_err(|errs| {
            Error::Lexing(
                errs.into_iter()
                    .map(|e| (*e.span(), e.reason().to_string()))
                    .collect(),
            )
        })?;
        self.src.spans = token_set.spans.into();
        self.file = file()
            .parse(token_set.tokens.as_slice())
            .into_result()
            .map_err(|errs| {
                Error::Parsing(
                    errs.into_iter()
                        .map(|e| (*e.span(), e.reason().to_string()))
                        .collect(),
                )
            })?;
        Ok(())
    }

    pub fn resolve(&mut self) -> Out<()> {
        Resolver::default().file(&mut self.file)
    }

    pub fn check(&mut self) -> Out<()> {
        self.fs = Checker::default().file(&mut self.file)?;
        Ok(())
    }

    pub fn eval_nth(&self, n: usize, arg: Expr) -> Expr {
        let Def::Func { sig, .. } = &self.file.defs[n].item;
        let stmts = &[Spanned::stdin(Stmt::Expr(Expr::Call(
            Box::new(Spanned::stdin(Expr::Ident(Ident::Id(sig.name.clone())))),
            Box::new([Spanned::stdin(arg)]),
        )))];
        Vm::new(&self.fs).func(stmts, Default::default())
    }

    pub fn eval(&self) -> Out<Expr> {
        let main = self.file.main.as_ref().ok_or(Error::ExpectedMain)?;
        Ok(Vm::new(&self.fs).func(&self.fs.get(main).unwrap().item.body, Default::default()))
    }

    pub fn compile(&self, path: &Path) -> Out<Code> {
        Jit::new(path, &self.fs, self.file.main.as_ref().cloned()).compile()
    }
}
