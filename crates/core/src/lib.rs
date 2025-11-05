pub(crate) mod semantics;
pub mod syntax;
#[cfg(test)]
mod tests;

use std::io::Error as IoError;

use chumsky::Parser;
use chumsky::extra::ParserExtra;
use chumsky::input::{Input, MapExtra};
use chumsky::prelude::SimpleSpan;
use cranelift_module::ModuleError;
use cranelift_object::object::write::Error as ObjectWriteError;
use libloading::{Error as LoadError, Library, Symbol};
use std::path::Path;
use ustr::Ustr;

use crate::semantics::Functions;
use crate::semantics::check::Checker;
use crate::semantics::jit::Jit;
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
    Emit(ObjectWriteError),
    Io(Box<Path>, IoError),

    Load(LoadError),
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

pub struct Source<'src> {
    text: &'src str,
    spans: Box<[Span]>,
}

impl<'src> Source<'src> {
    pub fn new(text: &'src str) -> Self {
        Self {
            text,
            spans: Default::default(),
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
            Error::Emit(e) => vec![(None, format!("Emit object file error: {e}"))],
            Error::Io(path, e) => vec![(None, format!("IO error on path {}: {e}", path.display()))],
            Error::Load(e) => vec![(None, format!("Load object error: {e}"))],
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
        LineCol {
            start: self.position(span.start),
            end: self.position(span.end),
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

    fn position(&self, pos: usize) -> (u32, u32) {
        let mut line = 0;
        let mut character = 0;
        for (i, c) in self.text.chars().enumerate() {
            if i == pos {
                break;
            }
            if c == '\n' {
                line += 1;
                character = 0;
                continue;
            }
            character += 1;
        }
        (line, character)
    }
}

#[derive(Default, Debug)]
pub struct State {
    file: File,
    fs: Functions,
}

impl State {
    pub fn parse(text: &str) -> Out<Self> {
        let mut src = Source::new(text);
        Self::parse_with(&mut src)
    }

    pub fn parse_with(src: &mut Source) -> Out<Self> {
        let mut state = Self::default();
        let token_set = lex().parse(src.text).into_result().map_err(|errs| {
            Error::Lexing(
                errs.into_iter()
                    .map(|e| (*e.span(), e.reason().to_string()))
                    .collect(),
            )
        })?;
        src.spans = token_set.spans.into();
        state.file = file()
            .parse(token_set.tokens.as_slice())
            .into_result()
            .map_err(|errs| {
                Error::Parsing(
                    errs.into_iter()
                        .map(|e| (*e.span(), e.reason().to_string()))
                        .collect(),
                )
            })?;
        Ok(state)
    }

    pub fn resolve(mut self) -> Out<Self> {
        Resolver::default().file(&mut self.file)?;
        Ok(self)
    }

    pub fn check(mut self) -> Out<Self> {
        self.fs = Checker::default().file(&mut self.file)?;
        Ok(self)
    }

    pub fn eval_nth(&self, n: usize, arg: Expr) -> Expr {
        let Def::Func { sig, .. } = &self.file.defs[n].item;
        let stmts = &[Spanned::stdin(Stmt::Expr(Expr::Call(
            Box::new(Spanned::stdin(Expr::Ident(Ident::Id(sig.name.clone())))),
            Box::new([Spanned::stdin(arg)]),
        )))];
        Vm::new(&self.fs).func(stmts, Default::default())
    }

    pub fn eval(self) -> Out<Expr> {
        let main = self.file.main.as_ref().ok_or(Error::ExpectedMain)?;
        Ok(Vm::new(&self.fs).func(&self.fs.get(main).unwrap().item.body, Default::default()))
    }

    pub fn compile(self, path: &Path) -> Out<Self> {
        Jit::new(&self.fs).compile(path)?;
        Ok(self)
    }

    pub fn load(&self, path: &Path) -> Out<()> {
        unsafe {
            let lib = Library::new(path.with_extension("obj")).map_err(Error::Load)?;
            let main = lib
                .get::<Symbol<extern "C" fn() -> u8>>(b"main")
                .map_err(Error::Load)?;
            main();
        }
        Ok(())
    }
}
