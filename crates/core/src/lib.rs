use chumsky::Parser;
use chumsky::extra::ParserExtra;
use chumsky::input::{Input, MapExtra};
use chumsky::prelude::SimpleSpan;
use cranelift_module::ModuleError;
use ustr::Ustr;

use crate::semantics::check::Checker;
use crate::semantics::jit::Jit;
use crate::semantics::vm::Vm;
use crate::semantics::{Code, Func, Functions};
use crate::syntax::Expr;
use crate::syntax::parse::file;
use crate::syntax::parse::lex::lex;
use crate::syntax::resolve::Resolver;

#[allow(dead_code)]
pub(crate) mod semantics;
#[allow(dead_code)]
pub mod syntax;

#[cfg(test)]
mod tests;

pub type Span = SimpleSpan;

#[derive(Debug, Clone)]
pub struct Spanned<T> {
    span: Span,
    item: T,
}

impl<T> Spanned<T> {
    pub(crate) fn map<F, U>(self, f: F) -> Spanned<U>
    where
        F: FnOnce(T) -> U,
    {
        Spanned {
            span: self.span,
            item: f(self.item),
        }
    }

    pub(crate) fn from_map_extra<'src, 'b, I, E>(item: T, e: &mut MapExtra<'src, 'b, I, E>) -> Self
    where
        I: Input<'src, Span = Span>,
        E: ParserExtra<'src, I>,
    {
        Self {
            span: e.span(),
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

    Jit(Box<ModuleError>),
}

impl Error {
    fn jit(e: ModuleError) -> Self {
        Self::Jit(Box::new(e))
    }
}

pub type Out<T> = Result<T, Error>;

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

    pub fn text_range(&self, span: Span) -> LineCol {
        LineCol {
            start: self.position(span.start),
            end: self.position(span.end),
        }
    }

    pub fn token_range(&self, token: Span) -> LineCol {
        let span = if token.start < self.spans.len() {
            Span::new(self.spans[token.start].start, self.spans[token.end].end)
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
                character = 1;
                continue;
            }
            character += 1;
        }
        (line, character)
    }
}

#[derive(Default, Debug)]
pub struct State {
    prog: Func,
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
        state.prog.body = file()
            .parse(token_set.tokens.as_slice())
            .into_result()
            .map_err(|errs| {
                Error::Parsing(
                    errs.into_iter()
                        .map(|e| (*e.span(), e.reason().to_string()))
                        .collect(),
                )
            })?
            .into();
        Ok(state)
    }

    pub fn resolve(mut self) -> Out<Self> {
        Resolver::default().file(self.prog.body.as_mut())?;
        Ok(self)
    }

    pub fn check(mut self) -> Out<Self> {
        self.fs = Checker::default().file(self.prog.body.as_mut())?;
        Ok(self)
    }

    pub fn eval(&self) -> Expr {
        Vm::new(&self.fs).func(&self.prog.body, Default::default())
    }

    pub fn compile(&self) -> Out<Code> {
        Jit::new(&self.fs).compile()
    }
}
