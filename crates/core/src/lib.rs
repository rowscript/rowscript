use chumsky::Parser;
use chumsky::extra::ParserExtra;
use chumsky::input::{Input, MapExtra};
use chumsky::prelude::SimpleSpan;
use cranelift_module::ModuleError;
use ustr::Ustr;

use crate::semantics::check::Checker;
use crate::semantics::vm::VM;
use crate::semantics::{Func, Functions};
use crate::syntax::Expr;
use crate::syntax::parse::file;
use crate::syntax::parse::lex::lex;
use crate::syntax::resolve::Resolver;

#[allow(dead_code)]
pub(crate) mod semantics;
#[allow(dead_code)]
pub(crate) mod syntax;

#[cfg(test)]
mod tests;

type Span = SimpleSpan;

#[allow(dead_code)]
pub(crate) fn line_col(span: &Span, text: &str) -> (usize, usize) {
    let mut line = 1;
    let mut col = 1;
    for (i, c) in text.chars().enumerate() {
        if i == span.start {
            break;
        }
        if c == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

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
    Parsing(Box<[Span]>, Box<[(Span, String)]>),

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

type Out<T> = Result<T, Error>;

#[allow(dead_code)]
#[derive(Default)]
pub struct Ctx<'src> {
    text: &'src str,
    file: Func,
    fs: Functions,
}

#[allow(dead_code)]
impl<'src> Ctx<'src> {
    pub fn new(text: &'src str) -> Self {
        Self {
            text,
            ..Default::default()
        }
    }

    fn run(text: &'src str) -> Expr {
        Self::new(text)
            .parse()
            .unwrap()
            .resolve()
            .unwrap()
            .check()
            .unwrap()
            .eval()
    }

    pub fn parse(mut self) -> Out<Self> {
        self.file.body = lex()
            .parse(self.text)
            .into_result()
            .map_err(|errs| {
                Error::Lexing(
                    errs.into_iter()
                        .map(|e| (*e.span(), e.reason().to_string()))
                        .collect(),
                )
            })
            .and_then(|tokens| {
                file()
                    .parse(tokens.tokens.as_slice())
                    .into_result()
                    .map_err(|errs| {
                        Error::Parsing(
                            tokens.spans.into(),
                            errs.into_iter()
                                .map(|e| (*e.span(), e.reason().to_string()))
                                .collect(),
                        )
                    })
            })?
            .into();
        Ok(self)
    }

    pub fn resolve(mut self) -> Out<Self> {
        Resolver::default().file(self.file.body.as_mut())?;
        Ok(self)
    }

    pub fn check(mut self) -> Out<Self> {
        self.fs = Checker::default().file(self.file.body.as_mut())?;
        Ok(self)
    }

    pub fn eval(&self) -> Expr {
        VM::new(&self.fs).func(&self.file.body, Default::default())
    }
}
