use std::collections::HashMap;

use chumsky::Parser;
use chumsky::extra::ParserExtra;
use chumsky::input::{Input, MapExtra};
use chumsky::prelude::SimpleSpan;
use ustr::Ustr;

use crate::semantics::Func;
use crate::semantics::check::Checker;
use crate::semantics::vm::VM;
use crate::syntax::parse::{file, lex};
use crate::syntax::resolve::Resolver;
use crate::syntax::{Expr, Name};

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
}

type Out<T> = Result<T, Error>;

#[allow(dead_code)]
#[derive(Default)]
pub struct Ctx<'src> {
    text: &'src str,
    file: Func,
    fns: HashMap<Name, Func>,
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

    pub fn parse(&mut self) -> Out<&mut Self> {
        self.file = Func::of_file(
            lex()
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
                })?,
        );
        Ok(self)
    }

    pub fn resolve(&mut self) -> Out<&mut Self> {
        Resolver::default().file(self.file.body.as_mut())?;
        Ok(self)
    }

    pub fn check(&mut self) -> Out<&mut Self> {
        self.fns = Checker::default().file(self.file.body.as_mut())?;
        Ok(self)
    }

    pub fn eval(&self) -> Expr {
        VM::new(&self.fns).func(&self.file, Default::default())
    }
}
