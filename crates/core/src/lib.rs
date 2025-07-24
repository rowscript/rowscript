use chumsky::extra::ParserExtra;
use chumsky::input::{Input, MapExtra};
use chumsky::prelude::SimpleSpan;
use ustr::Ustr;

#[allow(dead_code)]
mod semantics;
#[allow(dead_code)]
pub(crate) mod syntax;

#[cfg(test)]
mod tests;

#[allow(dead_code)]
struct Uri(Ustr);

impl Default for Uri {
    fn default() -> Self {
        Self("<stdin>".into())
    }
}

#[allow(dead_code)]
#[derive(Default)]
struct Loc {
    uri: Uri,
}

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
struct Spanned<T> {
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

#[allow(dead_code)]
#[derive(Debug)]
enum Error {
    Lexing(Box<[(Span, String)]>),
    Parsing(Box<[Span]>, Box<[(Span, String)]>),
    UndefName(Span, Ustr),
}

type Out<T> = Result<T, Error>;
