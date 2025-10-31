use chumsky::input::ValueInput;
use chumsky::prelude::IterParser;
use chumsky::{Parser, select};

use crate::Span;
use crate::syntax::parse::{SyntaxErr, Token};

pub(crate) fn docstring<'t, I>() -> impl Parser<'t, I, Vec<String>, SyntaxErr<'t, Token>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    select! {
        Token::Doc(s) => s
    }
    .repeated()
    .collect::<Vec<_>>()
    .labelled("docstring")
}
