use chumsky::container::Container;
use chumsky::extra::Err as Full;
use chumsky::input::ValueInput;
use chumsky::prelude::{IterParser, Rich, just};
use chumsky::{Parser, select};
use strum::{Display, EnumString};
use ustr::Ustr;

use crate::syntax::{BuiltinType, Id};
use crate::{Span, Spanned};

pub(crate) mod expr;
pub(crate) mod file;
pub(crate) mod lex;
pub(crate) mod stmt;

pub(crate) type SyntaxErr<'a, T> = Full<Rich<'a, T, Span>>;

#[derive(Debug, Eq, PartialEq, Clone, EnumString, Display)]
#[strum(serialize_all = "lowercase")]
pub(crate) enum Keyword {
    Let,
    Function,
    If,
    Else,
    Return,
    While,
}

#[derive(Debug, Eq, PartialEq, Clone, Display)]
pub enum Sym {
    // Long.
    EqEq,
    Le,
    Ge,

    // Short.
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
    Colon,
    Eq,
    Lt,
    Gt,
    Plus,
    Minus,
    Mul,
}

#[derive(Debug, Eq, PartialEq, Clone, Display)]
pub(crate) enum Token {
    #[strum(transparent)]
    Number(Ustr),
    #[strum(transparent)]
    String(Ustr), // TODO: short (interned) and long strings
    #[strum(transparent)]
    Boolean(bool),
    #[strum(transparent)]
    Ident(Id),
    #[strum(transparent)]
    Doc(String),
    #[strum(transparent)]
    Sym(Sym),
    #[strum(transparent)]
    BuiltinType(BuiltinType),
    #[strum(transparent)]
    Keyword(Keyword),
}

#[derive(Default)]
pub struct TokenSet {
    pub(crate) spans: Vec<Span>,
    pub(crate) tokens: Vec<Token>,
}

impl Container<Spanned<Token>> for TokenSet {
    fn with_capacity(n: usize) -> Self {
        Self {
            spans: Vec::with_capacity(n),
            tokens: Vec::with_capacity(n),
        }
    }

    fn push(&mut self, Spanned { span, item }: Spanned<Token>) {
        self.spans.push(span);
        self.tokens.push(item);
    }
}

fn id<'t, I>() -> impl Parser<'t, I, Spanned<Id>, SyntaxErr<'t, Token>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    select! {
        Token::Ident(n) => n
    }
    .map_with(Spanned::from_map_extra)
    .labelled("identifier")
}

fn grouped_by<'t, I, O, P>(
    lhs: Sym,
    parser: P,
    sep: Sym,
    rhs: Sym,
) -> impl Parser<'t, I, Vec<O>, SyntaxErr<'t, Token>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = Span>,
    P: Parser<'t, I, O, SyntaxErr<'t, Token>> + Clone,
{
    parser
        .separated_by(just(Token::Sym(sep)))
        .allow_trailing()
        .collect()
        .delimited_by(just(Token::Sym(lhs)), just(Token::Sym(rhs)))
}
