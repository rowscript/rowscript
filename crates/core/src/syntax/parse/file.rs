use chumsky::input::ValueInput;
use chumsky::prelude::{IterParser, just};
use chumsky::{Parser, select};

use crate::syntax::parse::expr::expr;
use crate::syntax::parse::stmt::stmt;
use crate::syntax::parse::{Keyword, Sym, SyntaxErr, Token, grouped_by, id};
use crate::syntax::{Def, File, Ident, Param, Sig};
use crate::{Span, Spanned};

fn docstring<'t, I>() -> impl Parser<'t, I, Vec<String>, SyntaxErr<'t, Token>> + Clone
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

fn func<'t, I>() -> impl Parser<'t, I, Spanned<Def>, SyntaxErr<'t, Token>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    let param = id()
        .then(just(Token::Sym(Sym::Colon)).ignore_then(expr()).or_not())
        .map(|(id, typ)| {
            id.map(|name| Param {
                name: Ident::Id(name),
                typ,
            })
        })
        .labelled("parameter");

    let params = grouped_by(Sym::LParen, param, Sym::Comma, Sym::RParen).labelled("parameters");

    docstring()
        .then_ignore(just(Token::Keyword(Keyword::Function)))
        .then(id())
        .then(params)
        .then(just(Token::Sym(Sym::Colon)).ignore_then(expr()).or_not())
        .then(
            stmt()
                .repeated()
                .collect::<Vec<_>>()
                .delimited_by(just(Token::Sym(Sym::LBrace)), just(Token::Sym(Sym::RBrace))),
        )
        .map(|((((doc, id), params), ret), body)| {
            id.map(|name| Def::Func {
                sig: Sig {
                    doc: doc.into_boxed_slice(),
                    name,
                    params: params.into_boxed_slice(),
                    ret,
                },
                body: body.into_boxed_slice(),
            })
        })
        .labelled("function definition")
}

pub(crate) fn file<'t, I>() -> impl Parser<'t, I, File, SyntaxErr<'t, Token>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    func()
        .repeated()
        .collect::<Vec<_>>()
        .map(|defs| File {
            defs: defs.into(),
            main: None,
        })
        .labelled("file")
}
