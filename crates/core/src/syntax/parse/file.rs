use chumsky::Parser;
use chumsky::input::ValueInput;
use chumsky::prelude::{IterParser, just};
use chumsky::primitive::select;

use crate::syntax::parse::expr::expr;
use crate::syntax::parse::stmt::stmt;
use crate::syntax::parse::{Keyword, Sym, SyntaxErr, Token, grouped_by, id};
use crate::syntax::{Def, File, Ident, Member, Param, Sig};
use crate::{Span, Spanned};

fn docstring<'t, I>() -> impl Parser<'t, I, Vec<String>, SyntaxErr<'t, Token>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    select(|x, _| match x {
        Token::Doc(s) => Some(s),
        _ => None,
    })
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

fn r#static<'t, I>() -> impl Parser<'t, I, Spanned<Def>, SyntaxErr<'t, Token>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    docstring()
        .then_ignore(just(Token::Keyword(Keyword::Static)))
        .then(id())
        .then(just(Token::Sym(Sym::Colon)).ignore_then(expr()).or_not())
        .then_ignore(just(Token::Sym(Sym::Eq)))
        .then(expr())
        .map(|(((doc, id), typ), rhs)| {
            id.map(|name| Def::Static {
                doc: doc.into_boxed_slice(),
                name,
                typ,
                rhs,
            })
        })
        .labelled("static definition")
}

fn r#struct<'t, I>() -> impl Parser<'t, I, Spanned<Def>, SyntaxErr<'t, Token>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    let member = id()
        .then(just(Token::Sym(Sym::Colon)).ignore_then(expr()))
        .map(|(id, typ)| id.map(|name| Member { name, typ }))
        .labelled("member");

    docstring()
        .then_ignore(just(Token::Keyword(Keyword::Struct)))
        .then(id())
        .then(
            member
                .repeated()
                .collect::<Vec<_>>()
                .delimited_by(just(Token::Sym(Sym::LBrace)), just(Token::Sym(Sym::RBrace))),
        )
        .map(|((doc, id), members)| {
            id.map(|name| Def::Struct {
                doc: doc.into_boxed_slice(),
                name,
                members: members.into_boxed_slice(),
            })
        })
        .labelled("static definition")
}

pub(crate) fn file<'t, I>() -> impl Parser<'t, I, File, SyntaxErr<'t, Token>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    func()
        .or(r#static())
        .or(r#struct())
        .repeated()
        .collect::<Vec<_>>()
        .map(|defs| File {
            defs: defs.into(),
            main: None,
        })
        .labelled("file")
}
