use chumsky::Parser;
use chumsky::input::ValueInput;
use chumsky::prelude::{IterParser, just};
use chumsky::primitive::select;

use crate::syntax::parse::expr::expr;
use crate::syntax::parse::stmt::stmt;
use crate::syntax::parse::{Keyword, Sym, SyntaxErr, Token, grouped_by, id, name};
use crate::syntax::{Decl, Def, File, FuncSig, Id, Ident, Member, MethodSig, Param, Sig, Stmt};
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

struct Method {
    sig: FuncSig,
    body: Vec<Spanned<Stmt>>,
}

fn method<'t, I>() -> impl Parser<'t, I, Spanned<Method>, SyntaxErr<'t, Token>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    let param = id()
        .then(just(Token::Sym(Sym::Colon)).ignore_then(expr()))
        .map(|(id, typ)| {
            id.map(|name| Param {
                name: Ident::Id(name),
                typ,
            })
        })
        .labelled("parameter");

    let params = grouped_by(Sym::LParen, param, Sym::Comma, Sym::RParen).labelled("parameters");

    id().then(params)
        .then(just(Token::Sym(Sym::Colon)).ignore_then(expr()).or_not())
        .then(
            stmt()
                .repeated()
                .collect::<Vec<_>>()
                .delimited_by(just(Token::Sym(Sym::LBrace)), just(Token::Sym(Sym::RBrace))),
        )
        .map(|(((id, params), ret), body)| {
            id.map(|name| Method {
                sig: FuncSig { name, params, ret },
                body,
            })
        })
}

struct Braced<T> {
    doc: Vec<String>,
    id: Spanned<Id>,
    items: Vec<T>,
}

fn braced<'t, I, O, P>(kw: Keyword, item: P) -> impl Parser<'t, I, Braced<O>, SyntaxErr<'t, Token>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
    P: Parser<'t, I, O, SyntaxErr<'t, Token>>,
{
    docstring()
        .then_ignore(just(Token::Keyword(kw)))
        .then(id())
        .then(
            item.repeated()
                .collect::<Vec<_>>()
                .delimited_by(just(Token::Sym(Sym::LBrace)), just(Token::Sym(Sym::RBrace))),
        )
        .map(|((doc, id), items)| Braced { doc, id, items })
}

fn func<'t, I>() -> impl Parser<'t, I, Spanned<Decl>, SyntaxErr<'t, Token>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    docstring()
        .then_ignore(just(Token::Keyword(Keyword::Function)))
        .then(method())
        .map(|(doc, method)| {
            method.map(|m| Decl {
                doc,
                sig: Sig::Func(m.sig),
                def: Def::Func { body: m.body },
            })
        })
        .labelled("function definition")
}

fn r#static<'t, I>() -> impl Parser<'t, I, Spanned<Decl>, SyntaxErr<'t, Token>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    docstring()
        .then_ignore(just(Token::Keyword(Keyword::Static)))
        .then(id())
        .then(just(Token::Sym(Sym::Colon)).ignore_then(expr()))
        .then_ignore(just(Token::Sym(Sym::Eq)))
        .then(expr())
        .map(|(((doc, id), typ), rhs)| {
            id.map(|name| Decl {
                doc,
                sig: Sig::Static { name, typ },
                def: Def::Static { rhs },
            })
        })
        .labelled("static definition")
}

fn r#struct<'t, I>() -> impl Parser<'t, I, Spanned<Decl>, SyntaxErr<'t, Token>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    let member = name()
        .then(just(Token::Sym(Sym::Colon)).ignore_then(expr()))
        .map(|(name, typ)| name.map(|name| Member { name, typ }))
        .labelled("member");

    braced(Keyword::Struct, member)
        .map(|Braced { doc, id, items }| {
            id.map(|name| Decl {
                doc,
                sig: Sig::Struct {
                    name,
                    members: items,
                },
                def: Def::Struct,
            })
        })
        .labelled("struct definition")
}

fn extends<'t, I>() -> impl Parser<'t, I, Spanned<Decl>, SyntaxErr<'t, Token>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    let method = docstring().then(method()).labelled("method definition");

    braced(Keyword::Extends, method)
        .map(|Braced { doc, id, items }| {
            let (methods, bodies) = items
                .into_iter()
                .map(|(doc, m)| {
                    (
                        Spanned {
                            span: m.span,
                            item: MethodSig {
                                doc,
                                sig: m.item.sig,
                            },
                        },
                        m.item.body,
                    )
                })
                .collect::<(Vec<_>, Vec<_>)>();
            id.map(|target| Decl {
                doc,
                sig: Sig::Extends {
                    target: Ident::Id(target),
                    methods,
                },
                def: Def::Extends { bodies },
            })
        })
        .labelled("extends definition")
}

pub(crate) fn file<'t, I>() -> impl Parser<'t, I, File, SyntaxErr<'t, Token>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    func()
        .or(r#static())
        .or(r#struct())
        .or(extends())
        .repeated()
        .collect::<Vec<_>>()
        .map(|decls| File { decls, main: None })
        .labelled("file")
}
