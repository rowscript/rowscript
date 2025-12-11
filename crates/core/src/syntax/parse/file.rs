use chumsky::Parser;
use chumsky::input::ValueInput;
use chumsky::prelude::{IterParser, just};
use chumsky::primitive::select;

use crate::semantics::BuiltinType;
use crate::syntax::parse::expr::expr;
use crate::syntax::parse::stmt::stmt;
use crate::syntax::parse::{Keyword, Sym, SyntaxErr, Token, grouped_by, groups_with, id, name};
use crate::syntax::{
    Decl, Def, Expr, File, FuncSig, Ident, Member, MethodSig, Param, Sig, Stmt, TypeParam,
};
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

fn type_params<'t, I>() -> impl Parser<'t, I, Vec<Spanned<TypeParam>>, SyntaxErr<'t, Token>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    let param = just(Token::Sym(Sym::Ellipsis))
        .or_not()
        .map(|t| t.is_some())
        .then(id())
        .then(just(Token::Sym(Sym::Colon)).ignore_then(expr()).or_not())
        .map(|((variadic, id), constraint)| Spanned {
            span: id.span,
            item: TypeParam {
                variadic,
                typ: Ident::Id(id.item),
                constraint: constraint.unwrap_or(Spanned {
                    span: id.span,
                    item: Expr::BuiltinType(BuiltinType::Type),
                }),
            },
        })
        .labelled("type parameter");
    grouped_by(Sym::Lt, param, Sym::Comma, Sym::Gt)
        .or_not()
        .map(Option::unwrap_or_default)
        .labelled("type parameters")
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

    id().then(type_params())
        .then(params)
        .then(just(Token::Sym(Sym::Colon)).ignore_then(expr()).or_not())
        .then(
            stmt()
                .repeated()
                .collect::<Vec<_>>()
                .delimited_by(just(Token::Sym(Sym::LBrace)), just(Token::Sym(Sym::RBrace))),
        )
        .map(|((((id, type_params), params), ret), body)| {
            id.map(|name| Method {
                sig: FuncSig {
                    name,
                    type_params,
                    params,
                    ret,
                },
                body,
            })
        })
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

    docstring()
        .then_ignore(just(Token::Keyword(Keyword::Struct)))
        .then(id())
        .then(type_params())
        .then(groups_with(Sym::LBrace, member, Sym::RBrace))
        .map(|(((doc, id), type_params), items)| {
            id.map(|name| Decl {
                doc,
                sig: Sig::Struct {
                    name,
                    type_params,
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

    docstring()
        .then_ignore(just(Token::Keyword(Keyword::Extends)))
        .then(type_params())
        .then(expr())
        .then(groups_with(Sym::LBrace, method, Sym::RBrace))
        .map(|(((doc, type_params), target), items)| {
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
            Decl {
                doc,
                sig: Sig::Extends {
                    type_params,
                    target,
                    methods,
                },
                def: Def::Extends { bodies },
            }
        })
        .map_with(Spanned::from_map_extra)
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
