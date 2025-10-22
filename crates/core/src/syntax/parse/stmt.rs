use chumsky::input::ValueInput;
use chumsky::prelude::{IterParser, just, recursive};
use chumsky::{Parser, select};

use crate::syntax::parse::expr::expr;
use crate::syntax::parse::{Keyword, Sym, SyntaxErr, Token, grouped_by};
use crate::syntax::{Branch, Ident, Param, Sig, Stmt};
use crate::{Span, Spanned};

pub(crate) fn stmt<'t, I>() -> impl Parser<'t, I, Spanned<Stmt>, SyntaxErr<'t, Token>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    let doc = select! {
        Token::Doc(s) => s
    }
    .repeated()
    .collect::<Vec<_>>()
    .labelled("docstring");

    let id = select! {
        Token::Ident(n) => n
    }
    .map_with(Spanned::from_map_extra)
    .labelled("identifier");

    let param = id
        .then(just(Token::Sym(Sym::Colon)).ignore_then(expr()).or_not())
        .map(|(id, typ)| {
            id.map(|name| Param {
                name: Ident::Id(name),
                typ,
            })
        })
        .labelled("parameter");

    let params = grouped_by(Sym::LParen, param, Sym::Comma, Sym::RParen).labelled("parameters");

    let assign = doc
        .then_ignore(just(Token::Keyword(Keyword::Let)))
        .then(id)
        .then(just(Token::Sym(Sym::Colon)).ignore_then(expr()).or_not())
        .then_ignore(just(Token::Sym(Sym::Eq)))
        .then(expr())
        .map(|(((doc, id), typ), rhs)| Stmt::Assign {
            doc: doc.into_boxed_slice(),
            name: id.map(Ident::Id),
            typ,
            rhs,
        })
        .map_with(Spanned::from_map_extra)
        .labelled("assignment statement");

    let update = id
        .then_ignore(just(Token::Sym(Sym::Eq)))
        .then(expr())
        .map(|(id, rhs)| Stmt::Update {
            name: id.map(Ident::Id),
            rhs,
        })
        .map_with(Spanned::from_map_extra)
        .labelled("update statement");

    let return_ = just(Token::Keyword(Keyword::Return))
        .ignore_then(expr().or_not())
        .map(Stmt::Return)
        .map_with(Spanned::from_map_extra)
        .labelled("return statement");

    let expr_ = expr()
        .map(|e| e.map(Stmt::Expr))
        .labelled("expression statement");

    recursive(|stmt| {
        let stmts = stmt.repeated().collect::<Vec<_>>().labelled("statements");

        let func = doc
            .then_ignore(just(Token::Keyword(Keyword::Function)))
            .then(id)
            .then(params)
            .then(just(Token::Sym(Sym::Colon)).ignore_then(expr()).or_not())
            .then(
                stmts
                    .clone()
                    .delimited_by(just(Token::Sym(Sym::LBrace)), just(Token::Sym(Sym::RBrace))),
            )
            .map(|((((doc, id), params), ret), body)| {
                id.map(|name| Stmt::Func {
                    short: false,
                    sig: Sig {
                        doc: doc.into_boxed_slice(),
                        name,
                        params: params.into_boxed_slice(),
                        ret,
                    },
                    body: body.into_boxed_slice(),
                })
            })
            .labelled("function statement");

        let branch = just(Token::Keyword(Keyword::If))
            .map_with(|_, e| e.span())
            .then(expr())
            .then(
                stmts
                    .clone()
                    .delimited_by(just(Token::Sym(Sym::LBrace)), just(Token::Sym(Sym::RBrace))),
            )
            .map(|((span, cond), body)| Branch {
                span,
                cond,
                body: body.into_boxed_slice(),
            })
            .labelled("if branch");

        let if_ =
            branch
                .clone()
                .then(
                    just(Token::Keyword(Keyword::Else))
                        .ignore_then(branch)
                        .repeated()
                        .collect::<Vec<_>>(),
                )
                .then(
                    just(Token::Keyword(Keyword::Else))
                        .map_with(|_, e| e.span())
                        .then(stmts.clone().delimited_by(
                            just(Token::Sym(Sym::LBrace)),
                            just(Token::Sym(Sym::RBrace)),
                        ))
                        .or_not(),
                )
                .map(|((then, elif), els)| Stmt::If {
                    then,
                    elif: elif.into_boxed_slice(),
                    els: els.map(|(span, stmts)| (span, stmts.into_boxed_slice())),
                })
                .map_with(Spanned::from_map_extra)
                .labelled("if statement");

        let while_ = just(Token::Keyword(Keyword::While))
            .map_with(|_, e| e.span())
            .then(expr())
            .then(stmts.delimited_by(just(Token::Sym(Sym::LBrace)), just(Token::Sym(Sym::RBrace))))
            .map(|((span, cond), body)| {
                Stmt::While(Branch {
                    span,
                    cond,
                    body: body.into_boxed_slice(),
                })
            })
            .map_with(Spanned::from_map_extra)
            .labelled("while statement");

        func.or(if_)
            .or(while_)
            .or(assign)
            .or(update)
            .or(return_)
            .or(expr_)
            .labelled("statement")
    })
}
