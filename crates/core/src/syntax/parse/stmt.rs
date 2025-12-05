use chumsky::Parser;
use chumsky::input::ValueInput;
use chumsky::prelude::{IterParser, just, recursive};

use crate::syntax::parse::expr::expr;
use crate::syntax::parse::{Keyword, Sym, SyntaxErr, Token, id};
use crate::syntax::{Branch, Ident, Stmt};
use crate::{Span, Spanned};

pub(crate) fn stmt<'t, I>() -> impl Parser<'t, I, Spanned<Stmt>, SyntaxErr<'t, Token>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    let assign = just(Token::Keyword(Keyword::Let))
        .ignore_then(id())
        .then(just(Token::Sym(Sym::Colon)).ignore_then(expr()).or_not())
        .then_ignore(just(Token::Sym(Sym::Eq)))
        .then(expr())
        .map(|((id, typ), rhs)| Stmt::Assign {
            name: id.map(Ident::Id),
            typ,
            rhs,
        })
        .map_with(Spanned::from_map_extra)
        .labelled("assignment statement");

    let update = id()
        .then_ignore(just(Token::Sym(Sym::Eq)))
        .then(expr())
        .map(|(id, rhs)| Stmt::Update {
            name: id.map(Ident::Id),
            rhs,
        })
        .map_with(Spanned::from_map_extra)
        .labelled("update statement");

    let r#return = just(Token::Keyword(Keyword::Return))
        .ignore_then(expr().or_not())
        .map(Stmt::Return)
        .map_with(Spanned::from_map_extra)
        .labelled("return statement");

    let exp = expr()
        .map(|e| e.map(Stmt::Expr))
        .labelled("expression statement");

    let cond = |kw: Keyword| {
        just(Token::Keyword(kw))
            .map_with(|_, e| e.span())
            .then(expr().delimited_by(just(Token::Sym(Sym::LParen)), just(Token::Sym(Sym::RParen))))
    };

    recursive(|stmt| {
        let stmts = stmt.repeated().collect::<Vec<_>>().labelled("statements");

        let branch = cond(Keyword::If)
            .then(
                stmts
                    .clone()
                    .delimited_by(just(Token::Sym(Sym::LBrace)), just(Token::Sym(Sym::RBrace))),
            )
            .map(|((span, cond), body)| Branch { span, cond, body })
            .labelled("if branch");

        let r#if =
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
                .map(|((then, elif), els)| Stmt::If { then, elif, els })
                .map_with(Spanned::from_map_extra)
                .labelled("if statement");

        let r#while = cond(Keyword::While)
            .then(
                stmts
                    .clone()
                    .delimited_by(just(Token::Sym(Sym::LBrace)), just(Token::Sym(Sym::RBrace))),
            )
            .map(|((span, cond), body)| Stmt::While(Branch { span, cond, body }))
            .map_with(Spanned::from_map_extra)
            .labelled("while statement");

        r#if.or(r#while)
            .or(assign)
            .or(update)
            .or(r#return)
            .or(exp)
            .labelled("statement")
    })
}
