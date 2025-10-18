use chumsky::input::ValueInput;
use chumsky::pratt::{infix, left};
use chumsky::prelude::{just, recursive};
use chumsky::{Parser, select};
use serde_json::from_str;

use crate::syntax::parse::{Sym, SyntaxErr, Token, grouped_by};
use crate::syntax::{Expr, Ident};
use crate::{Span, Spanned};

pub(crate) fn expr<'t, I>() -> impl Parser<'t, I, Spanned<Expr>, SyntaxErr<'t, Token>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    let constant = select! {
        Token::Number(n) => Expr::Number(
            from_str(n.as_str()).unwrap()),
        Token::String(s) => Expr::String(s),
        Token::Boolean(b) => Expr::Boolean(b),
        Token::BuiltinType(t) => Expr::BuiltinType(t)
    }
    .map_with(Spanned::from_map_extra)
    .labelled("constant expression");

    let ident_ = select! {
        Token::Ident(n) => Expr::Ident(Ident::Id(n))
    }
    .map_with(Spanned::from_map_extra)
    .labelled("identifier expression");

    recursive(|expr| {
        let paren = expr
            .clone()
            .delimited_by(just(Token::Sym(Sym::LParen)), just(Token::Sym(Sym::RParen)))
            .labelled("parenthesized expression");

        let args = grouped_by(Sym::LParen, expr, Sym::Comma, Sym::RParen).labelled("arguments");
        let call = constant
            .or(ident_)
            .or(paren)
            .foldl_with(args.repeated(), |callee, args, e| Spanned {
                span: e.span(),
                item: Expr::Call(Box::new(callee), args.into_boxed_slice()),
            })
            .labelled("call expression");

        call.pratt((
            infix(left(3), just(Token::Sym(Sym::Mul)), Expr::binary),
            infix(left(2), just(Token::Sym(Sym::Plus)), Expr::binary),
            infix(left(2), just(Token::Sym(Sym::Minus)), Expr::binary),
            infix(left(1), just(Token::Sym(Sym::Lt)), Expr::binary),
            infix(left(1), just(Token::Sym(Sym::Le)), Expr::binary),
            infix(left(1), just(Token::Sym(Sym::Gt)), Expr::binary),
            infix(left(1), just(Token::Sym(Sym::Ge)), Expr::binary),
            infix(left(1), just(Token::Sym(Sym::EqEq)), Expr::binary),
        ))
        .labelled("expression")
    })
}
