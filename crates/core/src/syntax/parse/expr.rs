use chumsky::Parser;
use chumsky::input::ValueInput;
use chumsky::pratt::{infix, left, prefix};
use chumsky::prelude::{just, recursive};
use chumsky::primitive::select;
use serde_json::from_str;

use crate::semantics::{Float, Integer};
use crate::syntax::parse::{Sym, SyntaxErr, Token, grouped_by};
use crate::syntax::{Expr, Ident};
use crate::{Span, Spanned};

pub(crate) fn expr<'t, I>() -> impl Parser<'t, I, Spanned<Expr>, SyntaxErr<'t, Token>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    let constant = select(|x, _| {
        Some(match x {
            Token::Number(n) => {
                let s = n.as_str();
                from_str::<i64>(s)
                    .map(|n| Expr::Integer(Integer::I64(n)))
                    .unwrap_or_else(|_| Expr::Float(Float::F64(from_str(s).unwrap())))
            }
            Token::String(s) => Expr::String(s),
            Token::Boolean(b) => Expr::Boolean(b),
            Token::BuiltinType(t) => Expr::BuiltinType(t),
            _ => return None,
        })
    })
    .map_with(Spanned::from_map_extra)
    .labelled("constant expression");

    let ident = select(|x, _| match x {
        Token::Ident(n) => Some(Expr::Ident(Ident::Id(n))),
        _ => None,
    })
    .map_with(Spanned::from_map_extra)
    .labelled("identifier expression");

    recursive(|expr| {
        let paren = expr
            .clone()
            .delimited_by(just(Token::Sym(Sym::LParen)), just(Token::Sym(Sym::RParen)))
            .labelled("parenthesized expression");

        let args = grouped_by(Sym::LParen, expr, Sym::Comma, Sym::RParen).labelled("arguments");
        let call = constant
            .or(ident)
            .or(paren)
            .foldl_with(args.repeated(), |callee, args, e| Spanned {
                span: e.span(),
                item: Expr::Call(Box::new(callee), args.into_boxed_slice()),
            })
            .labelled("call expression");

        call.pratt((
            prefix(4, just(Token::Sym(Sym::And)), |_, a, e| {
                Spanned::from_map_extra(Expr::RefType(Box::new(a)), e)
            }),
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
