use chumsky::Parser;
use chumsky::input::ValueInput;
use chumsky::pratt::{infix, left, prefix};
use chumsky::prelude::{just, recursive};
use chumsky::primitive::select;
use serde_json::from_str;
use ustr::Ustr;

use crate::semantics::{Float, Integer};
use crate::syntax::parse::{Keyword, Sym, SyntaxErr, Token, grouped_by, id, name};
use crate::syntax::{Access, Expr, Id, Ident, Object};
use crate::{Span, Spanned};

enum Chainer {
    Args(Vec<Spanned<Expr>>),
    Object(Vec<(Spanned<Ustr>, Spanned<Expr>)>),
    Access(Spanned<Ustr>),
    Method(Spanned<Id>, Vec<Spanned<Expr>>),
    TypeArgs(Vec<Spanned<Expr>>),
}

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
        Token::Ident(n) => Some(Expr::Ident(Ident::Id(Id::bound(n)))),
        _ => None,
    })
    .map_with(Spanned::from_map_extra)
    .labelled("identifier expression");

    recursive(|expr| {
        let paren = expr
            .clone()
            .delimited_by(just(Token::Sym(Sym::LParen)), just(Token::Sym(Sym::RParen)))
            .labelled("parenthesized expression");

        let args =
            grouped_by(Sym::LParen, expr.clone(), Sym::Comma, Sym::RParen).labelled("arguments");
        let arguments = args
            .clone()
            .map(Chainer::Args)
            .labelled("arguments expression");
        let obj = grouped_by(
            Sym::LBrace,
            name()
                .then_ignore(just(Token::Sym(Sym::Colon)))
                .then(expr.clone()),
            Sym::Comma,
            Sym::RBrace,
        )
        .map(Chainer::Object)
        .labelled("object expression");
        let method = just(Token::Sym(Sym::Dot))
            .ignore_then(id())
            .then(args)
            .map(|(id, args)| Chainer::Method(id, args))
            .labelled("method expression");
        let access = just(Token::Sym(Sym::Dot))
            .ignore_then(name())
            .map(Chainer::Access)
            .labelled("access expression");
        let type_args = grouped_by(Sym::Lt, expr, Sym::Comma, Sym::Gt)
            .map(Chainer::TypeArgs)
            .labelled("type arguments");
        let chainer = arguments.or(obj).or(method).or(access).or(type_args);

        let call = just(Token::Keyword(Keyword::New))
            .or_not()
            .then(constant.or(ident).or(paren))
            .map_with(|(new, callee), e| match new {
                None => callee,
                Some(..) => Spanned {
                    span: e.span(),
                    item: Expr::New(Box::new(callee)),
                },
            })
            .foldl_with(chainer.repeated(), |a, c, e| Spanned {
                span: e.span(),
                item: match c {
                    Chainer::Args(args) => Expr::Call(Box::new(a), args),
                    Chainer::Object(xs) => Expr::Object(Box::new(a), Object::Unordered(xs)),
                    Chainer::Access(m) => Expr::Access(Box::new(a), Access::Named(m)),
                    Chainer::Method(m, args) => Expr::Method {
                        callee: Box::new(a),
                        target: None,
                        method: m.map(Ident::Id),
                        args,
                    },
                    Chainer::TypeArgs(args) => Expr::Apply(Box::new(a), args),
                },
            })
            .labelled("call expression");

        call.pratt((
            prefix(4, just(Token::Sym(Sym::And)), |_, a, e| {
                Spanned::from_map_extra(Expr::RefType(Box::new(a)), e)
            }),
            prefix(4, just(Token::Sym(Sym::Mul)), Expr::unary),
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
