use std::str::FromStr;

use chumsky::container::Container;
use chumsky::extra::Err as Full;
use chumsky::input::ValueInput;
use chumsky::pratt::{infix, left};
use chumsky::prelude::{
    IterParser, Rich, any, choice, end, just, none_of, one_of, recursive, skip_then_retry_until,
};
use chumsky::text::{digits, ident, int};
use chumsky::{Parser, select};
use serde_json::from_str;
use strum::{Display, EnumString};
use ustr::Ustr;

use crate::syntax::{Branch, BuiltinType, Expr, Name, Param, Sig, Stmt};
use crate::{Error, Out, Span, Spanned};

pub(crate) type SyntaxErr<'a, T> = Full<Rich<'a, T, Span>>;

pub(crate) trait Parsed {
    fn parsed(self) -> Out<Vec<Spanned<Stmt>>>;
}

impl Parsed for &str {
    fn parsed(self) -> Out<Vec<Spanned<Stmt>>> {
        lex()
            .parse(self)
            .into_result()
            .map_err(|errs| {
                Error::Lexing(
                    errs.into_iter()
                        .map(|e| (*e.span(), e.reason().to_string()))
                        .collect(),
                )
            })
            .and_then(|tokens| {
                file()
                    .parse(tokens.tokens.as_slice())
                    .into_result()
                    .map_err(|errs| {
                        Error::Parsing(
                            tokens.spans.into(),
                            errs.into_iter()
                                .map(|e| (*e.span(), e.reason().to_string()))
                                .collect(),
                        )
                    })
            })
    }
}

#[derive(Debug, Eq, PartialEq, Clone, EnumString, Display)]
#[strum(serialize_all = "lowercase")]
pub(crate) enum Keyword {
    Function,
    If,
    Else,
    Return,
}

#[derive(Debug, Eq, PartialEq, Clone, Display)]
pub(crate) enum Sym {
    // Long.
    Assign,
    EqEq,
    Le,
    Ge,

    // Short.
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
    Eq,
    Lt,
    Gt,
    Plus,
    Minus,
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
    Name(Name),
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
pub(crate) struct TokenSet {
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

/// Lexical analysis.
///
/// Number and string literal parsing extracted from
/// [the fast JSON example](https://github.com/zesterer/chumsky/blob/main/examples/json_fast.rs).
pub(crate) fn lex<'s>() -> impl Parser<'s, &'s str, TokenSet, SyntaxErr<'s, char>> {
    let dec = digits(10).to_slice();
    let frac = just('.').then(dec);
    let exp = just('e')
        .or(just('E'))
        .then(one_of("+-").or_not())
        .then(dec);
    let number = just('-')
        .or_not()
        .then(int(10))
        .then(frac.or_not())
        .then(exp.or_not())
        .to_slice()
        .map(|s: &str| Token::Number(s.into()));

    let escape = just('\\')
        .then(choice((
            just('\\'),
            just('/'),
            just('"'),
            just('b').to('\x08'),
            just('f').to('\x0C'),
            just('n').to('\n'),
            just('r').to('\r'),
            just('t').to('\t'),
            just('u').ignore_then(digits(16).exactly(4).to_slice().validate(
                |digits, m, emitter| {
                    char::from_u32(u32::from_str_radix(digits, 16).unwrap()).unwrap_or_else(|| {
                        emitter.emit(Rich::custom(m.span(), digits));
                        '\u{FFFD}' // unicode replacement character
                    })
                },
            )),
        )))
        .ignored();
    let string = none_of("\\\"")
        .ignored()
        .or(escape)
        .repeated()
        .to_slice()
        .map(|s: &str| Token::String(s.into()))
        .delimited_by(just('"'), just('"'));

    let ident = ident().map(|text| {
        if let Ok(b) = bool::from_str(text) {
            Token::Boolean(b)
        } else if let Ok(t) = BuiltinType::from_str(text) {
            Token::BuiltinType(t)
        } else if let Ok(w) = Keyword::from_str(text) {
            Token::Keyword(w)
        } else {
            Token::Name(Name::bound(text.into()))
        }
    });

    let symbol = choice((
        just(":=").to(Sym::Assign),
        just("==").to(Sym::EqEq),
        just("<=").to(Sym::Le),
        just(">=").to(Sym::Ge),
        just('(').to(Sym::LParen),
        just(')').to(Sym::RParen),
        just('{').to(Sym::LBrace),
        just('}').to(Sym::RBrace),
        just(',').to(Sym::Comma),
        just('=').to(Sym::Eq),
        just('<').to(Sym::Lt),
        just('>').to(Sym::Gt),
        just('+').to(Sym::Plus),
        just('-').to(Sym::Minus),
    ))
    .map(Token::Sym);

    let doc = just("///")
        .ignore_then(any().and_is(just('\n').not()).repeated().to_slice())
        .map(|s: &str| Token::Doc(s.into()));

    let token = number.or(string).or(ident).or(symbol).or(doc);

    let line_comment = just("//")
        .then_ignore(any().and_is(just('/')).not())
        .then_ignore(any().and_is(just('\n').not()).repeated())
        .padded();
    let block_comment = just("/*")
        .then_ignore(any().and_is(just("*/").not()).repeated())
        .then_ignore(just("*/"))
        .padded();
    let comment = line_comment.or(block_comment);

    token
        .map_with(Spanned::from_map_extra)
        .padded_by(comment.repeated())
        .padded()
        .recover_with(skip_then_retry_until(any().ignored(), end()))
        .repeated()
        .collect()
}

pub(crate) fn expr<'t, I>() -> impl Parser<'t, I, Spanned<Expr>, SyntaxErr<'t, Token>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    let constant = select! {
        Token::Number(n) => Expr::Number(from_str(n.as_str()).unwrap()),
        Token::String(s) => Expr::String(s),
        Token::Boolean(b) => Expr::Boolean(b),
        Token::BuiltinType(t) => Expr::BuiltinType(t)
    }
    .map_with(Spanned::from_map_extra)
    .labelled("constant expression");

    let name = select! {
        Token::Name(n) => Expr::Name(n)
    }
    .map_with(Spanned::from_map_extra)
    .labelled("name expression");

    recursive(|expr| {
        let paren = expr
            .clone()
            .delimited_by(just(Token::Sym(Sym::LParen)), just(Token::Sym(Sym::RParen)))
            .labelled("parenthesized expression");

        let args = grouped_by(Sym::LParen, expr, Sym::Comma, Sym::RParen).labelled("arguments");
        let call = constant
            .or(name)
            .or(paren)
            .foldl_with(args.repeated(), |callee, args, e| Spanned {
                span: e.span(),
                item: Expr::Call(Box::new(callee), args.into_boxed_slice()),
            })
            .labelled("call expression");

        call.pratt((
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

    let name = select! {
        Token::Name(n) => n
    }
    .map_with(Spanned::from_map_extra)
    .labelled("name");

    let param = name
        .then(expr().or_not())
        .map(|(Spanned { span, item: name }, typ)| Spanned {
            span,
            item: Param { name, typ },
        })
        .labelled("parameter");

    let params = grouped_by(Sym::LParen, param, Sym::Comma, Sym::RParen).labelled("parameters");

    let assign = doc
        .then(name)
        .then(expr().or_not())
        .then_ignore(just(Token::Sym(Sym::Assign)))
        .then(expr())
        .map(
            |(((doc, Spanned { span, item: name }), typ), rhs)| Spanned {
                span,
                item: Stmt::Assign {
                    doc: doc.into_boxed_slice(),
                    name,
                    typ,
                    rhs,
                },
            },
        )
        .labelled("assignment statement");

    let return_ = just(Token::Keyword(Keyword::Return))
        .ignore_then(expr().or_not())
        .map(Stmt::Return)
        .map_with(Spanned::from_map_extra)
        .labelled("return statement");

    let expr_ = expr()
        .map(|Spanned { span, item }| Spanned {
            span,
            item: Stmt::Expr(item),
        })
        .labelled("expression statement");

    recursive(|stmt| {
        let stmts = stmt.repeated().collect::<Vec<_>>().labelled("statements");

        let short = doc
            .then(name)
            .then(params.clone())
            .then(expr().or_not())
            .then_ignore(just(Token::Sym(Sym::Assign)))
            .then(expr())
            .map(
                |((((doc, Spanned { span, item: name }), params), ret), body)| Spanned {
                    span,
                    item: Stmt::Func {
                        short: true,
                        sig: Sig {
                            doc: doc.into_boxed_slice(),
                            name,
                            params: params.into_boxed_slice(),
                            ret,
                        },
                        body: Box::new([Spanned {
                            span: body.span,
                            item: Stmt::Expr(body.item),
                        }]),
                    },
                },
            )
            .labelled("short function statement");

        let func = doc
            .then_ignore(just(Token::Keyword(Keyword::Function)))
            .then(name)
            .then(params)
            .then(expr().or_not())
            .then(
                stmts
                    .clone()
                    .delimited_by(just(Token::Sym(Sym::LBrace)), just(Token::Sym(Sym::RBrace))),
            )
            .map(
                |((((doc, Spanned { span, item: name }), params), ret), body)| Spanned {
                    span,
                    item: Stmt::Func {
                        short: false,
                        sig: Sig {
                            doc: doc.into_boxed_slice(),
                            name,
                            params: params.into_boxed_slice(),
                            ret,
                        },
                        body: body.into_boxed_slice(),
                    },
                },
            )
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
                        .then(stmts.delimited_by(
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

        func.or(if_)
            .or(short)
            .or(assign)
            .or(return_)
            .or(expr_)
            .labelled("statement")
    })
}

pub(crate) fn file<'t, I>() -> impl Parser<'t, I, Vec<Spanned<Stmt>>, SyntaxErr<'t, Token>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    stmt().repeated().collect().labelled("file")
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
