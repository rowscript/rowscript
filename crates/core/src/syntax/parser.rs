use chumsky::container::Container;
use chumsky::extra::Err as FullError;
use chumsky::input::ValueInput;
use chumsky::prelude::{
    IterParser, Rich, any, choice, end, just, none_of, one_of, recursive, skip_then_retry_until,
};
use chumsky::text::{digits, ident, int};
use chumsky::{Parser, select};
use ustr::Ustr;

use crate::semantics::BuiltinType;
use crate::syntax::{Expr, Name, Param, Span, Spanned, Stmt};

type Error<'a, T> = FullError<Rich<'a, T, Span>>;

pub(crate) fn line_col(span: &Span, text: &str) -> (usize, usize) {
    let mut line = 1;
    let mut col = 1;
    for (i, c) in text.chars().enumerate() {
        if i == span.start {
            break;
        }
        if c == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

const ASSIGN: &str = ":=";

#[derive(Debug, Eq, PartialEq, Clone)]
pub(crate) enum Token {
    // Contentful.
    Number(Ustr),
    String(Ustr),
    Boolean(bool),
    Name(Name),
    Ctrl(char),
    Doc(Ustr),
    Op(Ustr),

    // Types.
    BuiltinType(BuiltinType),

    // Misc.
    Function,
    Do,
    End,
    If,
    Then,
    Else,
    Return,
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
pub(crate) fn lex<'s>() -> impl Parser<'s, &'s str, TokenSet, Error<'s, char>> {
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

    let ident = ident().map(|text| match text {
        "true" => Token::Boolean(true),
        "false" => Token::Boolean(false),

        "unit" => Token::BuiltinType(BuiltinType::Unit),
        "bool" => Token::BuiltinType(BuiltinType::Bool),
        "i8" => Token::BuiltinType(BuiltinType::I8),
        "i16" => Token::BuiltinType(BuiltinType::I16),
        "i32" => Token::BuiltinType(BuiltinType::I32),
        "i64" => Token::BuiltinType(BuiltinType::I64),
        "u8" => Token::BuiltinType(BuiltinType::U8),
        "u16" => Token::BuiltinType(BuiltinType::U16),
        "u32" => Token::BuiltinType(BuiltinType::U32),
        "u64" => Token::BuiltinType(BuiltinType::U64),
        "f32" => Token::BuiltinType(BuiltinType::F32),
        "f64" => Token::BuiltinType(BuiltinType::F64),
        "str" => Token::BuiltinType(BuiltinType::Str),

        "function" => Token::Function,
        "do" => Token::Do,
        "end" => Token::End,
        "if" => Token::If,
        "then" => Token::Else,
        "else" => Token::Else,
        "return" => Token::Return,

        _ => Token::Name(Name::bound(text.into())),
    });

    let ctrl = one_of("(),").map(Token::Ctrl);

    let doc = just("///")
        .ignore_then(any().and_is(just('\n').not()).repeated().to_slice())
        .map(|s: &str| Token::Doc(s.into()));

    let ops = choice((just(ASSIGN), just("=="))).map(|s| Token::Op(s.into()));

    let token = number.or(string).or(ident).or(ctrl).or(doc).or(ops);

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

pub(crate) fn expr<'t, I>() -> impl Parser<'t, I, Spanned<Expr>, Error<'t, Token>> + Clone
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    let trivial = select! {
        Token::Number(n) => Expr::Number(n),
        Token::String(s) => Expr::String(s),
        Token::Boolean(b) => Expr::Boolean(b),
        Token::BuiltinType(t) => Expr::BuiltinType(t)
    }
    .labelled("constant");

    let name = select! { Token::Name(n) => Expr::Name(n) }.labelled("name");

    trivial
        .or(name)
        .map_with(Spanned::from_map_extra)
        .labelled("expression")
}

pub(crate) fn stmt<'t, I>() -> impl Parser<'t, I, Spanned<Stmt>, Error<'t, Token>>
where
    I: ValueInput<'t, Token = Token, Span = Span>,
{
    recursive(|stmt| {
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

        let params = param
            .separated_by(just(Token::Ctrl(',')))
            .allow_trailing()
            .collect::<Vec<_>>()
            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')))
            .labelled("parameters");

        let stmts = stmt.repeated().collect::<Vec<_>>().labelled("statements");

        let func = just(Token::Function)
            .ignore_then(name)
            .then(params)
            .then(just(Token::Ctrl(':')).ignore_then(expr()).or_not())
            .then(stmts)
            .then_ignore(just(Token::End))
            .map(
                |(((Spanned { span, item: name }, params), ret), body)| Spanned {
                    span,
                    item: Stmt::Func {
                        doc: None,
                        name,
                        params: params.into_boxed_slice(),
                        ret,
                        body: body.into_boxed_slice(),
                    },
                },
            )
            .labelled("function");

        let assign_op = just(Token::Op(ASSIGN.into())).labelled(ASSIGN);
        let assign = name
            .then_ignore(assign_op)
            .then(expr())
            .map(|(Spanned { span, item: name }, rhs)| Spanned {
                span,
                item: Stmt::Assign(name, None, rhs),
            })
            .labelled("assignment");

        let return_ = just(Token::Return)
            .ignore_then(expr().or_not())
            .map(Stmt::Return)
            .map_with(Spanned::from_map_extra)
            .labelled("return");

        func.or(assign).or(return_).labelled("statement")
    })
}
