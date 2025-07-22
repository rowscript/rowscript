use chumsky::Parser;
use chumsky::extra::Err as Error;
use chumsky::prelude::{
    IterParser, Rich, SimpleSpan, any, choice, end, just, none_of, one_of, skip_then_retry_until,
};
use chumsky::text::{digits, ident, int};
use ustr::Ustr;

type Span = SimpleSpan;
type Spanned<T> = (T, Span);

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

#[derive(Debug)]
pub(crate) enum Token {
    // Contentful.
    Number(Ustr),
    String(Ustr),
    Boolean(bool),
    Ident(Ustr),
    Ctrl(char),
    Doc(Ustr),

    // Symbols.
    /// `:=`.
    Assign,
    /// `==`.
    Eq,

    // Types.
    Unit,
    Bool,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Str,

    // Control.
    Do,
    End,
    If,
    Then,
    Else,
    Return,
}

/// Scan a token.
///
/// Number and string literal parsing extracted from
/// [the fast JSON example](https://github.com/zesterer/chumsky/blob/main/examples/json_fast.rs).
pub(crate) fn scan<'s>()
-> impl Parser<'s, &'s str, Vec<Spanned<Token>>, Error<Rich<'s, char, Span>>> {
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

        "unit" => Token::Unit,
        "bool" => Token::Bool,
        "i8" => Token::I8,
        "i16" => Token::I16,
        "i32" => Token::I32,
        "i64" => Token::I64,
        "u8" => Token::U8,
        "u16" => Token::U16,
        "u32" => Token::U32,
        "u64" => Token::U64,
        "f32" => Token::F32,
        "f64" => Token::F64,
        "str" => Token::Str,

        "do" => Token::Do,
        "end" => Token::End,
        "if" => Token::If,
        "then" => Token::Else,
        "else" => Token::Else,
        "return" => Token::Return,

        _ => Token::Ident(text.into()),
    });

    let ctrl = one_of("(),").map(Token::Ctrl);

    let doc = just("///")
        .ignore_then(any().and_is(just('\n').not()).repeated())
        .to_slice()
        .map(|s: &str| Token::Doc(s.into()));

    let ops = choice((
        just(":=").map(|_| Token::Assign),
        just("==").map(|_| Token::Eq),
    ));

    let token = number.or(string).or(ident).or(ctrl).or(doc).or(ops);

    let line_comment = just("//")
        .then(any().and_is(just('\n').not()).repeated())
        .padded();
    let block_comment = just("/*")
        .then(any().and_is(just("*/").not()).repeated())
        .then_ignore(just("*/"))
        .padded();
    let comment = line_comment.or(block_comment);

    token
        .map_with(|tok, e| (tok, e.span()))
        .padded_by(comment.repeated())
        .padded()
        .recover_with(skip_then_retry_until(any().ignored(), end()))
        .repeated()
        .collect()
}
