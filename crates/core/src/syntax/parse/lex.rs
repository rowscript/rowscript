use std::str::FromStr;

use chumsky::Parser;
use chumsky::error::Rich;
use chumsky::prelude::{
    IterParser, any, choice, end, just, none_of, one_of, skip_then_retry_until,
};
use chumsky::text::{digits, ident, int};

use crate::Spanned;
use crate::semantics::BuiltinType;
use crate::syntax::Id;
use crate::syntax::parse::{Keyword, Sym, SyntaxErr, Token, TokenSet};

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
            Token::Ident(Id::bound(text.into()))
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
        just(':').to(Sym::Colon),
        just('=').to(Sym::Eq),
        just('<').to(Sym::Lt),
        just('>').to(Sym::Gt),
        just('+').to(Sym::Plus),
        just('-').to(Sym::Minus),
        just('*').to(Sym::Mul),
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
