use chumsky::Parser;

use crate::syntax::Spanned;
use crate::syntax::parser::{Token, expr, lex};

const BASIC: &str = include_str!("basic.rows");

#[test]
fn it_scans() {
    lex().parse(BASIC).unwrap();
}

#[test]
fn it_scans_doc() {
    const TEXT: &str = r#"
// hey
/// hi
// and
/* hello */
"#;
    let tokens = lex().parse(TEXT).unwrap();
    assert_eq!(tokens.len(), 1);
    let Spanned {
        span,
        item: Token::Doc(doc),
    } = tokens[0]
    else {
        unreachable!();
    };
    assert_eq!(doc, " hi");
    assert_eq!(Some(span.start), TEXT.find("/// hi"));
}

#[test]
fn it_parses_expr() {
    let tokens = lex().parse("a := 42").unwrap();
    expr().parse(tokens.as_slice()).unwrap();
}
