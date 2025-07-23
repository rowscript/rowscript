use chumsky::Parser;

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
    let token_set = lex().parse(TEXT).unwrap();
    assert_eq!(token_set.tokens.len(), 1);
    let Token::Doc(doc) = token_set.tokens[0] else {
        unreachable!();
    };
    assert_eq!(doc, " hi");
    let span = token_set.spans[0];
    assert_eq!(Some(span.start), TEXT.find("/// hi"));
}

#[test]
fn it_parses_expr() {
    let out = lex().parse("a := 42").unwrap();
    expr().parse(out.tokens.as_slice()).unwrap();
}
