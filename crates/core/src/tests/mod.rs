use chumsky::Parser;

use crate::semantics::checker::Checked;
use crate::syntax::parser::{Parsed, Token, expr, lex, stmt};
use crate::syntax::resolver::Resolved;

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
    let Token::Doc(doc) = &token_set.tokens[0] else {
        unreachable!();
    };
    assert_eq!(doc, " hi");
    let span = token_set.spans[0];
    assert_eq!(Some(span.start), TEXT.find("/// hi"));
}

#[test]
fn it_parses_expr() {
    let out = lex().parse("f(42, x) == false").unwrap();
    expr().parse(out.tokens.as_slice()).unwrap();
}

#[test]
fn it_parses_stmt() {
    let out = lex()
        .parse(
            r#"
/// Hey.
function f(a)
    b := 42 // hi

    if a
        return false
    else if b
        return true
    else
        return false
    end

    return true
end
"#,
        )
        .unwrap();
    stmt().parse(out.tokens.as_slice()).unwrap();
}

#[test]
fn it_works() {
    include_str!("basic.rows")
        .parsed()
        .unwrap()
        .resolved()
        .unwrap()
        .checked()
        .unwrap();
}
