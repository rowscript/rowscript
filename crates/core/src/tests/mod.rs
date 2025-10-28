use std::mem::transmute;

use chumsky::Parser;

use crate::Ctx;
use crate::syntax::Expr;
use crate::syntax::parse::Token;
use crate::syntax::parse::expr::expr;
use crate::syntax::parse::lex::lex;
use crate::syntax::parse::stmt::stmt;

fn run(text: &str) -> Expr {
    Ctx::new(text)
        .parse()
        .unwrap()
        .resolve()
        .unwrap()
        .check()
        .unwrap()
        .eval()
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
function f(a) {
    let b = 42 // hi

    if a {
        return false
    } else if b {
        return true
    } else {
        return false
    }

    return true
}
"#,
        )
        .unwrap();
    stmt().parse(out.tokens.as_slice()).unwrap();
}

#[test]
fn it_runs_fibonacci() {
    let a = run(include_str!("fibonacci.rows"));
    assert!(matches!(a, Expr::Number(89.)));
}

#[test]
fn it_runs_factorial() {
    let a = run(include_str!("factorial.rows"));
    assert!(matches!(a, Expr::Number(3628800.)));
}

fn run_compiled<T, R>(text: &str, input: T) -> R {
    let ptr = Ctx::new(text)
        .parse()
        .unwrap()
        .resolve()
        .unwrap()
        .check()
        .unwrap()
        .compile()
        .unwrap()
        .into_values()
        .next()
        .unwrap();
    unsafe { transmute::<_, fn(T) -> R>(ptr)(input) }
}

#[test]
fn it_runs_compiled() {
    let v = run_compiled::<f64, f64>("function f(a: u32): u32 { return a + 1 }", 0.);
    assert_eq!(v, 1.);
}

#[test]
fn it_runs_compiled_fibonacci() {
    let v = run_compiled::<f64, f64>(include_str!("fibonacci.rows"), 10.);
    assert_eq!(v, 89.);
}

#[test]
fn it_runs_compiled_factorial() {
    let v = run_compiled::<f64, f64>(include_str!("factorial.rows"), 10.);
    assert_eq!(v, 3628800.);
}
