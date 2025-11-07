use chumsky::Parser;
use std::mem::transmute;
use std::path::Path;

use crate::State;
use crate::syntax::Expr;
use crate::syntax::parse::Token;
use crate::syntax::parse::expr::expr;
use crate::syntax::parse::file::file;
use crate::syntax::parse::lex::lex;

fn eval_nth(text: &str, n: usize, arg: Expr) -> Expr {
    State::parse(text)
        .unwrap()
        .resolve()
        .unwrap()
        .check()
        .unwrap()
        .eval_nth(n, arg)
}

fn eval(text: &str) -> Expr {
    State::parse(text)
        .unwrap()
        .resolve()
        .unwrap()
        .check()
        .unwrap()
        .eval()
        .unwrap()
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
fn it_parses_file() {
    let out = lex()
        .parse(
            r#"
/// Hey.
function f(a) {
    let b = 42 // hi

    if (a) {
        return false
    } else if (b) {
        return true
    } else {
        return false
    }

    return true
}
"#,
        )
        .unwrap();
    file().parse(out.tokens.as_slice()).unwrap();
}

#[test]
fn it_runs_fibonacci() {
    let a = eval_nth(include_str!("fibonacci.rows"), 0, Expr::Number(10.));
    assert!(matches!(a, Expr::Number(89.)));
}

#[test]
fn it_runs_factorial() {
    let a = eval_nth(include_str!("factorial.rows"), 0, Expr::Number(10.));
    assert!(matches!(a, Expr::Number(3628800.)));
}

#[test]
fn it_runs_factorial_main() {
    eval(include_str!("factorial.rows"));
}

fn run_compiled<T, R>(path: &Path, text: &str, input: T) -> R {
    let (_, ptr) = State::parse(text)
        .unwrap()
        .resolve()
        .unwrap()
        .check()
        .unwrap()
        .compile(path)
        .unwrap()
        .into_iter()
        .filter(|(id, ..)| id.raw() != "main")
        .next()
        .unwrap();
    unsafe { transmute::<_, fn(T) -> R>(ptr)(input) }
}

#[test]
fn it_runs_compiled() {
    let v = run_compiled::<f64, f64>(
        Path::new("<stdin>"),
        "function f(a: u32): u32 { return a + 1 }",
        0.,
    );
    assert_eq!(v, 1.);
}

#[test]
fn it_runs_compiled_fibonacci() {
    let v = run_compiled::<f64, f64>(
        Path::new("tests").join("fibonacci.rows").as_path(),
        include_str!("fibonacci.rows"),
        10.,
    );
    assert_eq!(v, 89.);
}

#[test]
fn it_runs_compiled_factorial() {
    let v = run_compiled::<f64, f64>(
        Path::new("tests").join("factorial.rows").as_path(),
        include_str!("factorial.rows"),
        10.,
    );
    assert_eq!(v, 3628800.);
}

#[allow(dead_code)]
fn run_compiled_main(path: &Path, text: &str) {
    let state = State::parse(text)
        .unwrap()
        .resolve()
        .unwrap()
        .check()
        .unwrap();
    let main = state.file.main.as_ref().cloned().unwrap();
    let ptr = *state.compile(path).unwrap().get(&main).unwrap();
    unsafe { transmute::<_, fn() -> u8>(ptr)() };
}

#[test]
fn it_runs_compiled_factorial_main() {
    run_compiled_main(
        Path::new("tests").join("factorial.rows").as_path(),
        include_str!("factorial.rows"),
    );
}
