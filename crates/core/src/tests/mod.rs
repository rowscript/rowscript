use std::mem::transmute;
use std::path::Path;

use chumsky::Parser;

use crate::semantics::Integer;
use crate::syntax::Expr;
use crate::syntax::parse::Token;
use crate::syntax::parse::expr::expr;
use crate::syntax::parse::file::file;
use crate::syntax::parse::lex::lex;
use crate::{Error, LineCol, State};

fn eval_nth(text: &str, n: usize, arg: Expr) -> Expr {
    let mut s = State::default();
    s.parse(text).unwrap();
    s.resolve().unwrap();
    s.check().unwrap();
    s.eval_nth(n, arg)
}

fn eval(text: &str) {
    let mut s = State::default();
    s.parse(text).unwrap();
    s.resolve().unwrap();
    s.check().unwrap();
    s.eval().unwrap();
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
    const TESTS: &[(&str, fn(Expr) -> bool)] = &[
        ("f(42, x) == false", |e| matches!(e, Expr::BinaryOp(..))),
        ("&i32", |e| matches!(e, Expr::RefType(..))),
        ("new i32(42)", |e| matches!(e, Expr::Call(..))),
        ("a()", |e| matches!(e, Expr::Call(..))),
        ("a()()", |e| matches!(e, Expr::Call(..))),
        ("a.b", |e| matches!(e, Expr::Access(..))),
        ("a.b()", |e| matches!(e, Expr::Method(..))),
        ("a.b()()", |e| matches!(e, Expr::Call(..))),
        ("a.b()().c.d()()()", |e| matches!(e, Expr::Call(..))),
    ];
    for (text, test) in TESTS {
        let out = lex().parse(text).unwrap();
        let e = expr().parse(out.tokens.as_slice()).unwrap();
        assert!(test(e.item));
    }
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
fn it_fails_resolving_file_duplicate() {
    let mut s = State::default();
    s.parse(
        r#"
function f() {}
function f() {}
"#,
    )
    .unwrap();
    let e = s.resolve().unwrap_err();
    let Error::DuplicateName(.., n) = e else {
        unreachable!();
    };
    assert_eq!(n, "f");
    let errs = s.explain(e);
    let LineCol { start, end } = errs[0].0.as_ref().unwrap();
    assert_eq!(start, &(2, 9));
    assert_eq!(end, &(2, 10));
}

#[test]
fn it_fails_checking_file() {
    const TEXT: &str = r#"
function f(): u32 {
    return "hi"
}
"#;
    let mut s = State::default();
    s.parse(TEXT).unwrap();
    s.resolve().unwrap();
    let e = s.check().unwrap_err();
    let Error::TypeMismatch { got, want, .. } = &e else {
        unreachable!();
    };
    assert_eq!(got, "str");
    assert_eq!(want, "u32");
    let errs = s.explain(e);
    let LineCol { start, end } = errs[0].0.as_ref().unwrap();
    assert_eq!(start, &(2, 11));
    assert_eq!(end, &(2, 15));
}

#[test]
fn it_checks_ref_type() {
    let mut s = State::default();
    s.parse(
        r#"
function f(): &u32 {
    return new u32(42)
}
"#,
    )
    .unwrap();
    s.resolve().unwrap();
    s.check().unwrap();
}

#[test]
fn it_runs_fibonacci() {
    let a = eval_nth(
        include_str!("fibonacci.rows"),
        0,
        Expr::Integer(Integer::U32(10)),
    );
    assert!(matches!(a, Expr::Integer(Integer::U32(89))));
}

#[test]
fn it_runs_factorial() {
    let a = eval_nth(
        include_str!("factorial.rows"),
        0,
        Expr::Integer(Integer::U32(10)),
    );
    assert!(matches!(a, Expr::Integer(Integer::U32(3628800))));
}

#[test]
fn it_runs_hello_main() {
    eval(include_str!("hello.rows"));
}

#[test]
fn it_runs_ref_main() {
    eval(include_str!("ref.rows"));
}

#[test]
fn it_runs_static_main() {
    eval(include_str!("static.rows"));
}

#[test]
fn it_runs_struct_main() {
    eval(include_str!("struct.rows"));
}

fn run_compiled<T, R>(path: &Path, text: &str, input: T) -> R {
    let mut s = State::default();
    s.parse(text).unwrap();
    s.resolve().unwrap();
    s.check().unwrap();
    let ptr = s.compile(path).unwrap().first_non_main().unwrap();
    unsafe { transmute::<_, fn(T) -> R>(ptr)(input) }
}

#[test]
fn it_runs_compiled() {
    let v = run_compiled::<u32, u32>(
        Path::new("<stdin>"),
        "function f(a: u32): u32 { return a + 1 }",
        0,
    );
    assert_eq!(v, 1);
}

#[test]
fn it_runs_compiled_fibonacci() {
    let v = run_compiled::<u32, u32>(
        Path::new("src")
            .join("tests")
            .join("fibonacci.rows")
            .as_path(),
        include_str!("fibonacci.rows"),
        10,
    );
    assert_eq!(v, 89);
}

#[test]
fn it_runs_compiled_factorial() {
    let v = run_compiled::<u32, u32>(
        Path::new("src")
            .join("tests")
            .join("factorial.rows")
            .as_path(),
        include_str!("factorial.rows"),
        10,
    );
    assert_eq!(v, 3628800);
}

fn run_compiled_main(path: &Path, text: &str) {
    let mut s = State::default();
    s.parse(text).unwrap();
    s.resolve().unwrap();
    s.check().unwrap();
    s.compile(path).unwrap().exec().unwrap();
}

#[test]
fn it_runs_compiled_factorial_main() {
    run_compiled_main(
        Path::new("src")
            .join("tests")
            .join("factorial.rows")
            .as_path(),
        include_str!("factorial.rows"),
    );
}

#[test]
fn it_runs_compiled_hello_main() {
    run_compiled_main(
        Path::new("src").join("tests").join("hello.rows").as_path(),
        include_str!("hello.rows"),
    );
}
