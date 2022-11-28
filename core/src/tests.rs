use crate::Driver;

fn check(text: &str) {
    let file = "test";
    if let Err(e) = Driver::new(file).check_text(text) {
        e.print(file, text);
        panic!("test failure : {:#?}", e)
    }
}

#[test]
fn test_fn() {
    check(
        "
    function f(): () -> unit {
        let id: (n: number) -> number = n => n;
        let a: number = id(42);
        return () => ()
    }

    function g<T>() {
        return f()()
    }
    ",
    )
}

#[test]
fn test_bool() {
    check(
        "
function f(): number {
    let a: number = if (true) {
        let b = 42;
        b
    } else {
        let c: number = 69;
        c
    };
    return a
}

function g<T>(): number {
    return f()
}
",
    )
}

#[test]
fn test_fn_postulate() {
    check(
        "
function f(a: number): number;
function g();
",
    )
}

#[test]
fn test_row() {
    check(
        "
function f<T, U>() { return }
function g<'A, 'B>() { return }
function h<'A, T>() { return }

function foo<'A, 'B>(a: {'A}, b: {'B}): number
    where (n: number) < ('A + 'B)
{
    // TODO: Extract field `n` from `a` or `b`.
    return 42
}

function foo<'A, 'B, 'C>(a: {'A}, b: {'B}): {'C}
    where 'C = 'A + 'B
      and (n: number) < 'C
{
    // TODO: Assign field `n` to the return type.
    return
}
",
    )
}

#[test]
#[should_panic]
fn test_parse_err() {
    check("function f() {}")
}

#[test]
#[should_panic]
fn test_resolve_err() {
    check(
        "
function f() {
    let a: number = if (true) {
        let b = 42;
        b
    } else {
        let c: number = 69;
        c1
    };
    return
}
",
    )
}
