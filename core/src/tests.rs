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
        let b: number = (n => n)(69);
        return () => ()
    }
    ",
    )
}

#[test]
fn test_bool() {
    check(
        "
    function f() {
        let a: number = if (true) {
            let b = 42;
            b
        } else {
            let c: number = 69;
            c
        };
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
