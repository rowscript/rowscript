use crate::surf::Surf;

#[test]
fn it_parses_empty_function() {
    Surf::new("function foo(){}".into()).unwrap();
}

#[test]
fn it_parses_annotated_function() {
    Surf::new("function foo(n: int): int { return 42 }".into()).unwrap();
}

#[test]
fn it_cannot_parse_no_return_function() {
    Surf::new("function foo(): int { return 42; }".into()).unwrap_err();
}

#[test]
fn it_parses_class_declaration() {
    Surf::new(
        "
class Derived<A> extends Base<B> {
  constructor() {
  }

  doSomething() {
  }
}
    "
        .into(),
    )
    .unwrap();
}

#[test]
fn it_converts_unary_expressions() {
    [
        "function foo(n: number): number { return +42 }",
        "function foo(n: number): number { return -42 }",
        "function foo(n: number): number { return !42 }",
        "function foo(n: number): number { return ~42 }",
    ]
    .map(|i| println!("{}", Surf::new(i.into()).unwrap().to_presyntax()));
}

#[test]
fn it_converts_call_expressions() {
    [
        "function f() { return g() }",
        "function f() { return g(1) }",
        "function f() { return g(1,2) }",
    ]
    .map(|i| println!("{}", Surf::new(i.into()).unwrap().to_presyntax()));
}

#[test]
fn it_converts_pipeline_expressions() {
    [
        "function _() { return a:foo() }",
        "function _() { return a:foo:bar() }",
        "function _() { return a:foo:bar:baz() }",
        "function _() { return a:foo:bar:baz(1) }",
        "function _() { return a:foo:bar:baz(1, 2) }",
    ]
    .map(|i| println!("{}", Surf::new(i.into()).unwrap().to_presyntax()));
}
