use crate::parsing::parse;

#[test]
fn it_parses_empty_function() {
    parse("function foo(){}".into()).unwrap();
}

#[test]
fn it_parses_annotated_function() {
    parse("function foo(n: int): int { return 42 }".into()).unwrap();
}

#[test]
fn it_cannot_parse_no_return_function() {
    parse("function foo(): int { return 42; }".into()).unwrap_err();
}

#[test]
fn it_parses_class_declaration() {
    parse(
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
