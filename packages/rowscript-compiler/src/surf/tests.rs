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
