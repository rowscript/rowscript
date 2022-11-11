use crate::surf::parse_text;

#[test]
fn test_function() {
    let text = "
function foo(a: number): number {
  return a;
}

function bar() {
  return;
}

function baz(): () -> number {
  return () => 42;
}

function qux(): (s: number) -> string {
  let a: number = 42;
  return n => \"Hello, world!\";
}";
    parse_text(text).expect("parse error");
}
