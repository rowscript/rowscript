use crate::parsing::build;

#[test]
fn it_works() {
    build("function foo(){}".to_string());
}
