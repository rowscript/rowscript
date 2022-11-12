use crate::Driver;

#[test]
fn test_basic() {
    Driver::new("test")
        .parse_text("function foo(){return;}")
        .unwrap()
}
