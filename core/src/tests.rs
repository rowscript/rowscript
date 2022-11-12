use crate::Driver;

#[test]
fn test_basic() {
    Driver::new("test")
        .parse_text(
            "
        function foo<T>(a: number, b: string): boolean {
            return false;
        }

        function bar<T, U>(a: number): (b: string) -> boolean {
            return b => false;
        }

        function baz(): () -> boolean {
            return () => true;
        }
        ",
        )
        .unwrap()
}
