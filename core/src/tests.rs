use crate::Driver;

#[test]
fn test_basic() {
    Driver::new("test")
        .check_text(
            "
        function foo<T>(a: number, b: string): boolean {
            return false
        }

        function bar<T, U>(a: number): (b: string) -> string {
            return b => \"hello\"
        }

        function baz(): () -> number {
            return () => 42
        }
        ",
        )
        .unwrap()
}
