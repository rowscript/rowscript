use crate::tests::run_err;
use crate::Error;

#[test]
fn test_resolve() {
    match run_err(module_path!()) {
        Error::UnresolvedVar(loc) => {
            assert_eq!(loc.line, 7);
            assert_eq!(loc.col, 9);
        }
        _ => assert!(false),
    }
}
