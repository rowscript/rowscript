use crate::tests::run_err;
use crate::theory::Loc;
use crate::Error;

#[test]
fn test_resolve() {
    match run_err(module_path!()) {
        Error::UnresolvedVar(Loc { line, col, .. }) => {
            assert_eq!(line, 3);
            assert_eq!(col, 5);
        }
        _ => assert!(false),
    }
}
