use crate::Error;
use crate::tests::run_err;

#[test]
fn test_issue114() {
    match run_err(module_path!()) {
        Error::UnresolvedVar(loc) => {
            assert_eq!(loc.line, 1);
            assert_eq!(loc.col, 6);
        }
        _ => unreachable!(),
    }
}
