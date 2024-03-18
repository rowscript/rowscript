use crate::tests::run_err;
use crate::Error;

#[test]
fn test_issue134() {
    match run_err(module_path!()) {
        Error::DuplicateName(loc) => {
            assert_eq!(loc.line, 1);
            assert_eq!(loc.col, 1);
        }
        _ => assert!(false),
    }
}
