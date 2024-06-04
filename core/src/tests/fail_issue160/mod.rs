use crate::tests::run_err;
use crate::Error;
use pest::error::LineColLocation;

#[test]
fn test_issue160() {
    match run_err(module_path!()) {
        Error::Parsing(e) => match e.line_col {
            LineColLocation::Pos((l, c)) => {
                assert_eq!(l, 3);
                assert_eq!(c, 9);
            }
            _ => assert!(false),
        },
        _ => assert!(false),
    }
}
