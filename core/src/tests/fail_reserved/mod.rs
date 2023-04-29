use pest::error::LineColLocation;

use crate::tests::run_err;
use crate::Error;

#[test]
fn test_reserved() {
    match run_err(module_path!()) {
        Error::Parsing(e) => match e.line_col {
            LineColLocation::Pos((l, c)) => {
                assert_eq!(l, 1);
                assert_eq!(c, 10);
            }
            _ => assert!(false),
        },
        _ => assert!(false),
    }
}
