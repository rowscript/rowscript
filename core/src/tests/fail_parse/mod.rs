use pest::error::LineColLocation;

use crate::Error;
use crate::tests::run_err;

#[test]
fn test_parse() {
    match run_err(module_path!()) {
        Error::Parsing(e) => match e.line_col {
            LineColLocation::Pos((l, c)) => {
                assert_eq!(l, 2);
                assert_eq!(c, 1);
            }
            _ => assert!(false),
        },
        _ => assert!(false),
    }
}
