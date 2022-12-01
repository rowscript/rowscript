use pest::error::LineColLocation;

use crate::tests::check_err;
use crate::Error;

#[test]
fn test_parse() {
    match check_err(module_path!()) {
        Error::Parsing(e) => match e.line_col {
            LineColLocation::Pos((l, c)) => {
                assert_eq!(l, 1);
                assert_eq!(c, 15);
            }
            _ => assert!(false),
        },
        _ => assert!(false),
    }
}
