use crate::Error;
use crate::tests::run_err;

#[test]
fn test_issue155() {
    match run_err(module_path!()) {
        Error::NonAnonVariadicDef(loc) => {
            assert_eq!(loc.line, 2);
            assert_eq!(loc.col, 18);
        }
        _ => unreachable!(),
    }
}
