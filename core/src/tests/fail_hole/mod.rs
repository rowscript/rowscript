use crate::tests::run_err;
use crate::theory::Loc;
use crate::Error;

#[test]
fn test_hole() {
    match run_err(module_path!()) {
        Error::UnsolvedMeta(_, Loc { end, .. }) => {
            assert_eq!(end, 25);
        }
        _ => assert!(false),
    }
}
