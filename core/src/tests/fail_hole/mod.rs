use crate::Error;
use crate::tests::run_err;
use crate::theory::Loc;

#[test]
fn test_hole() {
    match run_err(module_path!()) {
        Error::UnsolvedMeta(_, Loc { end, .. }) => {
            assert_eq!(end, 18);
        }
        _ => assert!(false),
    }
}
