use chumsky::Parser;

use crate::syntax::parser::scan;

const BASIC: &str = include_str!("basic.rows");

#[test]
fn it_scans() {
    scan().parse(BASIC).unwrap();
}
