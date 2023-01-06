use std::env;
use std::path::PathBuf;

use crate::{Driver, Error};

mod fail_parse;
mod fail_resolve;
mod ok_bool;
mod ok_enum;
mod ok_fn;
mod ok_fn_recur;
mod ok_hole;
mod ok_implicit_named;
mod ok_implicit_unnamed;
mod ok_object;
mod ok_object_rowpoly;
mod ok_postulate_fn;
mod ok_postulate_type;

fn check_helper(mod_path: &str) -> Result<(), Error> {
    let mut pkg = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    pkg.extend([
        "src",
        "tests",
        mod_path.to_string().split("::").last().unwrap(),
    ]);
    Driver::new(pkg).check()
}

pub fn check_ok(mod_path: &str) {
    check_helper(mod_path).unwrap()
}

pub fn check_err(mod_path: &str) -> Error {
    check_helper(mod_path).unwrap_err()
}
