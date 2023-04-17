use std::ffi::OsStr;
use std::path::PathBuf;

use crate::codegen::Target;
use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Def, Sigma};
use crate::Error;

#[derive(Default)]
pub struct Noop;

impl Target for Noop {
    fn filename(&self) -> &'static str {
        ""
    }

    fn should_import(&self, _: &OsStr) -> bool {
        false
    }

    fn module(
        &mut self,
        _: &mut Vec<u8>,
        _: &Sigma,
        _: Vec<Def<Term>>,
        _: Vec<(&OsStr, PathBuf)>,
    ) -> Result<(), Error> {
        Ok(())
    }
}
