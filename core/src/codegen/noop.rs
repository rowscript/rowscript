use std::path::Path;

use crate::codegen::Target;
use crate::theory::abs::def::Sigma;
use crate::theory::conc::load::ModuleID;
use crate::{Error, ModuleFile};

#[derive(Default)]
pub struct Noop;

impl Target for Noop {
    fn filename(&self) -> &'static str {
        ""
    }

    fn to_qualifier(&self, _: &ModuleID) -> String {
        unreachable!()
    }

    fn should_include(&self, _: &Path) -> bool {
        false
    }

    fn module(
        &mut self,
        _: &mut Vec<u8>,
        _: &Sigma,
        _: &[Box<Path>],
        _: ModuleFile,
    ) -> Result<(), Error> {
        Ok(())
    }
}
