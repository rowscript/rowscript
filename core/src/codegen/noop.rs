use std::path::{Path, PathBuf};

use crate::codegen::Target;
use crate::theory::abs::def::Sigma;
use crate::{Error, ModuleFile};

#[derive(Default)]
pub struct Noop;

impl Target for Noop {
    fn filename(&self) -> &'static str {
        ""
    }

    fn should_include(&self, _: &Path) -> bool {
        false
    }

    fn module(
        &mut self,
        _: &mut Vec<u8>,
        _: &Sigma,
        _: &[PathBuf],
        _: ModuleFile,
    ) -> Result<(), Error> {
        Ok(())
    }
}
