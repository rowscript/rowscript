use std::fs::write;
use std::path::PathBuf;

use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Def, Sigma};
use crate::Error;

#[cfg(feature = "codegen-es6")]
pub mod es6;
pub mod noop;

pub trait Target {
    fn filename(&self) -> &'static str;
    fn def<'a>(&self, f: &mut String, sigma: &'a Sigma, def: &Def<Term>) -> Result<(), Error>;
}

pub struct Codegen<'a> {
    sigma: &'a Sigma,
    path: PathBuf,
    target: Box<dyn Target>,
}

impl<'a> Codegen<'a> {
    pub fn new(sigma: &'a Sigma, path: PathBuf, target: Box<dyn Target>) -> Self {
        Self {
            sigma,
            path,
            target,
        }
    }

    pub fn package(self) -> Result<(), Error> {
        let mut buf = String::default();
        for def in self.sigma {
            self.target.def(&mut buf, self.sigma, def.1)?;
        }
        if buf.is_empty() {
            return Ok(());
        }
        write(self.path.join(self.target.filename()), buf).map_err(Error::from)
    }
}
