use std::fs::write;
use std::path::PathBuf;

use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Def, Sigma};
use crate::Error;

#[cfg(feature = "codegen-ecma")]
pub mod ecma;
pub mod noop;

pub trait Target {
    fn filename(&self) -> &'static str;
    fn defs(&self, buf: &mut Vec<u8>, sigma: &Sigma, defs: Vec<Def<Term>>) -> Result<(), Error>;
}

pub struct Codegen<'a> {
    sigma: &'a Sigma,
    defs: Vec<Def<Term>>,
    path: PathBuf,
    target: Box<dyn Target>,
}

impl<'a> Codegen<'a> {
    pub fn new(
        sigma: &'a Sigma,
        defs: Vec<Def<Term>>,
        path: PathBuf,
        target: Box<dyn Target>,
    ) -> Self {
        Self {
            sigma,
            defs,
            path,
            target,
        }
    }

    pub fn package(self) -> Result<(), Error> {
        let mut buf = Vec::default();
        self.target.defs(&mut buf, self.sigma, self.defs)?;
        if !buf.is_empty() {
            write(self.path.join(self.target.filename()), buf)?;
        }
        Ok(())
    }
}
