use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Def, Sigma};
use crate::{print_err, Error};
use std::collections::HashMap;
use std::fs::write;
use std::path::PathBuf;

#[cfg(feature = "codegen-ecma")]
pub mod ecma;
pub mod noop;

pub trait Target {
    fn filename(&self) -> &'static str;
    fn module(&self, buf: &mut Vec<u8>, sigma: &Sigma, defs: Vec<Def<Term>>) -> Result<(), Error>;
}

pub type Vtbl = HashMap<String, Vec<Def<Term>>>;

pub struct Codegen {
    target: Box<dyn Target>,
    vtbl: Vtbl,
    buf: Vec<u8>,
    pub outfile: PathBuf,
}

impl Codegen {
    pub fn new(target: Box<dyn Target>, outdir: &PathBuf) -> Self {
        let outfile = outdir.join(target.filename());
        Self {
            target,
            vtbl: Default::default(),
            buf: Default::default(),
            outfile,
        }
    }

    pub fn module(
        &mut self,
        sigma: &Sigma,
        files: Vec<(String, String, Vec<Def<Term>>)>,
    ) -> Result<(), Error> {
        for (path, src, defs) in files {
            self.target
                .module(&mut self.buf, sigma, defs)
                .map_err(|e| print_err(e, &path, &src))?;
        }
        if !self.buf.is_empty() {
            write(&self.outfile, &self.buf)?
        }
        Ok(())
    }
}
