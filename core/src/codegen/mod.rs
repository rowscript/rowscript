use std::fs::write;
use std::path::PathBuf;

use crate::theory::abs::data::Term;
use crate::theory::abs::def::Def;
use crate::Error;

#[cfg(feature = "codegen-es6")]
pub mod es6;
pub mod noop;

pub trait Target {
    fn filename(&self) -> &'static str;
    fn def(&self, def: Def<Term>, f: &mut String) -> Result<(), Error>;
}

pub struct Codegen {
    defs: Vec<Def<Term>>,
    path: PathBuf,
    target: Box<dyn Target>,
}

impl Codegen {
    pub fn new(defs: Vec<Def<Term>>, path: PathBuf, target: Box<dyn Target>) -> Self {
        Self { defs, path, target }
    }

    pub fn package(self) -> Result<(), Error> {
        let mut buf = String::default();
        for def in self.defs {
            self.target.def(def, &mut buf)?;
        }
        if buf.is_empty() {
            return Ok(());
        }
        write(self.path.join(self.target.filename()), buf).map_err(Error::from)
    }
}
