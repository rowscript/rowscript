use std::fs::{copy, create_dir_all, write};
use std::path::Path;

use crate::theory::abs::data::Term;
use crate::theory::abs::def::Sigma;
use crate::theory::conc::load::ModuleID;
use crate::{print_err, Error, File, Module};

pub mod ecma;
pub mod noop;

pub trait Target {
    fn filename(&self) -> &'static str;
    fn to_qualifier(&self, module: &ModuleID) -> String;
    fn should_include(&self, path: &Path) -> bool;
    fn module(
        &mut self,
        buf: &mut Vec<u8>,
        sigma: &Sigma,
        includes: &[Box<Path>],
        file: File<Term>,
    ) -> Result<(), Error>;
}

pub struct Codegen {
    target: Box<dyn Target>,
    pub out_dir: Box<Path>,
}

impl Codegen {
    pub fn new(target: Box<dyn Target>, out_dir: Box<Path>) -> Self {
        Self { target, out_dir }
    }

    pub fn should_include(&mut self, path: &Path) -> bool {
        self.target.should_include(path)
    }

    pub fn module(&mut self, sigma: &Sigma, module: Module<Term>) -> Result<(), Error> {
        let Module {
            module,
            files,
            includes,
            ..
        } = module;

        if !module.should_generate() {
            return Ok(());
        }

        let mut buf = Vec::default();

        for f in files {
            let file = f.path.clone();
            self.target
                .module(&mut buf, sigma, &includes, f)
                .map_err(|e| print_err(e, &file))?;
        }

        if buf.is_empty() {
            return Ok(());
        }

        let module_dir = module.to_source_path(&self.out_dir);
        let module_index_file = module_dir.join(self.target.filename()).into_boxed_path();
        create_dir_all(&module_dir).map_err(|e| Error::IO(module_dir.clone(), e))?;
        write(&module_index_file, &buf).map_err(|e| Error::IO(module_index_file, e))?;

        for file in includes {
            let to = module_dir.join(file.file_name().unwrap());
            copy(file, &to).map_err(|e| Error::IO(to.into_boxed_path(), e))?;
        }

        Ok(())
    }
}
