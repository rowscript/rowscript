use std::fs::{copy, create_dir_all, read_to_string, write};
use std::path::{Path, PathBuf};

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
    fn file(
        &mut self,
        buf: &mut Vec<u8>,
        sigma: &Sigma,
        includes: &[Box<Path>],
        file: File<Term>,
    ) -> Result<(), Error>;
}

pub struct Codegen {
    target: Box<dyn Target>,
    pub outdir: PathBuf,
}

impl Codegen {
    pub fn new(target: Box<dyn Target>, outdir: PathBuf) -> Self {
        Self { target, outdir }
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
            let p = f.path.clone();
            let file = p.as_ref();
            if let Err(e) = self.target.file(&mut buf, sigma, &includes, f) {
                return Err(print_err(
                    e,
                    file,
                    read_to_string(file).map_err(|e| Error::IO(file.into(), e))?,
                ));
            }
        }

        if buf.is_empty() {
            return Ok(());
        }

        let module_dir = module.to_source_path(&self.outdir);
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
