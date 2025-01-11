use std::fs::{copy, create_dir_all, write};
use std::path::Path;

use crate::theory::abs::data::Term;
use crate::theory::abs::def::Sigma;
use crate::theory::conc::load::ModuleID;
use crate::{print_err, Error, File, Module, Src, OUT_DIR};

pub mod ecma;
pub mod noop;

pub trait Target: Default {
    fn filename(&self) -> &'static str;
    fn to_qualifier(&self, module: &ModuleID) -> Src;
    fn should_include(&self, path: &Path) -> bool;
    fn module(
        &mut self,
        buf: &mut Vec<u8>,
        sigma: &Sigma,
        includes: &[Box<Path>],
        file: File<Term>,
        is_first_file: bool,
    ) -> Result<(), Error>;
}

#[derive(Clone)]
pub struct Codegen<T: Target> {
    target: T,
    pub out_dir: Box<Path>,
}

impl<T: Target> Codegen<T> {
    pub fn new(src_dir: &Path) -> Self {
        let target = T::default();
        let out_dir = src_dir.join(OUT_DIR).into_boxed_path();
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
        files
            .into_vec()
            .into_iter()
            .enumerate()
            .try_fold((), |_, (i, f)| {
                let file = f.path.clone();
                let src = f.src;
                self.target
                    .module(&mut buf, sigma, &includes, f, i == 0)
                    .map_err(|e| print_err(e, &file, src))
            })?;
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
