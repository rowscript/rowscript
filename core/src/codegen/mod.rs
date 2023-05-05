use std::fs::{copy, create_dir_all, read_to_string, write};
use std::path::{Path, PathBuf};

use crate::theory::abs::data::Term;
use crate::theory::abs::def::Sigma;
use crate::theory::conc::load::ModuleID;
use crate::theory::Loc;
use crate::Error::NonErasable;
use crate::{print_err, Error, Module, ModuleFile};

#[cfg(feature = "codegen-ecma")]
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
        includes: &[PathBuf],
        file: ModuleFile,
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

    pub fn module(&mut self, sigma: &Sigma, module: Module) -> Result<(), Error> {
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
            let file = f.file.clone();
            if let Err(e) = self.target.module(&mut buf, sigma, &includes, f) {
                return Err(print_err(e, &file, read_to_string(&file)?));
            }
        }

        if buf.is_empty() {
            return Ok(());
        }

        let module_dir = module.to_source_path(&self.outdir);
        let module_index_file = module_dir.join(self.target.filename());
        create_dir_all(&module_dir)?;
        write(&module_index_file, &buf)?;

        for file in includes {
            let to = module_dir.join(file.file_name().unwrap());
            copy(file, to)?;
        }

        Ok(())
    }
}

fn mangle(loc: Loc, tm: &Term) -> Result<String, Error> {
    use Term::*;
    Ok(match tm {
        Ref(_) => return Err(NonErasable(tm.clone(), loc)),

        Pi(p, b) => format!("({}{})", mangle(loc, &p.typ)?, mangle(loc, b)?),
        Unit => "U".to_string(),
        Boolean => "T".to_string(),
        String => "S".to_string(),
        Number => "N".to_string(),
        BigInt => "B".to_string(),
        Fields(fields) => {
            let mut vals = fields.iter().collect::<Vec<_>>();
            vals.sort_by_key(|p| p.0);
            let mut ms = Vec::default();
            for (name, tm) in vals {
                ms.push(format!("{name}{}", mangle(loc, tm)?))
            }
            ms.join("")
        }
        Object(f) => format!("{{{}}}", mangle(loc, f)?),
        Enum(f) => format!("[{}]", mangle(loc, f)?),

        _ => unreachable!(),
    })
}

pub fn mangle_hkt(loc: Loc, n: &str, ts: &Vec<Term>) -> Result<String, Error> {
    let mut ms = vec![n.to_string()];
    for t in ts {
        ms.push(mangle(loc, t)?)
    }
    Ok(ms.join(""))
}
