use std::ffi::OsStr;
use std::fs::{copy, create_dir_all, read_to_string, write};
use std::path::{Path, PathBuf};

use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Def, Sigma};
use crate::theory::Loc;
use crate::Error::NonErasable;
use crate::{print_err, Error, ModuleFile};

#[cfg(feature = "codegen-ecma")]
pub mod ecma;
pub mod noop;

pub trait Target {
    fn filename(&self) -> &'static str;
    fn should_import(&self, ext: &OsStr) -> bool;
    fn module(
        &mut self,
        buf: &mut Vec<u8>,
        sigma: &Sigma,
        defs: Vec<Def<Term>>,
        imports: Vec<(&OsStr, PathBuf)>,
    ) -> Result<(), Error>;
}

pub struct Codegen {
    target: Box<dyn Target>,
    buf: Vec<u8>,
    imports: Vec<PathBuf>,
    outdir: PathBuf,
    outfile: PathBuf,
}

impl Codegen {
    pub fn new(target: Box<dyn Target>, outdir: PathBuf) -> Self {
        let outfile = outdir.join(target.filename());
        Self {
            target,
            buf: Default::default(),
            imports: Default::default(),
            outdir,
            outfile,
        }
    }

    pub fn outfile(&self) -> &Path {
        self.outfile.as_path()
    }

    pub fn try_push_import(&mut self, ext: &OsStr, path: &Path) {
        if self.target.should_import(ext) {
            self.imports.push(path.to_path_buf())
        }
    }

    pub fn module(&mut self, sigma: &Sigma, files: Vec<ModuleFile>) -> Result<(), Error> {
        for ModuleFile { file, defs } in files {
            if let Err(e) = self.target.module(
                &mut self.buf,
                sigma,
                defs,
                self.imports
                    .iter()
                    .map(|p| {
                        (
                            p.file_stem().unwrap(),
                            [OsStr::new("."), p.file_name().unwrap()].iter().collect(),
                        )
                    })
                    .collect(),
            ) {
                return Err(print_err(e, &file, read_to_string(&file)?));
            }
        }
        if !self.buf.is_empty() {
            create_dir_all(&self.outdir)?;
            write(&self.outfile, &self.buf)?;
            for file in &self.imports {
                let to = self.outdir.join(file.file_name().unwrap());
                copy(file, to)?;
            }
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

fn mangle_hkt(loc: Loc, n: &str, ts: &Vec<Term>) -> Result<String, Error> {
    let mut ms = vec![n.to_string()];
    for t in ts {
        ms.push(mangle(loc, t)?)
    }
    Ok(ms.join(""))
}
