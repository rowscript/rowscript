use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Def, Sigma};
use crate::theory::Loc;
use crate::Error::NonErasable;
use crate::{print_err, Error};
use std::fs::write;
use std::path::PathBuf;

#[cfg(feature = "codegen-ecma")]
pub mod ecma;
pub mod noop;

pub trait Target {
    fn filename(&self) -> &'static str;
    fn decls(
        &mut self,
        buf: &mut Vec<u8>,
        sigma: &Sigma,
        defs: Vec<Def<Term>>,
    ) -> Result<(), Error>;
}

pub struct Codegen {
    target: Box<dyn Target>,
    buf: Vec<u8>,
    pub outfile: PathBuf,
}

impl Codegen {
    pub fn new(target: Box<dyn Target>, outdir: &PathBuf) -> Self {
        let outfile = outdir.join(target.filename());
        Self {
            target,
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
                .decls(&mut self.buf, sigma, defs)
                .map_err(|e| print_err(e, &path, &src))?;
        }
        if !self.buf.is_empty() {
            write(&self.outfile, &self.buf)?
        }
        Ok(())
    }
}

fn mangle(loc: Loc, tm: &Term) -> Result<String, Error> {
    use Term::*;
    Ok(match tm {
        Ref(_) => return Err(NonErasable(Box::new(tm.clone()), loc)),

        Pi(p, b) => format!("({}{})", mangle(loc, &*p.typ)?, mangle(loc, &**b)?),
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
        Object(f) => format!("{{{}}}", mangle(loc, &**f)?),
        Enum(f) => format!("[{}]", mangle(loc, &**f)?),

        _ => unreachable!(),
    })
}

fn mangle_hkt(loc: Loc, n: &String, ts: &Vec<Term>) -> Result<String, Error> {
    let mut ms = vec![n.clone()];
    for t in ts {
        ms.push(mangle(loc, t)?)
    }
    Ok(ms.join(""))
}
