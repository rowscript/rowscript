use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::path::{Path, PathBuf};

use crate::theory::abs::data::Term;
use crate::theory::abs::def::Def;
use crate::theory::{Loc, Var};
use crate::{Error, OUT_DIR, Src};

#[cfg(not(test))]
const MODULES_DIR: &str = "node_modules";
#[cfg(test)]
const MODULES_DIR: &str = "test_modules";

const PKG_DIR: &str = "rowscript";
const STD_PKG_DIR: &str = "std";

#[derive(Default, Debug, Hash, Eq, PartialEq, Clone)]
pub enum ImportedPkg {
    #[default]
    Root,
    Std(Src),
    Vendor(Src, Src),
}

#[derive(Default, Debug, Hash, Eq, PartialEq, Clone)]
pub struct ModuleID {
    pub pkg: ImportedPkg,
    pub modules: PathBuf,
}

impl ModuleID {
    pub fn to_source_path(&self, base: &Path) -> Box<Path> {
        use ImportedPkg::*;
        let mut ret = match &self.pkg {
            Std(pkg) => base
                .join(MODULES_DIR)
                .join(PKG_DIR)
                .join(STD_PKG_DIR)
                .join(pkg),
            Vendor(org, pkg) => base.join(MODULES_DIR).join(org).join(pkg),
            Root => base.to_path_buf(),
        };
        ret.extend(&self.modules);
        ret.into()
    }

    pub fn to_generated_path(&self) -> Box<Path> {
        use ImportedPkg::*;
        let mut p = match &self.pkg {
            Std(p) => Path::new(PKG_DIR).join(STD_PKG_DIR).join(OUT_DIR).join(p),
            Vendor(o, p) => Path::new(o).join(p).join(OUT_DIR),
            Root => PathBuf::from("."),
        };
        p.extend(&self.modules);
        p.into()
    }

    pub fn should_generate(&self) -> bool {
        use ImportedPkg::*;
        match self.pkg {
            Std(_) | Vendor(_, _) => false,
            Root => true,
        }
    }
}

impl Display for ModuleID {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.to_generated_path().to_str().unwrap())
    }
}

#[derive(Debug)]
pub enum ImportedDefs {
    Unqualified(Vec<(Loc, Src)>),
    Qualified,
    Loaded,
}

#[derive(Debug)]
pub struct Import {
    pub loc: Loc,
    pub module: ModuleID,
    pub defs: ImportedDefs,
}

impl Import {
    pub fn new(loc: Loc, module: ModuleID, defs: ImportedDefs) -> Self {
        Self { loc, module, defs }
    }
}

#[derive(Default, Clone)]
pub struct Loaded(HashMap<ModuleID, HashMap<Src, Var>>);

impl Loaded {
    pub fn contains(&self, module: &ModuleID) -> bool {
        self.0.contains_key(module)
    }

    pub fn get(&self, module: &ModuleID, n: Src) -> Option<&Var> {
        self.0.get(module).and_then(|m| m.get(n))
    }

    pub fn insert(&mut self, module: &ModuleID, def: &Def<Term>) -> Result<(), Error> {
        match self.0.get_mut(module) {
            Some(m) => {
                if m.insert(def.name.as_str(), def.name.clone()).is_some() {
                    return Err(Error::DuplicateName(def.loc));
                }
            }
            None => {
                self.0.insert(
                    module.clone(),
                    HashMap::from([(def.name.as_str(), def.name.clone())]),
                );
            }
        }
        Ok(())
    }
}
