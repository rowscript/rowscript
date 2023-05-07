use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::path::{Path, PathBuf};

use crate::theory::abs::data::Term;
use crate::theory::abs::def::Def;
use crate::theory::{Loc, Var};
use crate::{Error, OUTDIR};

#[cfg(not(test))]
const MODULES_DIR: &str = "node_modules";
#[cfg(test)]
const MODULES_DIR: &str = "test_modules";

const PKG_DIR: &str = "rowscript";
const STD_PKG_DIR: &str = "std";

const PRELUDE_DIR: &str = "prelude";

#[cfg(not(test))]
pub fn prelude_path() -> PathBuf {
    use std::env::var;
    match var("ROWS_PRELUDE_DIR") {
        Ok(p) => p.into(),
        Err(_) => Path::new(MODULES_DIR)
            .join(PKG_DIR)
            .join("core")
            .join(PRELUDE_DIR),
    }
}

#[cfg(test)]
pub fn prelude_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(PRELUDE_DIR)
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum ImportedPkg {
    Std(String),
    Vendor(String, String),
    Relative,
}

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub struct ModuleID {
    pub pkg: ImportedPkg,
    pub modules: PathBuf,
}

impl ModuleID {
    pub fn to_source_path(&self, base: &Path) -> PathBuf {
        use ImportedPkg::*;
        let mut ret = match &self.pkg {
            Std(pkg) => base
                .join(MODULES_DIR)
                .join(PKG_DIR)
                .join(STD_PKG_DIR)
                .join(pkg),
            Vendor(org, pkg) => base.join(MODULES_DIR).join(org).join(pkg),
            Relative => base.to_path_buf(),
        };
        ret.extend(&self.modules);
        ret
    }

    pub fn to_generated_path(&self) -> PathBuf {
        use ImportedPkg::*;
        let mut p = match &self.pkg {
            Std(p) => Path::new(PKG_DIR).join(STD_PKG_DIR).join(OUTDIR).join(p),
            Vendor(o, p) => Path::new(o).join(p).join(OUTDIR),
            Relative => PathBuf::from("."),
        };
        p.extend(&self.modules);
        p
    }

    pub fn should_generate(&self) -> bool {
        use ImportedPkg::*;
        match self.pkg {
            Std(_) | Vendor(_, _) => false,
            Relative => true,
        }
    }
}

impl Default for ModuleID {
    fn default() -> Self {
        Self {
            pkg: ImportedPkg::Relative,
            modules: Default::default(),
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
    Unqualified(Vec<(Loc, String)>),
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

#[derive(Default)]
pub struct Loaded(HashMap<ModuleID, HashMap<String, Var>>);

impl Loaded {
    pub fn contains(&self, module: &ModuleID) -> bool {
        self.0.contains_key(module)
    }

    pub fn get(&self, module: &ModuleID, n: &String) -> Option<&Var> {
        self.0.get(module).and_then(|m| m.get(n))
    }

    pub fn insert(&mut self, module: &ModuleID, def: &Def<Term>) -> Result<(), Error> {
        match self.0.get_mut(module) {
            Some(m) => {
                if m.insert(def.name.to_string(), def.name.clone()).is_some() {
                    return Err(Error::DuplicateName(def.loc));
                }
            }
            None => {
                self.0.insert(
                    module.clone(),
                    HashMap::from([(def.name.to_string(), def.name.clone())]),
                );
            }
        }
        Ok(())
    }
}
