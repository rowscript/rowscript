use std::path::{Path, PathBuf};

#[cfg(not(test))]
const MODULES_DIR: &str = "node_modules";
#[cfg(test)]
const MODULES_DIR: &str = "test_modules";

#[derive(Debug, Hash, Eq, PartialEq)]
pub enum ImportedPkg {
    Std(String),
    Vendor(String, String),
    Local,
}

#[derive(Debug, Hash, Eq, PartialEq)]
pub struct ModuleID {
    pkg: ImportedPkg,
    modules: PathBuf,
}

impl ModuleID {
    pub fn new(pkg: ImportedPkg, modules: PathBuf) -> Self {
        Self { pkg, modules }
    }

    pub fn to_path_buf(&self, base: &Path) -> PathBuf {
        use ImportedPkg::*;
        let mut ret = match &self.pkg {
            Std(pkg) => base.join(MODULES_DIR).join("rowscript").join(pkg),
            Vendor(org, pkg) => base.join(MODULES_DIR).join(org).join(pkg),
            Local => base.to_path_buf(),
        };
        ret.extend(&self.modules);
        ret
    }

    pub fn should_generate(&self) -> bool {
        use ImportedPkg::*;
        match self.pkg {
            Std(_) | Vendor(_, _) => false,
            Local => true,
        }
    }
}

impl Default for ModuleID {
    fn default() -> Self {
        Self {
            pkg: ImportedPkg::Local,
            modules: Default::default(),
        }
    }
}

#[derive(Debug)]
pub enum ImportedDefs {
    Unqualified(Vec<String>),
    Qualified,
    Unused,
}

#[derive(Debug)]
pub struct Import {
    pub module: ModuleID,
    defs: ImportedDefs,
}

impl Import {
    pub fn new(module: ModuleID, defs: ImportedDefs) -> Self {
        Self { module, defs }
    }
}
