use std::path::{Path, PathBuf};

#[cfg(not(test))]
const MODULES_DIR: &str = "node_modules";
#[cfg(test)]
const MODULES_DIR: &str = "test_modules";

#[derive(Debug)]
pub enum ImportedPkg {
    Std(String),
    Vendor(String, String),
    Local,
}

#[derive(Debug)]
pub enum ImportedItems {
    Initial,
    Unqualified(Vec<String>),
    Qualified,
    Unused,
}

#[derive(Debug)]
pub struct Import {
    pkg: ImportedPkg,
    modules: PathBuf,
    items: ImportedItems,
}

impl Import {
    pub fn new(pkg: ImportedPkg, modules: PathBuf, items: ImportedItems) -> Self {
        Self {
            pkg,
            modules,
            items,
        }
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

impl Default for Import {
    fn default() -> Self {
        Self {
            pkg: ImportedPkg::Local,
            modules: Default::default(),
            items: ImportedItems::Initial,
        }
    }
}
