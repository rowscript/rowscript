use crate::Error;

#[cfg(feature = "codegen-es6")]
pub mod es6;
pub mod noop;

pub trait Codegen {
    fn file(&self, f: &mut String) -> Result<(), Error>;
}
