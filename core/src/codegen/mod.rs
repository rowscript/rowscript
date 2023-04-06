use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Def, Sigma};
use crate::Error;

#[cfg(feature = "codegen-ecma")]
pub mod ecma;
pub mod noop;

pub trait Target {
    fn filename(&self) -> &'static str;
    fn package(&self, buf: &mut Vec<u8>, sigma: &Sigma, defs: Vec<Def<Term>>) -> Result<(), Error>;
}
