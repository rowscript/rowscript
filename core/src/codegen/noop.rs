use crate::codegen::Target;
use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Def, Sigma};
use crate::Error;

#[derive(Default)]
pub struct Noop {}

impl Target for Noop {
    fn filename(&self) -> &'static str {
        unreachable!()
    }

    fn defs(&self, _: &mut Vec<u8>, _: &Sigma, _: Vec<Def<Term>>) -> Result<(), Error> {
        Ok(())
    }
}
