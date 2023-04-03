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

    fn def<'a>(&self, _: &mut String, _: &'a Sigma, _: &Def<Term>) -> Result<(), Error> {
        Ok(())
    }
}
