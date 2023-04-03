use crate::codegen::Target;
use crate::theory::abs::data::Term;
use crate::theory::abs::def::Def;
use crate::Error;

#[derive(Default)]
pub struct Noop {}

impl Target for Noop {
    fn filename(&self) -> &'static str {
        unreachable!()
    }

    fn def(&self, _: Def<Term>, _: &mut String) -> Result<(), Error> {
        Ok(())
    }
}
