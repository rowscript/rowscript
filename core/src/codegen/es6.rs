use crate::codegen::Target;
use crate::theory::abs::data::Term;
use crate::theory::abs::def::Def;
use crate::Error;

#[derive(Default)]
pub struct Es6 {}

impl Target for Es6 {
    fn filename(&self) -> &'static str {
        "index.js"
    }

    fn def(&self, def: Def<Term>, f: &mut String) -> Result<(), Error> {
        todo!()
    }
}
