use crate::codegen::Target;
use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Body, Def, Sigma};
use crate::Error;

#[derive(Default)]
pub struct Es6 {}

impl Es6 {
    fn func(
        &self,
        f: &mut String,
        sigma: &Sigma,
        def: &Def<Term>,
        body: &Box<Term>,
    ) -> Result<(), Error> {
        todo!()
    }

    fn class(&self, f: &mut String, sigma: &Sigma, def: &Def<Term>) -> Result<(), Error> {
        todo!()
    }
}

impl Target for Es6 {
    fn filename(&self) -> &'static str {
        "index.js"
    }

    fn def(&self, f: &mut String, sigma: &Sigma, def: &Def<Term>) -> Result<(), Error> {
        use Body::*;

        match &def.body {
            Fn(body) => self.func(f, sigma, def, body)?,
            Class { .. } => self.class(f, sigma, def)?,

            Undefined => unreachable!(),

            Postulate => {}
            Alias(_) => {}
            Ctor(_) => {}
            Method(_) => {}
            VptrType(_) => {}
            VptrCtor => {}
            VtblType(_) => {}
            VtblLookup => {}
            Interface { .. } => {}
            Implements { .. } => {}
            Meta(_, _) => {}
            Findable(_) => {}
        }

        Ok(())
    }
}
