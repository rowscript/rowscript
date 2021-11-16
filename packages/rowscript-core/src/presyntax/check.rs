use crate::basis::data::{Ident, Lvl};
use crate::presyntax::data::Term;
use crate::syntax::data as V;
use std::collections::HashMap;
use tree_sitter::Point;

#[derive(Debug)]
pub enum CheckError {
    NameNotInScope(Ident),
    CantUnify(Term, Term),
}

#[derive(Debug)]
enum BD {
    Bound,
    Defined,
}

#[derive(Debug, Default)]
pub struct Ctx {
    env: Vec<V::Term>,
    lvl: Lvl,
    raw_named: HashMap<String, V::Term>,
    bds: Vec<BD>,
    pt: Point,
}

impl Ctx {
    pub fn new() -> Ctx {
        Default::default()
    }

    pub fn check(&mut self, tm: &mut Term) -> Result<(), CheckError> {
        Ok(())
    }
}
