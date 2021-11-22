use crate::basis::data::{Ident, Ix, Lvl};
use crate::conc::check::CheckError::NameNotInScope;
use crate::conc::data::Term::Var;
use crate::conc::data::{Term, Type};
use std::collections::HashMap;
use std::process::id;
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
    env: Vec<Term>,
    lvl: Lvl,
    raw_named: Vec<(String, Term)>,
    bds: Vec<BD>,
    pt: Point,
}

impl Ctx {
    pub fn new() -> Ctx {
        Default::default()
    }

    fn resolve_var(&self, ident: &Ident, ix: &mut Ix) -> Result<(), CheckError> {
        for i in 0..self.raw_named.len() {
            if ident.text == self.raw_named[i].0 {
                *ix = i as Ix
            }
        }
        return Err(NameNotInScope(ident.to_owned()));
    }

    pub fn scope_check(&mut self, tm: &mut Term) -> Result<(), CheckError> {
        match tm {
            Var(ident, ix) => self.resolve_var(ident, ix),
            _ => todo!(),
        }
    }

    pub fn infer(&mut self, tm: Term) -> Result<Type, CheckError> {
        use Term::*;
        match tm {
            Unit => Ok(Type::Unit),
            Str(_) => Ok(Type::Str),
            Num(_) => Ok(Type::Num),
            Bool(_) => Ok(Type::Bool),
            BigInt(_) => Ok(Type::BigInt),
            Tuple(xs) => xs
                .into_iter()
                .map(|x| self.infer(x))
                .collect::<Result<Vec<Type>, _>>()
                .map(|ts| Type::Tuple(ts)),
            _ => todo!(),
        }
    }
}
