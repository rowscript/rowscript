use crate::basis::data::{Ident, Ix, Lvl};
use crate::presyntax::check::CheckError::NameNotInScope;
use crate::presyntax::data::Term::Var;
use crate::presyntax::data::{Term, Type};
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
struct Env {
    env: Vec<(String, Term)>,
}

impl Env {
    fn resolve_name(&self, var: &mut Term) -> Result<(), CheckError> {
        if let Var(ident, ix) = var {
            for i in 0..self.env.len() {
                if ident.text == self.env[i].0 {
                    *ix = i as Ix
                }
            }
            return Err(NameNotInScope(ident.to_owned()));
        }
        unreachable!()
    }
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

    pub fn scope_check(&mut self, tm: &mut Term) -> Result<(), CheckError> {
        todo!()
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
