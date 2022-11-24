use std::collections::HashMap;
use std::fmt::Debug;

use crate::theory::abs::data::Term;
use crate::theory::abs::def::Body::Fun;
use crate::theory::{Loc, LocalVar, Param, Syntax};

pub type Sigma = HashMap<LocalVar, Def<Term>>;
pub type Gamma = HashMap<LocalVar, Box<Term>>;
pub type Rho = HashMap<LocalVar, Box<Term>>;

pub struct GammaGuard<'a> {
    gamma: &'a mut Gamma,
    ps: &'a [&'a Param<Term>],
}

impl<'a> GammaGuard<'a> {
    pub fn new(gamma: &'a mut Gamma, ps: &'a [&'a Param<Term>]) -> Self {
        for &p in ps {
            gamma.insert(p.var.clone(), p.typ.clone());
        }
        Self { gamma, ps }
    }
}

impl<'a> Drop for GammaGuard<'a> {
    fn drop(&mut self) {
        for p in self.ps {
            self.gamma.remove(&p.var);
        }
    }
}

#[derive(Debug)]
pub struct Def<T: Syntax> {
    pub loc: Loc,
    pub name: LocalVar,
    pub tele: Vec<Param<T>>,
    pub ret: Box<T>,
    pub body: Body<T>,
}

#[derive(Debug)]
pub enum Body<T: Syntax> {
    Fun(Box<T>),
}

impl<T: Syntax> Def<T> {
    pub fn fun(loc: Loc, name: LocalVar, tele: Vec<Param<T>>, ret: Box<T>, body: Box<T>) -> Self {
        Self {
            loc,
            name,
            tele,
            ret,
            body: Fun(body),
        }
    }
}
