use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};

use crate::theory::abs::data::Term;
use crate::theory::abs::def::Body::Postulate;
use crate::theory::{Loc, LocalVar, Param, Syntax};

pub type Sigma = HashMap<LocalVar, Def<Term>>;
pub type Gamma = HashMap<LocalVar, Box<Term>>;
pub type Rho = HashMap<LocalVar, Box<Term>>;

#[derive(Debug)]
pub struct Def<T: Syntax> {
    pub loc: Loc,
    pub name: LocalVar,
    pub tele: Vec<Param<T>>,
    pub ret: Box<T>,
    pub body: Body<T>,
}

impl<T: Syntax> Display for Def<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Body::*;
        f.write_str(
            match &self.body {
                Fun(f) => format!(
                    "function {}{}: {} {{\n\t{}\n}}",
                    self.name,
                    self.tele
                        .iter()
                        .map(|p| p.to_string())
                        .collect::<Vec<_>>()
                        .join(" "),
                    self.ret,
                    f
                ),
                Postulate => format!(
                    "function {}{}: {};",
                    self.name,
                    self.tele
                        .iter()
                        .map(|p| p.to_string())
                        .collect::<Vec<_>>()
                        .join(" "),
                    self.ret,
                ),
            }
            .as_str(),
        )
    }
}

#[derive(Debug)]
pub enum Body<T: Syntax> {
    Fun(Box<T>),
    Postulate,
}

impl<T: Syntax> Def<T> {
    pub fn fun(loc: Loc, name: LocalVar, tele: Vec<Param<T>>, ret: Box<T>, body: Box<T>) -> Self {
        Self {
            loc,
            name,
            tele,
            ret,
            body: Body::Fun(body),
        }
    }

    pub fn postulate(loc: Loc, name: LocalVar, tele: Vec<Param<T>>, ret: Box<T>) -> Self {
        Self {
            loc,
            name,
            tele,
            ret,
            body: Postulate,
        }
    }
}
