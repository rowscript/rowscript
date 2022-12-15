use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};

use crate::theory::abs::data::Term;
use crate::theory::abs::def::Body::Meta;
use crate::theory::ParamInfo::Explicit;
use crate::theory::{Loc, Param, Syntax, Tele, Var};

pub type Sigma = HashMap<Var, Def<Term>>;
pub type Gamma = HashMap<Var, Box<Term>>;
pub type Rho = HashMap<Var, Box<Term>>;

pub fn gamma_to_tele(g: &Gamma) -> Tele<Term> {
    g.into_iter()
        .map(|(v, typ)| Param {
            var: v.clone(),
            info: Explicit,
            typ: typ.clone(),
        })
        .collect()
}

#[derive(Clone, Debug)]
pub struct Def<T: Syntax> {
    pub loc: Loc,
    pub name: Var,
    pub tele: Tele<T>,
    pub ret: Box<T>,
    pub body: Body<T>,
}

impl<T: Syntax> Def<T> {
    pub fn new_constant_constraint(loc: Loc, name: Var, ret: Box<T>) -> Self {
        Self {
            loc,
            name,
            tele: Default::default(),
            ret,
            body: Meta(None),
        }
    }
}

impl<T: Syntax> Display for Def<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Body::*;
        f.write_str(
            match &self.body {
                Fun(f) => format!(
                    "function {} {}: {} {{\n\t{}\n}}",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret,
                    f
                ),
                Postulate => format!(
                    "function {}{}: {};",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret,
                ),
                Meta(s) => {
                    let tele = Param::tele_to_string(&self.tele);
                    if let Some(solved) = s {
                        format!(
                            "meta {} {}: {} {{\n\t{}\n}}",
                            self.name, tele, self.ret, solved
                        )
                    } else {
                        format!("meta {} {}: {};", self.name, tele, self.ret,)
                    }
                }
            }
            .as_str(),
        )
    }
}

#[derive(Clone, Debug)]
pub enum Body<T: Syntax> {
    Fun(Box<T>),
    Postulate,
    Meta(Option<T>),
}
