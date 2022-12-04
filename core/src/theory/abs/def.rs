use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};

use crate::theory::abs::data::Term;
use crate::theory::ParamInfo::Explicit;
use crate::theory::{Loc, LocalVar, Param, Syntax, Tele};

pub type Sigma = HashMap<LocalVar, Def<Term>>;
pub type Gamma = HashMap<LocalVar, Box<Term>>;
pub type Rho = HashMap<LocalVar, Box<Term>>;

pub fn gamma_to_tele(g: &Gamma) -> Tele<Term> {
    g.into_iter()
        .map(|(v, typ)| Param {
            var: v.clone(),
            info: Explicit,
            typ: typ.clone(),
        })
        .collect()
}

#[derive(Debug)]
pub struct Def<T: Syntax> {
    pub loc: Loc,
    pub name: LocalVar,
    pub tele: Tele<T>,
    pub ret: Box<T>,
    pub body: Body<T>,
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

#[derive(Debug)]
pub enum Body<T: Syntax> {
    Fun(Box<T>),
    Postulate,
    Meta(Option<T>),
}
