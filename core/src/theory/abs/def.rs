use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};

use crate::theory::abs::data::Term;
use crate::theory::abs::def::Body::Meta;
use crate::theory::abs::rename::rename;
use crate::theory::conc::data::Expr;
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

impl Def<Expr> {
    pub fn to_type(&self) -> Box<Expr> {
        Expr::pi(&self.tele, self.ret.clone())
    }
}

impl Def<Term> {
    pub fn to_term(&self, v: Var) -> Box<Term> {
        use Body::*;
        match &self.body {
            Fun(f) => rename(Term::lam(&self.tele, f.clone())),
            Postulate => Box::new(Term::Ref(v)),
            Alias(t) => rename(Term::lam(&self.tele, t.clone())),
            Undefined => Box::new(Term::Undef(v)),
            Class { object, .. } => rename(Term::lam(&self.tele, object.clone())),
            _ => unreachable!(),
        }
    }

    pub fn to_type(&self) -> Box<Term> {
        Term::pi(&self.tele, self.ret.clone())
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
                    "declare {} {}: {};",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret,
                ),
                Alias(t) => format!(
                    "type {}{}: {} = {};",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret,
                    t,
                ),
                Class {
                    object,
                    methods,
                    ctor,
                    vptr,
                    vptr_ctor,
                    vtbl,
                    vtbl_lookup,
                } => {
                    format!(
                        "class {}{} {{
    {object}
    {};
    {ctor};
    {vptr};
    {vptr_ctor};
    {vtbl};
    {vtbl_lookup};
}}",
                        self.name,
                        Param::tele_to_string(&self.tele),
                        methods
                            .iter()
                            .map(|m| m.to_string())
                            .collect::<Vec<_>>()
                            .join(";\n\t")
                    )
                }
                Interface(ty) => format!("interface {} {{\n\t{ty}\n}}", self.name),
                Implements { ty, funcs } => format!(
                    "implements {} for {ty} {{\n{}\t\n}}",
                    self.name,
                    funcs
                        .iter()
                        .map(|f| f.to_string())
                        .collect::<Vec<_>>()
                        .join(";\n\t")
                ),

                Undefined => format!(
                    "undefined {} {}: {}",
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
    Alias(Box<T>),
    Class {
        object: Box<T>,
        methods: Vec<Var>,
        ctor: Var,
        vptr: Var,
        vptr_ctor: Var,
        vtbl: Var,
        vtbl_lookup: Var,
    },
    Interface(Box<T>),
    Implements {
        ty: Box<T>,
        funcs: Vec<Var>,
    },

    Undefined,
    Meta(Option<T>),
}
