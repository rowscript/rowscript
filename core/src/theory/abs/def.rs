use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};

use crate::theory::abs::data::Term::Vp;
use crate::theory::abs::data::{MetaKind, Term};
use crate::theory::abs::rename::rename;
use crate::theory::conc::data::Expr;
use crate::theory::ParamInfo::Explicit;
use crate::theory::{Loc, Param, Syntax, Tele, Var};

pub type Sigma = HashMap<Var, Def<Term>>;
pub type Gamma = HashMap<Var, Box<Term>>;
pub type Rho = HashMap<Var, Box<Term>>;

pub fn gamma_to_tele(g: &Gamma) -> Tele<Term> {
    g.iter()
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

impl Def<Expr> {
    pub fn to_type(&self) -> Box<Expr> {
        Expr::pi(&self.tele, self.ret.clone())
    }
}

impl Def<Term> {
    pub fn to_term(&self, v: Var) -> Box<Term> {
        use Body::*;
        match &self.body {
            Fn(f) => self.to_lam_term(f),
            Postulate => Box::new(Term::Extern(v)),
            Alias(t) => self.to_lam_term(t),

            Class { object, .. } => self.to_lam_term(object),
            Ctor(f) => self.to_lam_term(f),
            Method(f) => self.to_lam_term(f),
            VptrType(t) => self.to_lam_term(t),
            VptrCtor(t) => self.to_lam_term(&Box::new(Vp(
                t.clone(),
                self.tele.iter().map(|p| Term::Ref(p.var.clone())).collect(),
            ))),
            VtblType(t) => self.to_lam_term(t),
            VtblLookup => self.to_lam_term(&Box::new(Term::Lookup(Box::new(Term::Ref(
                self.tele.last().unwrap().var.clone(),
            ))))),

            Interface { .. } => {
                let r = Box::new(Term::Ref(self.tele[0].var.clone()));
                self.to_lam_term(&Box::new(Term::ImplementsOf(r, v)))
            }
            Implements { .. } => unreachable!(),
            ImplementsFn(f) => self.to_lam_term(f),
            Findable(i) => {
                let r = Box::new(Term::Ref(self.tele[0].var.clone()));
                let mut f = Box::new(Term::Find(r, i.clone(), v));
                for p in self.tele.iter().skip(1) {
                    f = Box::new(Term::App(
                        f,
                        p.info.into(),
                        Box::new(Term::Ref(p.var.clone())),
                    ));
                }
                self.to_lam_term(&f)
            }

            Undefined => Box::new(Term::Undef(v)),
            Meta(_, s) => match s {
                None => unreachable!(),
                Some(f) => self.to_lam_term(&Box::new(f.clone())),
            },
        }
    }

    fn to_lam_term(&self, f: &Term) -> Box<Term> {
        Box::new(rename(Term::lam(&self.tele, f.clone())))
    }

    pub fn to_type(&self) -> Box<Term> {
        Box::new(rename(Term::pi(&self.tele, *self.ret.clone())))
    }
}

impl<T: Syntax> Display for Def<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Body::*;
        f.write_str(
            match &self.body {
                Fn(f) => format!(
                    "function {} {}: {} {{\n\t{f}\n}}",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret,
                ),
                Postulate => format!(
                    "declare function {} {}: {};",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret,
                ),
                Alias(t) => format!(
                    "type {} {}: {} = {t};",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret,
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
                        "class {} {} {{
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
                            .map(|m| m.1.to_string())
                            .collect::<Vec<_>>()
                            .join(";\n    ")
                    )
                }
                Ctor(f) => format!(
                    "constructor {} {}: {} {{\n\t{f}\n}}",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret,
                ),
                Method(f) => format!(
                    "method {} {}: {} {{\n\t{f}\n}}",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret,
                ),
                VptrType(t) => format!(
                    "vptr {} {}: {} = {t};",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret,
                ),
                VptrCtor(t) => format!(
                    "vptr {t} {}: {};",
                    Param::tele_to_string(&self.tele),
                    self.ret,
                ),
                VtblType(t) => format!(
                    "vtbl {} {}: {} = {t};",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret,
                ),
                VtblLookup => format!(
                    "vtbl {} {}: {};",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret,
                ),
                Interface { fns, ims } => format!(
                    "interface {} {}: {} {{\n{}\n{}}}",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret,
                    fns.iter()
                        .map(|f| format!("\t{f};\n"))
                        .collect::<Vec<_>>()
                        .concat(),
                    ims.iter()
                        .map(|f| format!("\t{f};\n"))
                        .collect::<Vec<_>>()
                        .concat()
                ),
                Implements { i: (i, im), fns } => format!(
                    "implements {i} for {im} {{\n{}}}",
                    fns.iter()
                        .map(|(i, im)| format!("\t{i}; {im};\n"))
                        .collect::<Vec<_>>()
                        .concat()
                ),
                ImplementsFn(f) => format!(
                    "implements function {} {}: {} {{\n\t{f}\n}}",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret,
                ),

                Undefined => format!(
                    "undefined {} {}: {};",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret,
                ),
                Meta(k, s) => {
                    let tele = Param::tele_to_string(&self.tele);
                    match s {
                        Some(a) => {
                            format!("meta {k}{} {tele}: {} {{\n\t{a}\n}}", self.name, self.ret)
                        }
                        None => format!("meta {k}{} {tele}: {};", self.name, self.ret),
                    }
                }
                Findable(i) => format!(
                    "findable {i}.{} {}: {};",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret
                ),
            }
            .as_str(),
        )
    }
}

#[derive(Clone, Debug)]
pub enum Body<T: Syntax> {
    Fn(Box<T>),
    Postulate,
    Alias(Box<T>),

    Class {
        object: Box<T>,
        methods: Vec<(String, Var)>,
        ctor: Var,
        vptr: Var,
        vptr_ctor: Var,
        vtbl: Var,
        vtbl_lookup: Var,
    },
    Ctor(Box<T>),
    Method(Box<T>),
    VptrType(Box<T>),
    VptrCtor(String),
    VtblType(Box<T>),
    VtblLookup,

    Interface {
        fns: Vec<Var>,
        ims: Vec<Var>,
    },
    Implements {
        i: (Var, Var),
        fns: HashMap<Var, Var>,
    },
    ImplementsFn(Box<T>),
    Findable(Var),

    Undefined,
    Meta(MetaKind, Option<T>),
}
