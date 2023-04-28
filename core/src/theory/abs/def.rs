use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};

use crate::theory::abs::data::Term::Vp;
use crate::theory::abs::data::{MetaKind, Term};
use crate::theory::abs::rename::rename;
use crate::theory::conc::data::Expr;
use crate::theory::ParamInfo::Explicit;
use crate::theory::{Loc, Param, Syntax, Tele, Var};
use crate::Error;

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

impl<T: Syntax> Def<T> {
    pub fn is_private(&self) -> bool {
        matches!( self.name.as_str().chars().next(), Some(b) if b == '_')
    }
}

impl Def<Expr> {
    pub fn to_type(&self) -> Expr {
        Expr::pi(&self.tele, *self.ret.clone())
    }
}

impl Def<Term> {
    pub fn to_term(&self, v: Var) -> Term {
        use Body::*;
        match &self.body {
            Fn(f) => self.to_lam_term(f.clone()),
            Postulate => Term::Extern(v),
            Alias(t) => self.to_lam_term(t.clone()),

            Class(body) => self.to_lam_term(body.object.clone()),
            Ctor(f) => self.to_lam_term(f.clone()),
            Method(f) => self.to_lam_term(f.clone()),
            VptrType(t) => self.to_lam_term(t.clone()),
            VptrCtor(t) => self.to_lam_term(Vp(
                t.clone(),
                self.tele.iter().map(|p| Term::Ref(p.var.clone())).collect(),
            )),
            VtblType(t) => self.to_lam_term(t.clone()),
            VtblLookup => self.to_lam_term(Term::Lookup(Box::new(Term::Ref(
                self.tele.last().unwrap().var.clone(),
            )))),

            Interface { .. } => {
                let r = Term::Ref(self.tele[0].var.clone());
                self.to_lam_term(Term::ImplementsOf(Box::new(r), v))
            }
            Implements { .. } => unreachable!(),
            ImplementsFn(f) => self.to_lam_term(f.clone()),
            Findable(i) => {
                let r = Term::Ref(self.tele[0].var.clone());
                let mut f = Term::Find(Box::new(r), i.clone(), v);
                for p in self.tele.iter().skip(1) {
                    f = Term::App(
                        Box::new(f),
                        p.info.into(),
                        Box::new(Term::Ref(p.var.clone())),
                    );
                }
                self.to_lam_term(f)
            }

            Undefined => Term::Undef(v),
            Meta(_, s) => match s {
                None => unreachable!(),
                Some(f) => self.to_lam_term(f.clone()),
            },
        }
    }

    fn to_lam_term(&self, f: Term) -> Term {
        rename(Term::lam(&self.tele, f))
    }

    pub fn to_type(&self) -> Term {
        rename(Term::pi(&self.tele, *self.ret.clone()))
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
                Class(body) => format!(
                    "class {} {} {body}",
                    self.name,
                    Param::tele_to_string(&self.tele),
                ),
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
                Implements(body) => body.to_string(),
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
    Fn(T),
    Postulate,
    Alias(T),

    Class(Box<ClassBody<T>>),
    Ctor(T),
    Method(T),
    VptrType(T),
    VptrCtor(String),
    VtblType(T),
    VtblLookup,

    Interface { fns: Vec<Var>, ims: Vec<Var> },
    Implements(Box<ImplementsBody<T>>),
    ImplementsFn(T),
    Findable(Var),

    Undefined,
    Meta(MetaKind, Option<T>),
}

#[derive(Clone, Debug)]
pub struct ClassBody<T: Syntax> {
    pub object: T,
    pub methods: Vec<(String, Var)>,
    pub ctor: Var,
    pub vptr: Var,
    pub vptr_ctor: Var,
    pub vtbl: Var,
    pub vtbl_lookup: Var,
}

impl<T: Syntax> Display for ClassBody<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{{
    {}
    {};
    {};
    {};
    {};
    {};
    {};
}}",
            self.object,
            self.methods
                .iter()
                .map(|m| m.1.to_string())
                .collect::<Vec<_>>()
                .join(";\n    "),
            self.ctor,
            self.vptr,
            self.vptr_ctor,
            self.vtbl,
            self.vtbl_lookup,
        )
    }
}

#[derive(Clone, Debug)]
pub struct ImplementsBody<T: Syntax> {
    pub i: (Var, Box<T>),
    pub fns: HashMap<Var, Var>,
}

impl ImplementsBody<Term> {
    pub fn implementor_type(&self, sigma: &Sigma) -> Result<Term, Error> {
        use Body::*;
        use Error::*;
        use Term::*;
        Ok(match &*self.i.1 {
            Ref(im) => {
                let im = im.clone();
                let def = sigma.get(&im).unwrap();
                if !matches!(def.body, Alias(_)) {
                    return Err(ExpectedAlias(Term::Ref(im), def.loc));
                }
                def.to_term(im.clone())
            }
            tm => tm.clone(),
        })
    }
}

impl<T: Syntax> Display for ImplementsBody<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "implements {} for {} {{\n{}}}",
            self.i.0,
            self.i.1,
            self.fns
                .iter()
                .map(|(i, im)| format!("\t{i}; {im};\n"))
                .collect::<Vec<_>>()
                .concat()
        )
    }
}
