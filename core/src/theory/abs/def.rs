use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};

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
    let info = Explicit;
    g.clone()
        .into_iter()
        .map(|(var, typ)| Param { var, info, typ })
        .collect()
}

pub fn tele_to_refs(tele: &Tele<Term>) -> Box<[Term]> {
    tele.iter().map(|p| Term::Ref(p.var.clone())).collect()
}

#[derive(Clone, Debug)]
pub struct Def<T: Syntax> {
    pub loc: Loc,
    pub name: Var,
    pub tele: Tele<T>,
    pub eff: Box<T>,
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
            Fn(f) => self.to_lam_term(*f.clone()),
            Postulate => Term::Extern(v),
            Alias(t) => self.to_lam_term(*t.clone()),
            Constant(_, f) => self.to_lam_term(*f.clone()),
            Verify(..) => unreachable!(),

            Interface { .. } => {
                let r = Term::Ref(self.tele[0].var.clone());
                self.to_lam_term(Term::Instanceof(Box::new(r), v))
            }
            Instance { .. } => unreachable!(),
            InstanceFn(f) => self.to_lam_term(*f.clone()),
            InterfaceFn(is_capability, i) => {
                let r = Term::Ref(self.tele[0].var.clone());
                let mut f = Term::Find {
                    is_capability: *is_capability,
                    instance_ty: Box::new(r),
                    interface: i.clone(),
                    interface_fn: v,
                };
                for p in self.tele.iter().skip(1) {
                    f = Term::App(
                        Box::new(f),
                        p.info.into(),
                        Box::new(Term::Ref(p.var.clone())),
                    );
                }
                self.to_lam_term(f)
            }

            Class {
                associated,
                members,
                ..
            } => self.to_lam_term(Term::Cls {
                class: self.name.clone(),
                type_args: self.tele.iter().map(|p| Term::Ref(p.var.clone())).collect(),
                associated: associated
                    .iter()
                    .map(|(n, v)| (n.clone(), Term::Ref(v.clone())))
                    .collect(),
                object: Box::new(Term::Object(Box::new(Term::Fields(
                    members
                        .iter()
                        .map(|(_, id, typ)| (id.clone(), typ.clone()))
                        .collect(),
                )))),
            }),
            Associated(t) => self.to_lam_term(*t.clone()),
            Method { f, .. } => self.to_lam_term(*f.clone()),

            Undefined => Term::Undef(v),
            Meta(_, s) => match s {
                None => unreachable!(),
                Some(f) => self.to_lam_term(*f.clone()),
            },
        }
    }

    fn to_lam_term(&self, f: Term) -> Term {
        *rename(Box::new(Term::lam(&self.tele, f)))
    }

    pub fn to_type(&self) -> Term {
        *rename(Box::new(Term::pi(
            &self.tele,
            *self.eff.clone(),
            *self.ret.clone(),
        )))
    }

    pub fn to_eff(&self) -> Term {
        *rename(self.eff.clone())
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
                    "function {} {}: {};",
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
                Constant(anno, f) => {
                    if *anno {
                        format!("const {}: {} = {f};", self.name, self.ret)
                    } else {
                        format!("const {} = {f};", self.name)
                    }
                }
                Verify(a) => format!(
                    "declare {a} {}: {};",
                    Param::tele_to_string(&self.tele),
                    self.ret
                ),
                Interface {
                    is_capability,
                    fns,
                    instances,
                } => format!(
                    "{} {} {}: {} {{\n{}\n{}}}",
                    if *is_capability { "throw" } else { "interface" },
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret,
                    fns.iter()
                        .map(|f| format!("\t{f};\n"))
                        .collect::<Vec<_>>()
                        .concat(),
                    instances
                        .iter()
                        .map(|f| format!("\t{f};\n"))
                        .collect::<Vec<_>>()
                        .concat()
                ),
                InterfaceFn(is_capability, i) => format!(
                    "{} function {i}.{} {}: {};",
                    if *is_capability { "throw" } else { "interface" },
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret
                ),
                Instance(body) => body.to_string(),
                InstanceFn(f) => format!(
                    "instanceof function {} {}: {} {{\n\t{f}\n}}",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    self.ret,
                ),

                Class {
                    associated,
                    members,
                    methods,
                    ..
                } => format!(
                    "class {}{} {{\n{}\n{}\n\n{}\n}}",
                    self.name,
                    Param::tele_to_string(&self.tele),
                    associated
                        .iter()
                        .map(|(name, v)| format!("\ttype {name} = {v};\n"))
                        .collect::<Vec<_>>()
                        .concat(),
                    members
                        .iter()
                        .map(|(_, id, typ)| format!("\t{id}: {typ};\n"))
                        .collect::<Vec<_>>()
                        .concat(),
                    methods
                        .iter()
                        .map(|(_, m)| format!("\t{m};\n"))
                        .collect::<Vec<_>>()
                        .concat()
                ),
                Associated(t) => format!(
                    "associated {} {} = {t};",
                    self.name,
                    Param::tele_to_string(&self.tele),
                ),
                Method { f, .. } => format!(
                    "method {} {}: {} {{\n\t{f}\n}}",
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
    Constant(bool, Box<T>),
    Verify(Box<T>),

    Interface {
        is_capability: bool,
        fns: Vec<Var>,
        instances: Vec<Var>,
    },
    InterfaceFn(bool, Var),
    Instance(Box<InstanceBody<T>>),
    InstanceFn(Box<T>),

    Class {
        ctor: Var,
        associated: HashMap<String, Var>,
        members: Vec<(Loc, String, T)>,
        methods: HashMap<String, Var>,
    },
    Associated(Box<T>),
    Method {
        class: Var,
        /// Only usable during name resolving.
        associated: HashMap<String, Var>,
        f: Box<T>,
    },

    Undefined,
    Meta(MetaKind, Option<Box<T>>),
}

#[derive(Clone, Debug)]
pub struct InstanceBody<T: Syntax> {
    pub i: (Var, Box<T>),
    pub fns: HashMap<Var, Var>,
}

impl InstanceBody<Term> {
    pub fn instance_type(&self, sigma: &Sigma) -> Result<Term, Error> {
        use Body::*;
        use Error::*;
        use Term::*;
        Ok(match self.i.1.as_ref() {
            Ref(inst) => {
                let inst = inst.clone();
                let def = sigma.get(&inst).unwrap();
                if !matches!(def.body, Alias(_)) {
                    return Err(ExpectedAlias(Ref(inst), def.loc));
                }
                def.to_term(inst.clone())
            }
            tm => tm.clone(),
        })
    }
}

impl<T: Syntax> Display for InstanceBody<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "instanceof {} for {} {{\n{}}}",
            self.i.0,
            self.i.1,
            self.fns
                .iter()
                .map(|(i, inst)| format!("\t{i}; {inst};\n"))
                .collect::<Vec<_>>()
                .concat()
        )
    }
}
