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
    g.iter()
        .map(|(v, typ)| Param {
            var: v.clone(),
            info: Explicit,
            typ: typ.clone(),
        })
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
            Const(_, f) => self.to_lam_term(f.clone()),
            Verify(..) => unreachable!(),

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
            Associated(t) => self.to_lam_term(t.clone()),
            Method { f, .. } => self.to_lam_term(f.clone()),

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
                Const(anno, f) => {
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

                Class {
                    associated,
                    members,
                    methods,
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
    Const(bool, T),
    Verify(T),

    Interface {
        fns: Vec<Var>,
        ims: Vec<Var>,
    },
    Implements(Box<ImplementsBody<T>>),
    ImplementsFn(T),
    Findable(Var),

    Class {
        associated: HashMap<String, Var>,
        members: Vec<(Loc, String, T)>,
        methods: HashMap<String, Var>,
    },
    Associated(T),
    Method {
        class: Var,
        /// Only usable during name resolving.
        associated: HashMap<String, Var>,
        f: T,
    },

    Undefined,
    Meta(MetaKind, Option<T>),
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
        Ok(match self.i.1.as_ref() {
            Ref(im) => {
                let im = im.clone();
                let def = sigma.get(&im).unwrap();
                if !matches!(def.body, Alias(_)) {
                    return Err(ExpectedAlias(Ref(im), def.loc));
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
