use std::fmt::{Display, Formatter};

use crate::theory::abs::data::Term::{Lam, Pi};
use crate::theory::{LocalVar, Param, ParamInfo, Syntax, Tele};

pub type Spine = Vec<(ParamInfo, Term)>;

#[derive(Debug, Copy, Clone)]
pub enum Dir {
    Lt,
    Gt,
}

impl Display for Dir {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Dir::Lt => "<",
            Dir::Gt => ">",
        })
    }
}

#[derive(Debug, Clone)]
pub enum Term {
    Ref(LocalVar),
    MetaRef(LocalVar, Spine),

    Let(Param<Self>, Box<Self>, Box<Self>),

    Univ,

    Pi(Param<Self>, Box<Self>),
    Lam(Param<Self>, Box<Self>),
    App(Box<Self>, Box<Self>),

    Sigma(Param<Self>, Box<Self>),
    Tuple(Box<Self>, Box<Self>),
    TupleLet(Param<Self>, Param<Self>, Box<Self>, Box<Self>),

    Unit,
    TT,
    UnitLet(Box<Self>, Box<Self>),

    Boolean,
    False,
    True,
    If(Box<Self>, Box<Self>, Box<Self>),

    String,
    Str(String),

    Number,
    Num(String, f64),

    BigInt,
    Big(String),

    RowOrd(Box<Self>, Dir, Box<Self>),
    RowSat,

    RowEq(Box<Self>, Box<Self>),
    RowRefl,

    Row,
    Fields(Vec<(String, Self)>),
    Label(String, Box<Self>),
    Unlabel(Box<Self>, String),

    Object(Box<Self>),
    Prj(Dir, Box<Self>),
    Concat(Box<Self>, Box<Self>),

    Variant(Box<Self>),
    Inj(Dir, Box<Self>),
    Branch(Box<Self>, Box<Self>),
}

impl Term {
    pub fn lam(tele: &Tele<Term>, tm: Box<Term>) -> Box<Term> {
        tele.iter().rfold(tm, |b, p| Box::new(Lam(p.clone(), b)))
    }

    pub fn pi(tele: &Tele<Term>, tm: Box<Term>) -> Box<Term> {
        tele.iter().rfold(tm, |b, p| Box::new(Pi(p.clone(), b)))
    }

    pub fn tele_to_spine(tele: &Tele<Term>) -> Spine {
        tele.into_iter()
            .map(|p| (p.info, Self::Ref(p.var.clone())))
            .collect()
    }
}

impl Syntax for Term {}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Term::*;
        f.write_str(
            match self {
                Ref(r) => r.to_string(),
                MetaRef(r, sp) => {
                    let mut s = vec![r.to_string()];
                    s.extend(
                        sp.into_iter()
                            .map(|(i, tm)| match i {
                                ParamInfo::Explicit => tm.to_string(),
                                ParamInfo::Implicit => format!("{{{}}}", tm.to_string()),
                            })
                            .collect::<Vec<_>>(),
                    );
                    format!("({})", s.join(" "))
                }
                Let(p, a, b) => format!("let {p} = {a}; {b}"),
                Univ => "type".to_string(),
                Pi(p, b) => format!("{p} -> {b}"),
                Lam(p, b) => format!("{p} => {b}"),
                App(f, x) => format!("({f}) ({x})"),
                Sigma(p, b) => format!("{p} * {b}"),
                Tuple(a, b) => format!("({a}, {b})"),
                TupleLet(p, q, a, b) => format!("let ({p}, {q}) = {a}; {b}"),
                Unit => "unit".to_string(),
                TT => "()".to_string(),
                UnitLet(a, b) => format!("let _ = {a}; {b}"),
                Boolean => "boolean".to_string(),
                False => "false".to_string(),
                True => "true".to_string(),
                If(p, t, e) => format!("if {p} {{ {t} }} else {{ {e} }}"),
                String => "string".to_string(),
                Str(v) => v.clone(),
                Number => "number".to_string(),
                Num(v, _) => v.clone(),
                BigInt => "bigint".to_string(),
                Big(v) => v.clone(),
                _ => todo!(),
            }
            .as_str(),
        )
    }
}
