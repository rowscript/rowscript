use std::fmt::{Display, Formatter};

use crate::theory::abs::data::Term::{Lam, Pi};
use crate::theory::{LocalVar, Param, Syntax};

#[derive(Debug, Copy, Clone)]
pub enum Dir {
    Left,
    Right,
}

#[derive(Debug, Clone)]
pub enum Term {
    Ref(LocalVar),
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

    RowConcatEq(Box<Self>, Box<Self>, Box<Self>),
    RowRefl,

    RowCont(Dir, Box<Self>, Box<Self>),
    RowSat,

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
    pub fn lam(tele: &Vec<Param<Term>>, tm: Box<Term>) -> Box<Term> {
        tele.iter().rfold(tm, |b, p| Box::new(Lam(p.clone(), b)))
    }

    pub fn pi(tele: &Vec<Param<Term>>, tm: Box<Term>) -> Box<Term> {
        tele.iter().rfold(tm, |b, p| Box::new(Pi(p.clone(), b)))
    }
}

impl Syntax for Term {}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Term::*;
        f.write_str(
            match self {
                Ref(r) => r.to_string(),
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
