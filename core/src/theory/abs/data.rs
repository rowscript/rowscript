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
    Num(String),

    BigInt,
    Big(String),

    RowConcatEq(Box<Self>, Box<Self>, Box<Self>),
    RowRefl,

    RowCont(Dir, Box<Self>, Box<Self>),
    RowSat,

    Row(Vec<(String, Self)>),
    Label(String, Box<Self>),
    Unlabel(Box<Self>, String),

    Record(Box<Self>),
    Prj(Dir, Box<Self>),
    Concat(Box<Self>, Box<Self>),

    Variant(Box<Self>),
    Inj(Dir, Box<Self>),
    Branch(Box<Self>, Box<Self>),
}

impl Term {
    pub fn new_lam(tele: &Vec<Param<Term>>, tm: Box<Term>) -> Box<Term> {
        tele.iter().rfold(tm, |b, p| Box::new(Lam(p.to_owned(), b)))
    }

    pub fn new_pi(tele: &Vec<Param<Term>>, tm: Box<Term>) -> Box<Term> {
        tele.iter().rfold(tm, |b, p| Box::new(Pi(p.to_owned(), b)))
    }
}

impl Syntax for Term {}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}
