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

    Sig(Param<Self>, Box<Self>),
    Pair(Box<Self>, Box<Self>),
    PairLet(Param<Self>, Param<Self>, Box<Self>, Box<Self>),

    Unit,
    TT,
    UnitLet(Box<Self>, Box<Self>),

    Bool,
    False,
    True,
    IfThenElse(Box<Self>, Box<Self>, Box<Self>),

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

impl Syntax for Term {}

pub const U: Term = Term::Univ;
pub const TT: Term = Term::TT;
