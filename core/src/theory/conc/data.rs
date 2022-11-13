use crate::theory::{LineCol, LocalVar, Param, Syntax};

#[derive(Debug)]
pub enum Expr {
    Unresolved(LineCol, LocalVar),
    Resolved(LineCol, LocalVar),
    Let(LineCol, Param<Self>, Box<Self>, Box<Self>),

    Univ(LineCol),

    Pi(LineCol, Param<Self>, Box<Self>),
    TupledLam(LineCol, Vec<LocalVar>, Box<Self>),
    App(LineCol, Box<Self>, Box<Self>),

    Sig(LineCol, Param<Self>, Box<Self>),
    Pair(LineCol, Box<Self>, Box<Self>),
    PairLet(LineCol, Param<Self>, Param<Self>, Box<Self>, Box<Self>),

    Unit(LineCol),
    TT(LineCol),
    UnitLet(LineCol, Box<Self>, Box<Self>),

    Boolean(LineCol),
    False(LineCol),
    True(LineCol),
    IfThenElse(LineCol, Box<Self>, Box<Self>, Box<Self>),

    String(LineCol),
    Str(LineCol, String),

    Number(LineCol),
    Num(LineCol, String),

    BigInt(LineCol),
    Big(LineCol, String),
}

impl Syntax for Expr {}
