use crate::theory::{LineCol, LocalVar, Param, Syntax};

#[derive(Debug)]
pub enum Expr {
    Unresolved(LineCol, LocalVar),
    Resolved(LineCol, LocalVar),
    Let(LineCol, LocalVar, Option<Box<Self>>, Box<Self>, Box<Self>),

    Univ(LineCol),

    Pi(LineCol, Param<Self>, Box<Self>),
    TupledLam(LineCol, Vec<LocalVar>, Box<Self>),
    Lam(LineCol, LocalVar, Box<Self>),
    App(LineCol, Box<Self>, Box<Self>),

    Sigma(LineCol, Param<Self>, Box<Self>),
    Tuple(LineCol, Box<Self>, Box<Self>),
    TupleLet(LineCol, LocalVar, LocalVar, Box<Self>, Box<Self>),

    Unit(LineCol),
    TT(LineCol),
    UnitLet(LineCol, Box<Self>, Box<Self>),

    Boolean(LineCol),
    False(LineCol),
    True(LineCol),
    If(LineCol, Box<Self>, Box<Self>, Box<Self>),

    String(LineCol),
    Str(LineCol, String),

    Number(LineCol),
    Num(LineCol, String),

    BigInt(LineCol),
    Big(LineCol, String),
}

impl Syntax for Expr {}
