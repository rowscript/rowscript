use crate::base::{LineCol, LocalVar, Param};

#[derive(Debug)]
pub enum Expr {
    Unresolved(LineCol, LocalVar),
    Resolved(LineCol, LocalVar),
    Let(Param<Self>, Box<Self>, Box<Self>),

    Univ(LineCol),

    Pi(LineCol, Param<Self>, Box<Self>),
    Lam(LineCol, Param<Self>, Box<Self>),
    App(LineCol, Box<Self>, Box<Self>),

    Sig(LineCol, Param<Self>, Box<Self>),
    Pair(LineCol, Box<Self>, Box<Self>),
    PairLet(LineCol, Param<Self>, Param<Self>, Box<Self>, Box<Self>),

    Unit(LineCol),
    TT(LineCol),
    UnitLet(LineCol, Box<Self>, Box<Self>),

    Bool(LineCol),
    False(LineCol),
    True(LineCol),
    IfThenElse(LineCol, Box<Self>, Box<Self>, Box<Self>),
}
