use std::fmt::{Display, Formatter};

use crate::theory::{Loc, LocalVar, Param, Syntax};

#[derive(Debug, Clone)]
pub enum Expr {
    Unresolved(Loc, LocalVar),
    Resolved(Loc, LocalVar),
    Let(Loc, LocalVar, Option<Box<Self>>, Box<Self>, Box<Self>),

    Univ(Loc),

    Pi(Loc, Param<Self>, Box<Self>),
    TupledLam(Loc, Vec<LocalVar>, Box<Self>),
    Lam(Loc, LocalVar, Box<Self>),
    App(Loc, Box<Self>, Box<Self>),

    Sigma(Loc, Param<Self>, Box<Self>),
    Tuple(Loc, Box<Self>, Box<Self>),
    TupleLet(Loc, LocalVar, LocalVar, Box<Self>, Box<Self>),

    Unit(Loc),
    TT(Loc),
    UnitLet(Loc, Box<Self>, Box<Self>),

    Boolean(Loc),
    False(Loc),
    True(Loc),
    If(Loc, Box<Self>, Box<Self>, Box<Self>),

    String(Loc),
    Str(Loc, String),

    Number(Loc),
    Num(Loc, String),

    BigInt(Loc),
    Big(Loc, String),
}

impl Syntax for Expr {}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}
