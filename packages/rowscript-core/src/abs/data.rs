use crate::basis::data::{Ident, Ix};
use tree_sitter::Point;

pub type Label = Ident;

#[derive(Debug, PartialEq, Eq)]
pub enum Dir {
    L,
    R,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Row {
    Var(Ident, Ix),
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct SchemeBinder {
    tvars: Vec<Ident>,
    rvars: Vec<Ident>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Scheme {
    Scm {
        binders: SchemeBinder,
        qualified: QualifiedType,
    },
    Meta(Point),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Pred {
    Cont { d: Dir, lhs: Row, rhs: Row },
    Comb { lhs: Row, rhs: Row, result: Row },
}

#[derive(Debug, PartialEq, Eq)]
pub struct QualifiedType {
    pub preds: Vec<Pred>,
    pub typ: Type,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Type {
    Var(Ident, Ix),
    Arrow(Vec<Type>),
    Record(Row),
    Variant(Row),
    Row(Label, Box<Type>),

    Unit,
    Str,
    Num,
    Bool,
    BigInt,

    Array(Box<Type>),
    Tuple(Vec<Type>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Term {
    Var(Ident, Ix),

    Abs(Vec<Ident>, Box<Term>),
    App(Box<Term>, Box<Term>),

    Let(Ident, Scheme, Box<Term>, Box<Term>),

    Rec(Label, Box<Term>),
    Sel(Box<Term>, Label),

    Prj(Dir, Box<Term>),
    Cat(Box<Term>, Box<Term>),

    Inj(Ident, Box<Term>),
    Case(Box<Term>, Box<Term>),

    PrimRef(Ident, Scheme),
    Unit,
    Str(String),
    Num(String),
    Bool(bool),
    BigInt(String),
    Tuple(Vec<Term>),
    Array(Vec<Term>),
    If(Box<Term>, Box<Term>, Box<Term>),
    Subs(Box<Term>, Box<Term>),
}
