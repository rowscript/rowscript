use crate::basis::data::{Ident, Lvl};

#[derive(Debug)]
pub enum Type {
    Var(Ident, Lvl),
    Arr(Vec<Type>),
    Forall(Ident, Box<Type>),
    Prod(Vec<Type>),
    Coprod(Vec<Type>),
}

#[derive(Debug)]
pub enum Term {
    Var(Ident, Lvl),

    Abs(Vec<(Ident, Type)>, Box<Term>),
    App(Vec<Term>),

    TAbs(Vec<Ident>, Box<Term>),
    TApp(Vec<Term>),

    Cat(Vec<Term>),
    Prj(Box<Term>, i32),

    Inj(Box<Term>, i32),
    Case(Box<Term>, Vec<Term>),
}
