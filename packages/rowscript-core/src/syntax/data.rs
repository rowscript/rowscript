use crate::basis::data::Ident;

enum Type {
    Var(Ident),
    Arr(Vec<Type>),
    Forall(Ident, Box<Type>),
    Prod(Vec<Type>),
    Coprod(Vec<Type>),
}

enum Term {
    Var(Ident),

    Abs(Vec<(Ident, Type)>, Box<Term>),
    App(Vec<Term>),

    TAbs(Vec<Ident>, Box<Term>),
    TApp(Vec<Term>),

    Cat(Vec<Term>),
    Prj(Box<Term>, i32),

    Inj(Box<Term>, i32),
    Case(Box<Term>, Vec<Term>),
}
