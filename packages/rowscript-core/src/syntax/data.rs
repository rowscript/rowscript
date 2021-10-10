use crate::basis::data::Ident;

enum Type {
    Var(Ident),
    Arr(Vec<Type>),
    Forall(Ident, Type),
    Prod(Vec<Type>),
    Coprod(Vec<Type>),
}

enum Term {
    Var(Ident),

    Abs(Vec<(Ident, Type)>, Term),
    App(Vec<Term>),

    TAbs(Vec<Ident>, Term),
    TApp(Vec<Term>),

    Cat(Vec<Term>),
    Prj(Term, i32),

    Inj(Term, i32),
    Case(Term, Vec<Term>),
}
