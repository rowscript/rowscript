use crate::base::{LocalVar, Param};

pub enum Dir {
    Left,
    Right,
}

pub enum Term {
    Ref(LocalVar),
    Let(Param<Term>, Term, Term),

    Univ,

    Fn(Param<Term>, Term),
    Lam(Param<Term>, Term),
    App(Term, Term),

    RowConcatEq(Term, Term, Term),
    RowRefl,

    RowCont(Dir, Term, Term),
    RowSat,

    Row(Vec<(String, Term)>),
    Label(String, Term),
    Unlabel(Term, String),

    Record(Term),
    Prj(Dir, Term),
    Concat(Term, Term),

    Variant(Term),
    Inj(Dir, Term),
    Branch(Term, Term),
}

pub const U: Term = Term::Univ;
