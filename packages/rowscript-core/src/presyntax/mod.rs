use crate::basis::data::Ident;
use crate::presyntax::Term::Var;
use tree_sitter::Tree;

type Label = Ident;

pub enum Dir {
    L,
    R,
}

pub struct Row {
    label: Label,
    typ: Type,
}

pub enum Type {
    Var(Ident),
    Arr(Vec<Type>),
    Pi(Vec<Row>),
    Sigma(Vec<Row>),
    Row(Label, Box<Type>),
}

pub enum Pred {
    Cont(Dir, Row, Row),
    Comb(Row, Row, Row),
}

pub struct QualifiedType {
    preds: Vec<Pred>,
    typ: Type,
}

pub struct Scheme {
    type_vars: Vec<Ident>,
    row_vars: Vec<Ident>,
    qualified: QualifiedType,
}

pub enum Term {
    Var(Ident),

    Abs(Vec<Ident>, Box<Term>),
    App(Vec<Term>),

    Let(Ident, Scheme, Box<Term>, Box<Term>),

    Rec(Label, Box<Term>),
    Sel(Box<Term>, Label),

    Prj(Dir, Box<Term>),
    Cat(Vec<Term>),

    Inj(Dir, Box<Term>),
    Case(Vec<Term>),
}

impl Term {
    pub fn new(_tree: Tree) -> Term {
        Var(Ident {
            pt: Default::default(),
            text: "lolwtf".into(),
        })
    }
}
