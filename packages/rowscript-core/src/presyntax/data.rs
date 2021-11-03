use crate::basis::data::Ident;

type Label = Ident;

#[derive(Debug)]
pub enum Dir {
    L,
    R,
}

#[derive(Debug)]
pub struct Row {
    label: Label,
    typ: Type,
}

#[derive(Debug)]
pub enum Type {
    Var(Ident),
    Arr(Vec<Type>),
    Pi(Vec<Row>),
    Sigma(Vec<Row>),
    Row(Label, Box<Type>),

    Tuple(Vec<Type>),

    Unit,
    String,
    Number,
    Boolean,
    BigInt,
}

#[derive(Debug)]
pub enum Pred {
    Cont(Dir, Row, Row),
    Comb(Row, Row, Row),
}

#[derive(Debug)]
pub struct QualifiedType {
    pub preds: Vec<Pred>,
    pub typ: Type,
}

#[derive(Debug)]
pub struct Scheme {
    pub type_vars: Vec<Ident>,
    pub row_vars: Vec<Ident>,
    pub qualified: QualifiedType,
}

#[derive(Debug)]
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

    Unit,
}
