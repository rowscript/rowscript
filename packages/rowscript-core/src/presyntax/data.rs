use crate::basis::data::Ident;

type Label = Ident;

#[derive(Debug)]
pub enum Dir {
    L,
    R,
}

#[derive(Debug)]
pub struct Row {
    pub label: Label,
    pub typ: Type,
}

#[derive(Debug)]
pub enum Type {
    Var(Ident),
    Arrow(Vec<Type>),
    Record(Vec<Row>, bool),
    Variant(Vec<Row>, bool),
    Row(Label, Box<Type>),

    Array(Box<Type>),

    /// Sugar for records.
    Tuple(Vec<Type>),

    /// Sugar for empty records/tuples.
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
