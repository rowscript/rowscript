use crate::basis::data::Ident;

type Label = Ident;

#[derive(Debug)]
pub enum Dir {
    L,
    R,
}

#[derive(Debug)]
pub enum Row {
    Var(Ident),
    Labeled(Vec<(Label, Type)>),
}

#[derive(Debug)]
pub enum Type {
    Var(Ident),
    Arrow(Vec<Type>),
    Record(Row),
    Variant(Row),
    Row(Label, Box<Type>),

    Array(Box<Type>),

    /// Sugar for records.
    Tuple(Vec<Type>),

    /// Sugar for empty records/tuples.
    Unit,

    Str,
    Num,
    Bool,
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

impl Scheme {
    pub fn new_schemeless(typ: Type) -> Scheme {
        Scheme {
            type_vars: vec![],
            row_vars: vec![],
            qualified: QualifiedType { preds: vec![], typ },
        }
    }
}

#[derive(Debug)]
pub enum Term {
    Var(Ident),

    Abs(Vec<Ident>, Box<Term>),
    App(Vec<Term>),

    Let(Ident, Option<Scheme>, Box<Term>, Box<Term>),

    Rec(Label, Box<Term>),
    Sel(Box<Term>, Label),

    Prj(Dir, Box<Term>),
    Cat(Vec<Term>),

    Inj(Dir, Box<Term>),
    Case(Vec<Term>),

    Unit,
    Str(String),
    Num(String),
    Bool(bool),
    BigInt(String),

    /// Eliminator for booleans.
    If(Box<Term>, Box<Term>, Box<Term>),
}
