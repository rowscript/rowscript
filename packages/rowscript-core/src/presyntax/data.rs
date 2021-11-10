use crate::basis::data::Ident;
use crate::presyntax::data::Scheme::Scm;
use std::collections::HashMap;
use tree_sitter::Point;

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
pub enum Scheme {
    Scm {
        type_vars: Vec<Ident>,
        row_vars: Vec<Ident>,
        qualified: QualifiedType,
    },

    /// Meta-variable for unifying type holes.
    Meta(Point),
}

impl Scheme {
    pub fn new_schemeless(typ: Type) -> Scheme {
        Scm {
            type_vars: vec![],
            row_vars: vec![],
            qualified: QualifiedType { preds: vec![], typ },
        }
    }
}

#[derive(Debug)]
pub enum Pred {
    Cont { d: Dir, lhs: Row, rhs: Row },
    Comb { lhs: Row, rhs: Row, result: Row },
}

#[derive(Debug)]
pub struct QualifiedType {
    pub preds: Vec<Pred>,
    pub typ: Type,
}

#[derive(Debug)]
pub enum Type {
    Var(Ident),
    Arrow(Vec<Type>),
    Record(Row),
    Variant(Row),
    Row(Label, Box<Type>),

    /// Sugar for empty records/tuples.
    Unit,
    Str,
    Num,
    Bool,
    BigInt,
    /// Array is not a sugar for anything, quite like an ad hoc type.
    Array(Box<Type>),
    /// Sugar for records.
    Tuple(Vec<Type>),
}

#[derive(Debug)]
pub enum Term {
    Var(Ident),

    Abs(Vec<Ident>, Box<Term>),
    App(Box<Term>, Box<Term>),

    Let(Ident, Scheme, Box<Term>, Box<Term>),

    Rec(Label, Box<Term>),
    Sel(Box<Term>, Label),

    Prj(Dir, Box<Term>),
    Cat(Vec<Term>),

    Inj(Dir, Box<Term>),
    Case(HashMap<Ident, Term>, Box<Option<Term>>),

    /// Type alias.
    TLet(Ident, Scheme, Box<Term>),
    /// Reference to primitives/builtins.
    PrimRef(Ident, Scheme),
    /// Constructor for units.
    Unit,
    /// Constructor for primitive `string`.
    Str(String),
    /// Constructor for primitive `number`.
    Num(String),
    /// Constructor for primitive `boolean`.
    Bool(bool),
    /// Constructor for primitive `bigint`.
    BigInt(String),
    /// Constructor for tuples.
    Tuple(Vec<Term>),
    /// Constructor for arrays.
    Array(Vec<Term>),
    /// Eliminator for booleans.
    If(Box<Term>, Box<Term>, Box<Term>),
    /// Eliminator for arrays/tuples.
    Subs(Box<Term>, Box<Term>),
}
