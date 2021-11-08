use crate::basis::data::Ident;
use crate::presyntax::data::Scheme::Scm;
use tree_sitter::{Node, Point};

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
    Case(Vec<Term>),

    Unit,
    Str(String),
    Num(String),
    Bool(bool),
    BigInt(String),
    /// Eliminator for booleans.
    If(Box<Term>, Box<Term>, Box<Term>),
    /// Eliminator for arrays.
    Subs(Box<Term>, Box<Term>),
    /// Type alias.
    TLet(Ident, Scheme, Box<Term>),
    /// Constructor for tuples.
    Tuple(Vec<Term>),
    /// Reference to primitives.
    PrimRef {
        src: Ident,
        dst: PrimName,
        typ: Scheme,
    },
}

#[derive(Debug)]
pub struct PrimName(&'static str);

const PRIM_ADD: PrimName = PrimName("primAdd");
const PRIM_SUB: PrimName = PrimName("primSub");
const PRIM_BNOT: PrimName = PrimName("primBNot");
const PRIM_NOT: PrimName = PrimName("primNot");

const PRIM_EXP: PrimName = PrimName("primExp");
const PRIM_TIME: PrimName = PrimName("primTime");
const PRIM_DIV: PrimName = PrimName("primDiv");
const PRIM_MOD: PrimName = PrimName("primMod");
const PRIM_RSHIFT: PrimName = PrimName("primRShift");
const PRIM_URSHIFT: PrimName = PrimName("primURShift");
const PRIM_LSHIFT: PrimName = PrimName("primLShift");
const PRIM_LT: PrimName = PrimName("primLt");
const PRIM_LE: PrimName = PrimName("primLe");
const PRIM_EQ: PrimName = PrimName("primEq");
const PRIM_NE: PrimName = PrimName("primNe");
const PRIM_GE: PrimName = PrimName("primGe");
const PRIM_GT: PrimName = PrimName("primGt");
const PRIM_AND: PrimName = PrimName("primAnd");
const PRIM_BAND: PrimName = PrimName("primBAnd");
const PRIM_OR: PrimName = PrimName("primOr");
const PRIM_BOR: PrimName = PrimName("primBOr");
const PRIM_XOR: PrimName = PrimName("primXor");

impl From<Node<'_>> for PrimName {
    fn from(n: Node) -> Self {
        match n.kind() {
            "+" => PRIM_ADD,
            "-" => PRIM_SUB,
            "~" => PRIM_BNOT,
            "!" => PRIM_NOT,

            "**" => PRIM_EXP,
            "*" => PRIM_TIME,
            "/" => PRIM_DIV,
            "%" => PRIM_MOD,
            ">>" => PRIM_RSHIFT,
            ">>>" => PRIM_URSHIFT,
            "<<" => PRIM_LSHIFT,
            "<" => PRIM_LT,
            "<=" => PRIM_LE,
            "==" => PRIM_EQ,
            "!=" => PRIM_NE,
            ">=" => PRIM_GE,
            ">" => PRIM_GT,
            "&&" => PRIM_AND,
            "&" => PRIM_BAND,
            "||" => PRIM_OR,
            "|" => PRIM_BOR,
            "^" => PRIM_XOR,

            _ => unreachable!(),
        }
    }
}
