use std::collections::HashMap;
use std::fmt::{write, Formatter};
use std::path::Display;
use std::process::id;

use tree_sitter::Point;

use crate::basis::data::Ident;
use crate::presyntax::data::Row::Var;
use crate::presyntax::data::Scheme::Scm;

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

    /// Unlike ROSE, we use identifiers as labels to form a variant value. So we
    /// don't need multiple `Dir`s to reference the correct row type.
    Inj(Ident, Box<Term>),
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

struct IterFmt<Iter> {
    iter: Iter,
}

struct PairFmt<X, Y> {
    pair: (X, Y),
}

struct OptionFmt<'a, T> {
    option: &'a Option<T>,
}

impl<'a, T, U> std::fmt::Display for IterFmt<U>
where
    T: std::fmt::Display,
    U: std::iter::Iterator<Item = T> + Clone,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str("'(")
            .and_then(|_| {
                let mut iter = self.iter.clone();
                if let Some(x) = iter.next() {
                    write!(f, "{}", x)?;
                }
                while let Some(x) = iter.next() {
                    write!(f, " {}", x)?;
                }
                Ok(())
            })
            .and_then(|_| f.write_str(")"))
    }
}

impl<X, Y> std::fmt::Display for PairFmt<X, Y>
where
    X: std::fmt::Display,
    Y: std::fmt::Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "'({} {})", self.pair.0, self.pair.1)
    }
}

impl<'a, T> std::fmt::Display for OptionFmt<'a, T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.option {
            None => write!(f, "'()"),
            Some(x) => write!(f, "'({})", x),
        }
    }
}

impl std::fmt::Display for Dir {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Dir::L => write!(f, "L"),
            Dir::R => write!(f, "R"),
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Var(ident) => write!(f, "(type/var {})", ident),
            Type::Arrow(types) => write!(f, "(type/arrow {})", IterFmt { iter: types.iter() }),
            Type::Record(row) => write!(f, "(type/record {})", row),
            Type::Variant(row) => write!(f, "(type/variant {})", row),
            Type::Row(label, t) => write!(f, "(type/row {} {})", label, t),
            Type::Unit => write!(f, "(type/unit)"),
            Type::Str => write!(f, "(type/str)"),
            Type::Num => write!(f, "(type/num)"),
            Type::Bool => write!(f, "(type/bool)"),
            Type::BigInt => write!(f, "(type/bigint)"),
            Type::Array(inner) => write!(f, "(type/array {})", inner),
            Type::Tuple(list) => write!(f, "(type/tuple {})", IterFmt { iter: list.iter() }),
        }
    }
}

impl std::fmt::Display for Row {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Row::Var(ident) => write!(f, "(row/var {})", ident),
            Row::Labeled(label) => write!(
                f,
                "(row/labeled {})",
                IterFmt {
                    iter: label.iter().map(|x| PairFmt { pair: (&x.0, &x.1) })
                }
            ),
        }
    }
}

impl std::fmt::Display for Pred {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Pred::Cont { d, lhs, rhs } => write!(f, "(pred/cont {} {} {})", d, lhs, rhs),
            Pred::Comb { lhs, rhs, result } => write!(f, "(pred/comb {} {} {})", lhs, rhs, result),
        }
    }
}

impl std::fmt::Display for QualifiedType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(qualified-type {} {})",
            IterFmt {
                iter: self.preds.iter()
            },
            self.typ
        )
    }
}

impl std::fmt::Display for Scheme {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Scheme::Scm {
                type_vars,
                row_vars,
                qualified,
            } => write!(
                f,
                "(scheme/scm {} {} {})",
                IterFmt {
                    iter: type_vars.iter()
                },
                IterFmt {
                    iter: row_vars.iter()
                },
                qualified
            ),
            Scheme::Meta(point) => write!(f, "(scheme/meta {} {})", point.row, point.column),
        }
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Term::*;
        match self {
            Var(ident) => write!(f, "(term/var {})", ident),
            Abs(args, body) => write!(f, "(term/abs {} {})", IterFmt { iter: args.iter() }, body),
            App(func, term) => write!(f, "(term/app {} {})", func, term),
            Let(x, t, val, body) => write!(f, "(term/let {} {} {} {})", x, t, val, body),
            Rec(label, term) => write!(f, "(term/rec {} {})", label, term),
            Sel(term, label) => write!(f, "(term/sel {} {})", term, label),
            Prj(dir, label) => write!(f, "(term/prj {} {})", dir, label),
            Cat(terms) => write!(f, "(term/cat {})", IterFmt { iter: terms.iter() }),
            Inj(ident, term) => write!(f, "(term/inj {} {})", ident, term),
            Case(map, x) => write!(
                f,
                "(term/case {} {})",
                IterFmt {
                    iter: map.iter().map(|x| PairFmt { pair: x })
                },
                OptionFmt { option: x }
            ),
            TLet(ident, scheme, term) => write!(f, "(term/tlet {} {} {})", ident, scheme, term),
            PrimRef(ident, scheme) => write!(f, "(term/prim-ref {} {})", ident, scheme),
            Unit => write!(f, "(term/unit)"),
            Str(data) => write!(f, "(term/str {:?})", data),
            Num(data) => write!(f, "(term/num {:?})", data),
            Bool(data) => write!(f, "(term/bool {})", data),
            BigInt(data) => write!(f, "(term/bigint {})", data),
            Tuple(data) => write!(f, "(term/tuple {})", IterFmt { iter: data.iter() }),
            Array(data) => write!(f, "(term/array {})", IterFmt { iter: data.iter() }),
            If(cond, then, otherwise) => write!(f, "(term/if {} {} {})", cond, then, otherwise),
            Subs(left, right) => write!(f, "(term/subs {} {})", left, right),
        }
    }
}
