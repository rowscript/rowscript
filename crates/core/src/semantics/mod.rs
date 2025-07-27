use std::fmt::{Display, Formatter};

use ustr::Ustr;

use crate::syntax::parse::Sym;
use crate::syntax::{BuiltinType, Name};

pub(crate) mod check;
mod vm;

#[derive(Clone)]
enum Type {
    BuiltinType(BuiltinType),
    FunctionType(Box<[Self]>, Box<Self>),
}

macro_rules! write_separated {
    ($f:ident, $items:ident, $sep:literal) => {
        let mut it = $items.iter();
        if let Some(first) = it.next() {
            write!($f, "{first}")?;
        }
        for item in it {
            write!($f, $sep)?;
            write!($f, "{item}")?;
        }
    };
}

macro_rules! write_delimited {
    ($f:ident, $lhs:literal, $items:ident, $sep:literal, $rhs:literal) => {
        write!($f, $lhs)?;
        write_separated!($f, $items, $sep);
        write!($f, $rhs)?;
    };
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::BuiltinType(t) => write!(f, "{t}"),
            Type::FunctionType(params, ret) => {
                write_delimited!(f, "(", params, ",", ")");
                write!(f, " -> {ret}")
            }
        }
    }
}

#[derive(Clone)]
enum Value {
    Global(Name),
    Local(usize),

    BuiltinType(BuiltinType),
    Unit,
    Boolean(bool),
    Number(f64),
    String(Ustr),
}

enum IR {
    Load(usize, Value),
    Call(Value, Box<[Value]>),
    BinaryOp(Value, Sym, Value),
    Return,
    If {
        then: (Value, Box<[Self]>),
        elif: Box<[(Value, Box<[Self]>)]>,
        els: Option<Box<[Self]>>,
    },
}
