use std::collections::HashMap;
use std::fmt::{Display, Formatter};

use crate::Spanned;
use crate::syntax::{BuiltinType, Id, Stmt};

pub(crate) mod check;
mod jit;
pub(crate) mod vm;

#[derive(Clone)]
pub(crate) enum Type {
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

#[derive(Default)]
pub(crate) struct Func {
    pub(crate) params: Box<[Type]>,
    pub(crate) body: Box<[Spanned<Stmt>]>,
}

pub(crate) type Functions = HashMap<Id, Func>;
