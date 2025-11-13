pub(crate) mod builtin;
pub(crate) mod check;
pub(crate) mod jit;
pub(crate) mod vm;

use std::collections::HashMap;
use std::fmt::{Display, Formatter, Result as FmtResult};
use strum::{Display, EnumString};

use crate::Spanned;
use crate::syntax::{Id, Stmt};

macro_rules! write_separated {
    ($f:ident, $items:expr, $sep:literal) => {
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
    ($f:ident, $lhs:literal, $items:expr, $sep:literal, $rhs:literal) => {
        write!($f, $lhs)?;
        write_separated!($f, $items, $sep);
        write!($f, $rhs)?;
    };
}

#[derive(Debug, Clone)]
pub(crate) enum Type {
    Builtin(BuiltinType),
    Function(Box<FunctionType>),
    Ptr(Box<Self>),
}

impl Type {
    fn main() -> Self {
        Self::Function(Box::new(FunctionType {
            params: Default::default(),
            ret: Self::Builtin(BuiltinType::Unit),
        }))
    }
}

impl Default for Type {
    fn default() -> Self {
        Self::Builtin(Default::default())
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::Builtin(t) => write!(f, "{t}"),
            Self::Function(t) => write!(f, "{t}"),
            Self::Ptr(t) => write!(f, "*{t}"),
        }
    }
}

#[derive(Default, Debug, Eq, PartialEq, Copy, Clone, EnumString, Display)]
#[strum(serialize_all = "lowercase")]
pub enum BuiltinType {
    Type,
    #[default]
    Unit,
    Bool,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Str,
}

impl BuiltinType {
    pub(crate) fn is_number(&self) -> bool {
        matches!(
            self,
            Self::I8
                | Self::I16
                | Self::I32
                | Self::I64
                | Self::U8
                | Self::U16
                | Self::U32
                | Self::U64
                | Self::F32
                | Self::F64
        )
    }
}

#[derive(Default, Debug, Clone)]
pub(crate) struct FunctionType {
    params: Box<[Type]>,
    ret: Type,
}

impl Display for FunctionType {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write_delimited!(f, "(", self.params, ",", ")");
        write!(f, " -> {}", self.ret)
    }
}

#[derive(Default, Debug)]
pub(crate) struct Func {
    pub(crate) typ: FunctionType,
    pub(crate) body: Box<[Spanned<Stmt>]>,
}

pub(crate) type Functions = HashMap<Id, Spanned<Func>>;
