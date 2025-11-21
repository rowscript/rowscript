pub(crate) mod builtin;
pub(crate) mod check;
pub(crate) mod jit;
pub(crate) mod vm;

use std::collections::HashMap;
use std::fmt::{Display, Formatter, Result as FmtResult};
use strum::{Display, EnumString};

use rowscript_derive::Ops;

use crate::syntax::{Expr, Id, Stmt};
use crate::{Span, Spanned};

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
pub enum Type {
    Builtin(BuiltinType),
    Function(Box<FunctionType>),
    Ref(Box<Self>),
}

impl Type {
    fn main() -> Self {
        Self::Function(Box::new(FunctionType {
            params: Default::default(),
            ret: Self::Builtin(BuiltinType::Unit),
        }))
    }

    fn to_expr(&self, span: Span) -> Expr {
        match self {
            Type::Builtin(t) => Expr::BuiltinType(*t),
            Type::Ref(t) => Expr::RefType(Box::new(Spanned {
                span,
                item: t.to_expr(span),
            })),
            _ => unreachable!(),
        }
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
            Self::Ref(t) => write!(f, "&{t}"),
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
    fn narrow_integer(&self, n: i64) -> Option<Integer> {
        match self {
            BuiltinType::I8 => i8::try_from(n).ok().map(Integer::I8),
            BuiltinType::I16 => i16::try_from(n).ok().map(Integer::I16),
            BuiltinType::I32 => i32::try_from(n).ok().map(Integer::I32),
            BuiltinType::I64 => Some(Integer::I64(n)),
            BuiltinType::U8 => u8::try_from(n).ok().map(Integer::U8),
            BuiltinType::U16 => u16::try_from(n).ok().map(Integer::U16),
            BuiltinType::U32 => u32::try_from(n).ok().map(Integer::U32),
            BuiltinType::U64 => u64::try_from(n).ok().map(Integer::U64),
            _ => unreachable!(),
        }
    }

    fn narrow_float(&self, n: f64) -> Float {
        match self {
            BuiltinType::F32 => Float::F32(n as _),
            BuiltinType::F64 => Float::F64(n),
            _ => unreachable!(),
        }
    }

    fn is_integer(&self) -> bool {
        self.is_signed_integer() || self.is_unsigned_integer()
    }

    fn is_signed_integer(&self) -> bool {
        matches!(self, Self::I8 | Self::I16 | Self::I32 | Self::I64)
    }

    fn is_unsigned_integer(&self) -> bool {
        matches!(self, Self::U8 | Self::U16 | Self::U32 | Self::U64)
    }

    fn is_float(&self) -> bool {
        matches!(self, Self::F32 | Self::F64)
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Ops)]
pub enum Integer {
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
}

#[derive(Debug, Clone, Ops)]
pub enum Float {
    F32(f32),
    F64(f64),
}

#[derive(Default, Debug, Clone)]
pub struct FunctionType {
    params: Box<[Type]>,
    ret: Type,
}

impl Display for FunctionType {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write_delimited!(f, "(", self.params, ", ", ")");
        write!(f, " -> {}", self.ret)
    }
}

#[derive(Default, Debug)]
pub(crate) struct Func {
    pub(crate) typ: FunctionType,
    pub(crate) body: Box<[Spanned<Stmt>]>,
}

pub(crate) type Functions = HashMap<Id, Spanned<Func>>;
