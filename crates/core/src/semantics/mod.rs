pub(crate) mod builtin;
pub(crate) mod check;
pub(crate) mod jit;
pub(crate) mod vm;

use rowscript_derive::Ops;
use std::collections::HashMap;
use std::fmt::{Display, Formatter, Result as FmtResult};
use strum::{Display, EnumString};
use ustr::UstrMap;

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

#[derive(Debug, Clone, Display)]
pub enum Type {
    #[strum(transparent)]
    Builtin(BuiltinType),
    #[strum(transparent)]
    Function(Box<FuncType>),
    #[strum(to_string = "&{0}")]
    Ref(Box<Self>),
    #[strum(to_string = "struct {0}")]
    Struct(Id),
}

impl Type {
    fn main() -> Self {
        Self::Function(Box::new(FuncType {
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
            Type::Struct(id) => Expr::StructType(id.clone()),
            _ => unreachable!(),
        }
    }
}

impl Default for Type {
    fn default() -> Self {
        Self::Builtin(Default::default())
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
    USize,
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
            BuiltinType::USize => usize::try_from(n).ok().map(Integer::USize),
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
    USize(usize),
    U64(u64),
}

#[derive(Debug, Clone, Ops)]
pub enum Float {
    F32(f32),
    F64(f64),
}

#[derive(Debug, Clone)]
pub struct FuncType {
    params: Vec<Type>,
    ret: Type,
}

impl Display for FuncType {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write_delimited!(f, "(", self.params, ", ", ")");
        write!(f, " -> {}", self.ret)
    }
}

#[derive(Debug)]
pub(crate) struct Func {
    pub(crate) typ: FuncType,
    pub(crate) body: Vec<Spanned<Stmt>>,
}

#[derive(Debug)]
pub(crate) struct Static {
    #[allow(dead_code)]
    pub(crate) typ: Type,
    pub(crate) expr: Spanned<Expr>,
}

#[derive(Default, Debug)]
pub(crate) struct Struct {
    pub(crate) members: UstrMap<(usize, Type)>,
    pub(crate) extends: UstrMap<(usize, FuncType)>,
    pub(crate) bodies: Vec<Vec<Spanned<Stmt>>>,
}

#[derive(Default, Debug)]
pub(crate) struct Globals {
    pub(crate) fns: HashMap<Id, Spanned<Func>>,
    pub(crate) statics: HashMap<Id, Spanned<Static>>,
    pub(crate) structs: HashMap<Id, Struct>,
}
