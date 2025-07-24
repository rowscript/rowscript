use strum::{Display, EnumString};

use crate::syntax::Name;

mod checker;

#[derive(Debug)]
pub(crate) enum IR {
    Name(Name),

    BuiltinType(BuiltinType),
}

#[derive(Debug, Eq, PartialEq, Copy, Clone, EnumString, Display)]
#[strum(serialize_all = "lowercase")]
pub(crate) enum BuiltinType {
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

#[derive(Debug, Eq, PartialEq, Copy, Clone, Display)]
pub(crate) enum Op {
    #[strum(serialize = ":=")]
    Assign,
    #[strum(serialize = "==")]
    EqEq,
}
