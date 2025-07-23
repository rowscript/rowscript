use crate::syntax::Name;

#[derive(Debug)]
pub(crate) enum IR {
    Name(Name),

    BuiltinType(BuiltinType),
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
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
