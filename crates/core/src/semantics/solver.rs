use crate::semantics::Type;
use crate::{Error, Out, Span};

pub(crate) fn isa(span: Span, got: &Type, want: &Type) -> Out<()> {
    match (got, want) {
        (Type::BuiltinType(a), Type::BuiltinType(b)) if a == b => Ok(()),
        (Type::FunctionType(xs, x), Type::FunctionType(ys, y)) if xs.len() == ys.len() => {
            xs.iter()
                .zip(ys.iter())
                .try_for_each(|(a, b)| isa(span, a, b))?;
            isa(span, x, y)
        }
        _ => {
            let got = got.to_string();
            let want = want.to_string();
            Err(Error::TypeMismatch { span, got, want })
        }
    }
}
