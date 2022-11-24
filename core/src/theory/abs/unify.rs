use crate::theory::abs::data::Term;
use crate::theory::Loc;
use crate::Error;
use crate::Error::NonUnifiable;

pub fn unify(loc: Loc, expected: Box<Term>, inferred: Box<Term>) -> Result<(), Error> {
    use Term::*;
    if match (&*expected, &*inferred) {
        (Ref(a), Ref(b)) => a == b,
        (Str(a), Str(b)) => a == b,
        (Num(_, a), Num(_, b)) => a == b,
        (Big(a), Big(b)) => a == b,

        (Univ, Univ) => true,
        (Unit, Unit) => true,
        (TT, TT) => true,
        (Boolean, Boolean) => true,
        (False, False) => true,
        (True, True) => true,
        (String, String) => true,
        (Number, Number) => true,
        (BigInt, BigInt) => true,

        _ => false,
    } {
        Ok(())
    } else {
        Err(NonUnifiable(loc, expected, inferred))
    }
}
