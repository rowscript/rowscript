use crate::theory::abs::data::Term;
use crate::theory::abs::data::Term::Ref;
use crate::theory::Loc;
use crate::Error;
use crate::Error::NonUnifiable;

pub fn unify(loc: Loc, expected: Box<Term>, inferred: Box<Term>) -> Result<(), Error> {
    match (&*expected, &*inferred) {
        (Ref(x), Ref(y)) => {
            if x == y {
                Ok(())
            } else {
                Err(NonUnifiable(loc, expected, inferred))
            }
        }
        _ => unreachable!(),
    }
}
