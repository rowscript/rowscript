use crate::theory::abs::data::Term;

pub fn unify(expected: &Term, inferred: &Term) -> bool {
    use Term::*;
    match (expected, inferred) {
        (Let(p, a, b), Let(q, x, y)) => unify(&p.typ, &q.typ) && unify(a, x) && unify(b, y),
        (Pi(p, a), Pi(q, b)) => unify(&p.typ, &q.typ) && unify(a, b),

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
    }
}
