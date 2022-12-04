use crate::theory::abs::data::Term;
use crate::theory::abs::normalize::Normalizer;

pub fn unify(expected: &Term, inferred: &Term) -> bool {
    use Term::*;
    match (expected, inferred) {
        (Let(p, a, b), Let(q, x, y)) => unify(&p.typ, &q.typ) && unify(a, x) && unify(b, y),
        (Pi(p, a), Pi(q, b)) => unify(&p.typ, &q.typ) && unify(a, b),
        (Lam(p, a), Lam(q, _)) => {
            let b = Normalizer::apply(Box::new(inferred.clone()), &[&Box::new(Ref(p.var.clone()))]);
            unify(&p.typ, &q.typ) && unify(a, &b)
        }
        (App(f, x), App(g, y)) => unify(f, g) && unify(x, y),
        (Sigma(p, a), Sigma(q, b)) => {
            let rho = &[(&q.var, &Box::new(Ref(p.var.clone())))];
            let b = Normalizer::default().with(rho, b.clone());
            unify(&p.typ, &q.typ) && unify(a, &b)
        }
        (Tuple(a, b), Tuple(x, y)) => unify(a, x) && unify(b, y),
        (TupleLet(p, q, a, b), TupleLet(r, s, x, y)) => {
            let rho = &[
                (&r.var, &Box::new(Ref(p.var.clone()))),
                (&s.var, &Box::new(Ref(q.var.clone()))),
            ];
            let y = Normalizer::default().with(rho, y.clone());
            unify(a, x) && unify(b, &y)
        }
        (UnitLet(a, b), UnitLet(x, y)) => unify(a, x) && unify(b, y),
        (If(a, b, c), If(x, y, z)) => unify(a, x) && unify(b, y) && unify(c, z),

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
