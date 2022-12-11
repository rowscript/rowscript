use crate::theory::abs::data::Term;
use crate::theory::abs::def::Body;
use crate::theory::abs::def::Sigma;
use crate::theory::abs::normalize::Normalizer;
use crate::theory::Var;

pub struct Unifier<'a> {
    sigma: &'a mut Sigma,
}

impl<'a> Unifier<'a> {
    pub fn new(sigma: &'a mut Sigma) -> Self {
        Self { sigma }
    }

    pub fn unify(&mut self, lhs: &Term, rhs: &Term) -> bool {
        use Term::*;
        match (lhs, rhs) {
            (MetaRef(v, _), rhs) => {
                self.solve(v, rhs);
                true
            }
            (lhs, MetaRef(v, _)) => {
                self.solve(v, lhs);
                true
            }

            (Let(p, a, b), Let(q, x, y)) => {
                self.unify(&p.typ, &q.typ) && self.unify(a, x) && self.unify(b, y)
            }
            (Pi(p, a), Pi(q, b)) => self.unify(&p.typ, &q.typ) && self.unify(a, b),
            (Lam(p, a), Lam(q, _)) => {
                let b = Normalizer::new(self.sigma)
                    .apply(Box::new(rhs.clone()), &[&Box::new(Ref(p.var.clone()))]);
                self.unify(&p.typ, &q.typ) && self.unify(a, &b)
            }
            (App(f, x), App(g, y)) => self.unify(f, g) && self.unify(x, y),
            (Sigma(p, a), Sigma(q, b)) => {
                let rho = &[(&q.var, &Box::new(Ref(p.var.clone())))];
                let b = Normalizer::new(self.sigma).with(rho, b.clone());
                self.unify(&p.typ, &q.typ) && self.unify(a, &b)
            }
            (Tuple(a, b), Tuple(x, y)) => self.unify(a, x) && self.unify(b, y),
            (TupleLet(p, q, a, b), TupleLet(r, s, x, y)) => {
                let rho = &[
                    (&r.var, &Box::new(Ref(p.var.clone()))),
                    (&s.var, &Box::new(Ref(q.var.clone()))),
                ];
                let y = Normalizer::new(self.sigma).with(rho, y.clone());
                self.unify(a, x) && self.unify(b, &y)
            }
            (UnitLet(a, b), UnitLet(x, y)) => self.unify(a, x) && self.unify(b, y),
            (If(a, b, c), If(x, y, z)) => self.unify(a, x) && self.unify(b, y) && self.unify(c, z),
            (Fields(a), Fields(b)) => todo!(),
            (Object(a), Object(b)) => self.unify(a, b),
            (Obj(a), Obj(b)) => self.unify(a, b),

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
            (Row, Row) => true,

            _ => false,
        }
    }

    fn solve(&mut self, meta_var: &Var, tm: &Term) -> bool {
        use Body::*;

        let def = self.sigma.get_mut(meta_var).unwrap();
        match &def.body {
            Meta(s) => {
                if let Some(_) = s {
                    return true;
                }
                def.body = Meta(Some(tm.clone()));
                true
            }
            _ => unreachable!(),
        }
    }
}
