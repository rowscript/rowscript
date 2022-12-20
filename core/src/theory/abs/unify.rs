use crate::theory::abs::data::{FieldMap, Term};
use crate::theory::abs::def::Body;
use crate::theory::abs::def::Sigma;
use crate::theory::abs::normalize::Normalizer;
use crate::theory::{Loc, Var};
use crate::Error;
use crate::Error::NonUnifiable;

pub struct Unifier<'a> {
    sigma: &'a mut Sigma,
}

impl<'a> Unifier<'a> {
    pub fn new(sigma: &'a mut Sigma) -> Self {
        Self { sigma }
    }

    pub fn unify(&mut self, loc: Loc, lhs: &Term, rhs: &Term) -> Result<(), Error> {
        use Term::*;

        fn unify_err(loc: Loc, lhs: &Term, rhs: &Term) -> Result<(), Error> {
            Err(NonUnifiable(
                Box::new(lhs.clone()),
                Box::new(rhs.clone()),
                loc,
            ))
        }

        match (lhs, rhs) {
            (MetaRef(v, _), rhs) => {
                self.solve(v, rhs);
                Ok(())
            }
            (lhs, MetaRef(v, _)) => {
                self.solve(v, lhs);
                Ok(())
            }

            (Let(p, a, b), Let(q, x, y)) => {
                self.unify(loc, &p.typ, &q.typ)?;
                self.unify(loc, a, x)?;
                self.unify(loc, b, y)
            }
            (Pi(p, a), Pi(q, b)) => {
                self.unify(loc, &p.typ, &q.typ)?;
                self.unify(loc, a, b)
            }
            (Lam(p, a), Lam(q, _)) => {
                let b = Normalizer::new(self.sigma)
                    .apply(Box::new(rhs.clone()), &[&Box::new(Ref(p.var.clone()))])?;
                self.unify(loc, &p.typ, &q.typ)?;
                self.unify(loc, a, &b)
            }
            (App(f, x), App(g, y)) => {
                self.unify(loc, f, g)?;
                self.unify(loc, x, y)
            }
            (Sigma(p, a), Sigma(q, b)) => {
                let rho = &[(&q.var, &Box::new(Ref(p.var.clone())))];
                let b = Normalizer::new(self.sigma).with(rho, b.clone())?;
                self.unify(loc, &p.typ, &q.typ)?;
                self.unify(loc, a, &b)
            }
            (Tuple(a, b), Tuple(x, y)) => {
                self.unify(loc, a, x)?;
                self.unify(loc, b, y)
            }
            (TupleLet(p, q, a, b), TupleLet(r, s, x, y)) => {
                let rho = &[
                    (&r.var, &Box::new(Ref(p.var.clone()))),
                    (&s.var, &Box::new(Ref(q.var.clone()))),
                ];
                let y = Normalizer::new(self.sigma).with(rho, y.clone())?;
                self.unify(loc, a, x)?;
                self.unify(loc, b, &y)
            }
            (UnitLet(a, b), UnitLet(x, y)) => {
                self.unify(loc, a, x)?;
                self.unify(loc, b, y)
            }
            (If(a, b, c), If(x, y, z)) => {
                self.unify(loc, a, x)?;
                self.unify(loc, b, y)?;
                self.unify(loc, c, z)
            }
            (Fields(a), Fields(b)) if a.len() == b.len() => {
                for (n, x) in a {
                    if let Some(y) = b.get(n) {
                        self.unify(loc, x, y)?;
                    } else {
                        return unify_err(loc, lhs, rhs);
                    }
                }
                Ok(())
            }
            (Object(a), Object(b)) => self.unify(loc, a, b),
            (Obj(a), Obj(b)) => self.unify(loc, a, b),

            (Ref(a), Ref(b)) if a == b => Ok(()),
            (Str(a), Str(b)) if a == b => Ok(()),
            (Num(_, a), Num(_, b)) if a == b => Ok(()),
            (Big(a), Big(b)) if a == b => Ok(()),

            (Univ, Univ) => Ok(()),
            (Unit, Unit) => Ok(()),
            (TT, TT) => Ok(()),
            (Boolean, Boolean) => Ok(()),
            (False, False) => Ok(()),
            (True, True) => Ok(()),
            (String, String) => Ok(()),
            (Number, Number) => Ok(()),
            (BigInt, BigInt) => Ok(()),
            (Row, Row) => Ok(()),

            _ => unify_err(loc, lhs, rhs),
        }
    }

    fn solve(&mut self, meta_var: &Var, tm: &Term) {
        use Body::*;

        let def = self.sigma.get_mut(meta_var).unwrap();
        match &def.body {
            Meta(s) => {
                if let Some(_) = s {
                    return;
                }
                def.body = Meta(Some(tm.clone()));
            }
            _ => unreachable!(),
        }
    }

    fn fields_contains(&mut self, bigger: &FieldMap, smaller: &FieldMap) -> Result<(), Error> {
        todo!()
    }
}
