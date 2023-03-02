use crate::theory::abs::data::Term;
use crate::theory::abs::def::Body;
use crate::theory::abs::def::Sigma;
use crate::theory::abs::normalize::Normalizer;
use crate::theory::{Loc, Var};
use crate::Error;
use crate::Error::{NonRowSat, NonUnifiable};

pub struct Unifier<'a> {
    sigma: &'a mut Sigma,
    loc: Loc,
}

impl<'a> Unifier<'a> {
    pub fn new(sigma: &'a mut Sigma, loc: Loc) -> Self {
        Self { sigma, loc }
    }

    fn unify_err(&self, lhs: &Term, rhs: &Term) -> Result<(), Error> {
        Err(NonUnifiable(
            Box::new(lhs.clone()),
            Box::new(rhs.clone()),
            self.loc,
        ))
    }

    pub fn unify(&mut self, lhs: &Term, rhs: &Term) -> Result<(), Error> {
        use Term::*;

        match (lhs, rhs) {
            (MetaRef(v, _), rhs) => {
                self.solve(v, rhs);
                Ok(())
            }
            (lhs, MetaRef(v, _)) => {
                self.solve(v, lhs);
                Ok(())
            }

            // A constraint is a subtype of universe.
            (Univ, InterfaceRef(_)) => Ok(()),

            (Let(p, a, b), Let(q, x, y)) => {
                self.unify(&p.typ, &q.typ)?;
                self.unify(a, x)?;
                self.unify(b, y)
            }
            (Pi(p, a), Pi(q, b)) => {
                self.unify(&p.typ, &q.typ)?;
                let rho = &[(&q.var, &Box::new(Ref(p.var.clone())))];
                let b = Normalizer::new(self.sigma, self.loc).with(rho, b.clone())?;
                self.unify(a, &b)
            }
            (Lam(p, a), Lam(_, _)) => {
                let b = Normalizer::new(self.sigma, self.loc)
                    .apply(Box::new(rhs.clone()), &[Box::new(Ref(p.var.clone()))])?;
                self.unify(a, &b)
            }
            (App(f, x), App(g, y)) => {
                self.unify(f, g)?;
                self.unify(x, y)
            }
            (Sigma(p, a), Sigma(q, b)) => {
                self.unify(&p.typ, &q.typ)?;
                let rho = &[(&q.var, &Box::new(Ref(p.var.clone())))];
                let b = Normalizer::new(self.sigma, self.loc).with(rho, b.clone())?;
                self.unify(a, &b)
            }
            (Tuple(a, b), Tuple(x, y)) => {
                self.unify(a, x)?;
                self.unify(b, y)
            }
            (TupleLet(p, q, a, b), TupleLet(r, s, x, y)) => {
                let rho = &[
                    (&r.var, &Box::new(Ref(p.var.clone()))),
                    (&s.var, &Box::new(Ref(q.var.clone()))),
                ];
                let y = Normalizer::new(self.sigma, self.loc).with(rho, y.clone())?;
                self.unify(a, x)?;
                self.unify(b, &y)
            }
            (UnitLet(a, b), UnitLet(x, y)) => {
                self.unify(a, x)?;
                self.unify(b, y)
            }
            (If(a, b, c), If(x, y, z)) => {
                self.unify(a, x)?;
                self.unify(b, y)?;
                self.unify(c, z)
            }
            (Fields(_), Fields(_)) => self.unify_fields_eq(lhs, rhs),
            (Object(a), Object(b)) => self.unify(a, b),
            (Obj(a), Obj(b)) => self.unify(a, b),
            (Enum(a), Enum(b)) => self.unify(a, b),
            (Variant(a), Variant(b)) => self.unify(a, b),

            (Ref(a), Ref(b)) if a == b => Ok(()),
            (Str(a), Str(b)) if a == b => Ok(()),
            (Num(_, a), Num(_, b)) if a == b => Ok(()),
            (Big(a), Big(b)) if a == b => Ok(()),
            (Vptr(a), Vptr(b)) if a == b => Ok(()),
            (InterfaceRef(a), InterfaceRef(b)) if a == b => Ok(()),

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

            _ => self.unify_err(lhs, rhs),
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
                // FIXME: A solution `T` of type `type` is inserted with the interface constraint,
                // which is illegal due to the subtyping rule.
                def.body = Meta(Some(tm.clone()));
            }
            _ => unreachable!(),
        }
    }

    pub fn unify_fields_ord(&mut self, smaller: &Term, bigger: &Term) -> Result<(), Error> {
        use Term::*;

        match (smaller, bigger) {
            (Fields(f), Fields(g)) => {
                for (x, a) in f {
                    if let Some(b) = g.get(x) {
                        self.unify(a, b)?;
                        continue;
                    }
                    return Err(NonRowSat(
                        Box::new(smaller.clone()),
                        Box::new(bigger.clone()),
                        self.loc,
                    ));
                }
                Ok(())
            }
            _ => unreachable!(),
        }
    }

    pub fn unify_fields_eq(&mut self, lhs: &Term, rhs: &Term) -> Result<(), Error> {
        use Term::*;

        match (lhs, rhs) {
            (Fields(a), Fields(b)) => {
                if a.len() != b.len() {
                    return self.unify_err(lhs, rhs);
                }
                for (n, x) in a {
                    if let Some(y) = b.get(n) {
                        self.unify(x, y)?;
                    } else {
                        return self.unify_err(lhs, rhs);
                    }
                }
                Ok(())
            }
            _ => unreachable!(),
        }
    }
}
