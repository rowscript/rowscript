use crate::theory::abs::builtin::Builtins;
use crate::theory::abs::data::{FieldMap, Term};
use crate::theory::abs::def::Body;
use crate::theory::abs::def::Sigma;
use crate::theory::abs::normalize::Normalizer;
use crate::theory::{Loc, Var};
use crate::Error::{NonRowSat, NonUnifiable};
use crate::{maybe_grow, Error};

pub struct Unifier<'a> {
    builtins: &'a Builtins,
    sigma: &'a mut Sigma,
    loc: Loc,
}

impl<'a> Unifier<'a> {
    pub fn new(builtins: &'a Builtins, sigma: &'a mut Sigma, loc: Loc) -> Self {
        Self {
            builtins,
            sigma,
            loc,
        }
    }

    fn unify_err(&self, lhs: &Term, rhs: &Term) -> Result<(), Error> {
        Err(NonUnifiable(lhs.clone(), rhs.clone(), self.loc))
    }

    fn nf(&mut self) -> Normalizer {
        Normalizer::new(self.builtins, self.sigma, self.loc)
    }

    pub fn unify(&mut self, lhs: &Term, rhs: &Term) -> Result<(), Error> {
        maybe_grow(move || self.unify_impl(lhs, rhs))
    }

    fn unify_impl(&mut self, lhs: &Term, rhs: &Term) -> Result<(), Error> {
        use Term::*;

        match (lhs, rhs) {
            (MetaRef(_, v, _), rhs) => {
                self.solve(v, rhs)?;
                Ok(())
            }
            (lhs, MetaRef(_, v, _)) => {
                self.solve(v, lhs)?;
                Ok(())
            }

            (Ref(a), Ref(b)) if a == b => Ok(()),
            (Ref(a), b) => match self.sigma.get(a) {
                Some(d) => self.unify(&d.to_term(a.clone()), b),
                None => self.unify_err(lhs, rhs),
            },
            (a, Ref(b)) => match self.sigma.get(b) {
                Some(d) => self.unify(a, &d.to_term(b.clone())),
                None => self.unify_err(lhs, rhs),
            },

            (Qualified(_, a), Qualified(_, b)) if a == b => Ok(()),
            (Qualified(_, a), b) => match self.sigma.get(a) {
                Some(d) => self.unify(&d.to_term(a.clone()), b),
                None => self.unify_err(lhs, rhs),
            },
            (a, Qualified(_, b)) => match self.sigma.get(b) {
                Some(d) => self.unify(a, &d.to_term(b.clone())),
                None => self.unify_err(lhs, rhs),
            },

            (Named(m, _), Named(n, _)) if m == n => Ok(()),
            (Named(_, a), b) => self.unify(a, b),
            (a, Named(_, b)) => self.unify(a, b),

            (Let(p, a, b), Let(q, x, y)) => {
                self.unify(&p.typ, &q.typ)?;
                self.unify(a, x)?;
                self.unify(b, y)
            }
            (Pi(p, a), Pi(q, b)) => {
                self.unify(&p.typ, &q.typ)?;
                let rho = &[(&q.var, &Ref(p.var.clone()))];
                let b = self.nf().with(rho, *b.clone())?;
                self.unify(a, &b)
            }
            (Lam(p, a), Lam(_, _)) => {
                let b = self
                    .nf()
                    .apply(rhs.clone(), p.info.into(), &[Ref(p.var.clone())])?;
                self.unify(a, &b)
            }
            (App(f, i, x), App(g, j, y)) if i == j => {
                self.unify(f, g)?;
                self.unify(x, y)
            }
            (Sigma(p, a), Sigma(q, b)) => {
                self.unify(&p.typ, &q.typ)?;
                let rho = &[(&q.var, &Ref(p.var.clone()))];
                let b = self.nf().with(rho, *b.clone())?;
                self.unify(a, &b)
            }
            (Tuple(a, b), Tuple(x, y)) => {
                self.unify(a, x)?;
                self.unify(b, y)
            }
            (TupleLet(p, q, a, b), TupleLet(r, s, x, y)) => {
                let rho = &[(&r.var, &Ref(p.var.clone())), (&s.var, &Ref(q.var.clone()))];
                let y = self.nf().with(rho, *y.clone())?;
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
            (Fields(a), Fields(b)) => self.fields_eq(a, b),
            (Object(a), Object(b)) => self.unify(a, b),
            (Obj(a), Obj(b)) => self.unify(a, b),
            (Downcast(a, m), Object(b)) => self.downcast(m, a, b),
            (Object(a), Downcast(b, m)) => self.downcast(m, b, a),
            (Enum(a), Enum(b)) => self.unify(a, b),
            (Variant(a), Variant(b)) => self.unify(a, b),
            (Upcast(a), Enum(b)) => self.upcast(a, b),
            (Enum(a), Upcast(b)) => self.upcast(b, a),
            (Reflected(a), Reflected(b)) => self.unify(a, b),

            (Extern(a), Extern(b)) if a == b => Ok(()),
            (Str(a), Str(b)) if a == b => Ok(()),
            (Num(a), Num(b)) if a == b => Ok(()),
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

            _ => self.unify_err(lhs, rhs),
        }
    }

    fn solve(&mut self, meta_var: &Var, tm: &Term) -> Result<(), Error> {
        use Body::*;
        use Term::*;

        let d = self.sigma.get_mut(meta_var).unwrap();
        match &d.body {
            Meta(k, s) => {
                if s.is_some() {
                    return Ok(());
                }
                d.body = Meta(k.clone(), Some(tm.clone()));
            }
            _ => unreachable!(),
        }

        let tele = d.tele.clone();
        let ret = d.ret.clone();
        match tm {
            Ref(r) => match tele.into_iter().find(|p| &p.var == r) {
                Some(p) => self.unify(&ret, &p.typ),
                None => unreachable!(),
            },
            _ => Ok(()),
        }
    }

    pub fn fields_ord(&mut self, small: &FieldMap, big: &FieldMap) -> Result<(), Error> {
        use Term::*;
        for (x, a) in small {
            match big.get(x) {
                Some(b) => self.unify(a, b)?,
                None => {
                    return Err(NonRowSat(
                        Fields(small.clone()),
                        Fields(big.clone()),
                        self.loc,
                    ))
                }
            }
        }
        Ok(())
    }

    pub fn fields_eq(&mut self, a: &FieldMap, b: &FieldMap) -> Result<(), Error> {
        use Term::*;
        if a.len() != b.len() {
            return self.unify_err(&Fields(a.clone()), &Fields(b.clone()));
        }
        for (n, x) in a {
            if let Some(y) = b.get(n) {
                self.unify(x, y)?;
                continue;
            }
            return self.unify_err(&Fields(a.clone()), &Fields(b.clone()));
        }
        Ok(())
    }

    fn downcast(&mut self, meta: &Term, big: &Term, small: &Term) -> Result<(), Error> {
        use Term::*;
        match big {
            Object(big) => match (big.as_ref(), small) {
                (Fields(a), Fields(b)) => {
                    self.fields_ord(b, a)?;
                    self.unify(meta, small)
                }
                (a, b) => self.unify(a, b),
            },
            _ => unreachable!(),
        }
    }

    fn upcast(&mut self, small: &Term, big: &Term) -> Result<(), Error> {
        use Term::*;
        match small {
            Enum(small) => match (small.as_ref(), big) {
                (Fields(a), Fields(b)) => self.fields_ord(a, b),
                (a, b) => self.unify(a, b),
            },
            _ => unreachable!(),
        }
    }
}
