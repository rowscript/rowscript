use crate::Error::{EffectNonUnifiable, ExpectedObject, NonRowSat, NonUnifiable};
use crate::theory::NameMap;
use crate::theory::abs::data::{FieldMap, Term};
use crate::theory::abs::def::Body;
use crate::theory::abs::def::Sigma;
use crate::theory::abs::normalize::Normalizer;
use crate::theory::{Loc, Var};
use crate::{Error, maybe_grow};

pub struct Unifier<'a> {
    ubiquitous: &'a NameMap,
    sigma: &'a mut Sigma,
    loc: Loc,
    no_meta_solving: bool,
}

impl<'a> Unifier<'a> {
    pub fn new(ubiquitous: &'a NameMap, sigma: &'a mut Sigma, loc: Loc) -> Self {
        Self {
            ubiquitous,
            sigma,
            loc,
            no_meta_solving: false,
        }
    }

    pub fn unify(&mut self, lhs: &Term, rhs: &Term) -> Result<(), Error> {
        maybe_grow(move || self.unify_impl(lhs, rhs))
    }

    pub fn unify_eff(&mut self, lhs: &Term, rhs: &Term) -> Result<(), Error> {
        self.unify(lhs, rhs).map_err(|e| match e {
            NonUnifiable(l, r, loc) => EffectNonUnifiable(l, r, loc),
            e => e,
        })
    }

    pub fn without_meta_solving(&mut self, lhs: &Term, rhs: &Term) -> Result<(), Error> {
        let no_meta_solving = self.no_meta_solving;
        self.no_meta_solving = true;
        self.unify(lhs, rhs)?;
        self.no_meta_solving = no_meta_solving;
        Ok(())
    }

    fn unify_err(&self, lhs: &Term, rhs: &Term) -> Result<(), Error> {
        Err(NonUnifiable(lhs.clone(), rhs.clone(), self.loc))
    }

    fn nf(&mut self) -> Normalizer {
        Normalizer::new(self.ubiquitous, self.sigma, self.loc)
    }

    fn swap_err(err: Error) -> Error {
        match err {
            NonUnifiable(lhs, rhs, loc) => NonUnifiable(rhs, lhs, loc),
            e => e,
        }
    }

    fn unify_impl(&mut self, lhs: &Term, rhs: &Term) -> Result<(), Error> {
        use Term::*;

        match (lhs, rhs) {
            (MetaRef(k, a, _), MetaRef(l, b, _)) if k == l && a == b => Ok(()),
            (MetaRef(_, v, _), rhs) if !self.no_meta_solving => {
                self.solve(v, rhs)?;
                Ok(())
            }
            (lhs, MetaRef(_, v, _)) if !self.no_meta_solving => {
                self.solve(v, lhs)?;
                Ok(())
            }

            (a, Varargs(b)) => self.unify(a, b),
            (Varargs(a), b) => self.unify(a, b),
            (a, AnonVarargs(b)) => self.unify(a, b),
            (AnonVarargs(a), b) => self.unify(a, b),

            // If expected effect is impure, but the actual is pure, we could proceed. But the opposite is not ture.
            (Effect(..), Pure) => Ok(()),
            (Ref(..), Pure) => Ok(()),

            (Ref(a), Ref(b)) if a == b => Ok(()),
            (Qualified(_, a), Qualified(_, b)) if a == b => Ok(()),

            (Ref(a), b) | (Qualified(_, a), b) => match self.sigma.get(a) {
                Some(d) => self.unify(&d.to_term(), b),
                None => self.unify_err(lhs, rhs),
            },
            (a, Ref(b)) | (a, Qualified(_, b)) => match self.sigma.get(b) {
                Some(d) => self.unify(a, &d.to_term()),
                None => self.unify_err(lhs, rhs),
            },

            (
                Cls {
                    class: m,
                    object: a,
                    ..
                },
                Cls {
                    class: n,
                    object: b,
                    ..
                },
            ) if m == n => self.unify(a, b),
            (Cls { object, .. }, b) => self.unify(object, b),
            (a, Cls { object, .. }) => self.unify(a, object),

            (Union(a), Union(b)) if a.len() == b.len() && self.union_eq(a, b) => Ok(()),
            (Union(a), b) if self.union_ord(a, b) => Ok(()),
            (Object(a), Union(b)) if matches!(a.as_ref(), MetaRef(..)) => {
                self.solve_object_union(a, b)
            }

            (Const(p, a, b), Const(q, x, y)) => {
                self.unify(&p.typ, &q.typ)?;
                self.unify(a, x)?;
                self.unify(b, y)
            }
            (
                Pi {
                    param: p, body: a, ..
                },
                Pi {
                    param: q, body: b, ..
                },
            ) => {
                self.unify(&p.typ, &q.typ)?;
                let rho = &[(&q.var, &Ref(p.var.clone()))];
                let b = self.nf().with(rho, *b.clone())?;
                self.unify(a, &b)
            }
            (Lam(p, a), Lam(..)) => {
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
            (TupleBind(p, q, a, b), TupleBind(r, s, x, y)) => {
                let rho = &[(&r.var, &Ref(p.var.clone())), (&s.var, &Ref(q.var.clone()))];
                let y = self.nf().with(rho, *y.clone())?;
                self.unify(a, x)?;
                self.unify(b, &y)
            }
            (UnitBind(a, b), UnitBind(x, y)) => {
                self.unify(a, x)?;
                self.unify(b, y)
            }
            (If(a, b, c), If(x, y, z)) => {
                self.unify(a, x)?;
                self.unify(b, y)?;
                self.unify(c, z)
            }
            (ArrayIterator(a), ArrayIterator(b)) => self.unify(a, b),
            (Array(a), Array(b)) => self.unify(a, b),
            (MapIterator(a), MapIterator(b)) => self.unify(a, b),
            (Map(ka, va), Map(kb, vb)) => {
                self.unify(ka, kb)?;
                self.unify(va, vb)
            }
            (Fields(a), Fields(b)) => self.fields_eq(a, b),
            (Associate(a, x), Associate(b, y)) if x == y => self.unify(a, b),
            (Object(a), Object(b)) => self.unify(a, b),
            (Obj(a), Obj(b)) => self.unify(a, b),
            (Downcast(a, m), Object(b)) => self.downcast(m, a, b),
            (Object(a), Downcast(b, m)) => self.downcast(m, b, a).map_err(Self::swap_err),
            (Enum(a), Enum(b)) => self.unify(a, b),
            (Variant(a), Variant(b)) => self.unify(a, b),
            (Upcast(a), Enum(b)) => self.upcast(a, b),
            (Enum(a), Upcast(b)) => self.upcast(b, a).map_err(Self::swap_err),

            (Interface { name: x, args: xs }, Interface { name: y, args: ys })
                if x == y && xs.len() == ys.len() =>
            {
                xs.iter()
                    .zip(ys.iter())
                    .try_for_each(|(a, b)| self.unify(a, b))
            }

            (a, Object(..)) | (a, Downcast(..)) | (a, Enum(..)) | (a, Upcast(..)) if a.has_mu() => {
                let a = self.nf().with_expand_mu(a.clone())?;
                self.unify(&a, rhs)
            }
            (Object(..), b) | (Downcast(..), b) | (Enum(..), b) | (Upcast(..), b) if b.has_mu() => {
                let b = self.nf().with_expand_mu(b.clone())?;
                self.unify(lhs, &b)
            }

            (Extern(a), Extern(b)) if a == b => Ok(()),
            (Mu(a), Mu(b)) if a == b => Ok(()),
            (Str(a), Str(b)) if a == b => Ok(()),
            (Num(a), Num(b)) if a == b => Ok(()),
            (Big(a), Big(b)) if a == b => Ok(()),
            (Effect(a), Effect(b)) if a == b => Ok(()),

            (Univ, Univ) => Ok(()),
            (Unit, Unit) => Ok(()),
            (TT, TT) => Ok(()),
            (Boolean, Boolean) => Ok(()),
            (False, False) => Ok(()),
            (True, True) => Ok(()),
            (String, String) => Ok(()),
            (Number, Number) => Ok(()),
            (Bigint, Bigint) => Ok(()),
            (Row, Row) => Ok(()),
            (Rowkey, Rowkey) => Ok(()),
            (Pure, Pure) => Ok(()),

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
                d.body = Meta(k.clone(), Some(Box::new(tm.clone())));
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
                    ));
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

    fn union_eq(&mut self, a: &[Term], b: &[Term]) -> bool {
        b.iter().all(|y| self.union_ord(a, y))
    }

    fn union_ord(&mut self, a: &[Term], b: &Term) -> bool {
        a.iter().any(|a| self.without_meta_solving(a, b).is_ok())
    }

    fn solve_object_union(&mut self, a: &Term, b: &[Term]) -> Result<(), Error> {
        use Term::*;
        let u = Union(
            b.iter()
                .map(|t| match t {
                    Object(f) if matches!(f.as_ref(), Fields(..)) => Ok(*f.clone()),
                    a => Err(ExpectedObject(a.clone(), self.loc)),
                })
                .collect::<Result<_, _>>()?,
        );
        self.unify(a, &u)
    }
}
