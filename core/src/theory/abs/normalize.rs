use crate::theory::abs::data::Term::{App, Lam};
use crate::theory::abs::data::{CaseMap, Dir, FieldMap, Term};
use crate::theory::abs::def::{Body, Rho, Sigma};
use crate::theory::abs::rename::rename;
use crate::theory::abs::unify::Unifier;
use crate::theory::conc::data::ArgInfo;
use crate::theory::conc::data::ArgInfo::UnnamedExplicit;
use crate::theory::{Loc, Param, Var};
use crate::Error;
use crate::Error::{UnresolvedField, UnresolvedImplementation};

pub struct Normalizer<'a> {
    sigma: &'a mut Sigma,
    rho: Rho,
    loc: Loc,
}

impl<'a> Normalizer<'a> {
    pub fn new(sigma: &'a mut Sigma, loc: Loc) -> Self {
        Self {
            sigma,
            rho: Default::default(),
            loc,
        }
    }

    pub fn term(&mut self, tm: Term) -> Result<Term, Error> {
        stacker::maybe_grow(512 * 1024, 4 * 1024 * 1024, move || self.term_impl(tm))
    }

    fn term_impl(&mut self, tm: Term) -> Result<Term, Error> {
        use Body::*;
        use Term::*;

        Ok(match tm {
            Ref(x) => {
                if let Some(y) = self.rho.get(&x) {
                    self.term(rename(*y.clone()))?
                } else {
                    Ref(x)
                }
            }
            MetaRef(k, x, sp) => {
                let mut def = self.sigma.get(&x).unwrap().clone();
                def.ret = Box::new(self.term(*def.ret)?);
                let ret = match &def.body {
                    Meta(_, s) => match s {
                        Some(solved) => {
                            let mut ret = rename(Term::lam(&def.tele, solved.clone()));
                            for (_, x) in sp {
                                ret = App(Box::new(ret), UnnamedExplicit, Box::new(x))
                            }
                            self.term(ret)?
                        }
                        None => Self::auto_implicit(&def.ret).map_or(
                            MetaRef(k.clone(), x.clone(), sp),
                            |tm| {
                                def.body = Meta(k, Some(tm.clone()));
                                tm
                            },
                        ),
                    },
                    _ => unreachable!(),
                };
                self.sigma.insert(x, def);
                ret
            }
            Undef(x) => self.sigma.get(&x).unwrap().to_term(x),
            Let(p, a, b) => match self.term(*a)? {
                MetaRef(k, r, sp) => Let(p, Box::new(MetaRef(k, r, sp)), Box::new(self.term(*b)?)),
                a => self.with(&[(&p.var, &a)], *b)?,
            },
            Pi(p, b) => Pi(self.param(p)?, Box::new(self.term(*b)?)),
            Lam(p, b) => Lam(self.param(p)?, Box::new(self.term(*b)?)),
            App(f, ai, x) => {
                let f = self.term(*f)?;
                let x = self.term(*x)?;
                if let MetaRef(k, r, sp) = x {
                    App(Box::new(f), ai, Box::new(MetaRef(k, r, sp)))
                } else if let Lam(p, b) = f {
                    self.rho.insert(p.var, Box::new(x));
                    self.term(*b)?
                } else {
                    App(Box::new(f), ai, Box::new(x))
                }
            }
            Sigma(p, b) => Sigma(self.param(p)?, Box::new(self.term(*b)?)),
            Tuple(a, b) => Tuple(Box::new(self.term(*a)?), Box::new(self.term(*b)?)),
            TupleLet(p, q, a, b) => match self.term(*a)? {
                MetaRef(k, r, sp) => {
                    TupleLet(p, q, Box::new(MetaRef(k, r, sp)), Box::new(self.term(*b)?))
                }
                Tuple(x, y) => {
                    self.rho.insert(p.var, x);
                    self.rho.insert(q.var, y);
                    self.term(*b)?
                }
                a => TupleLet(p, q, Box::new(a), Box::new(self.term(*b)?)),
            },
            UnitLet(a, b) => match self.term(*a)? {
                TT => self.term(*b)?,
                a => UnitLet(Box::new(a), Box::new(self.term(*b)?)),
            },
            If(p, t, e) => {
                let p = self.term(*p)?;
                let t = self.term(*t)?;
                let e = self.term(*e)?;
                match p {
                    True => t,
                    False => e,
                    p => If(Box::new(p), Box::new(t), Box::new(e)),
                }
            }
            Fields(fields) => {
                let mut nf = FieldMap::default();
                for (f, tm) in fields {
                    nf.insert(f, self.term(tm)?);
                }
                Fields(nf)
            }
            Combine(a, b) => match (self.term(*a)?, self.term(*b)?) {
                (Fields(mut a), Fields(b)) => {
                    a.extend(b.into_iter());
                    Fields(a)
                }
                (a, b) => Combine(Box::new(a), Box::new(b)),
            },
            RowOrd(a, d, b) => {
                let a = self.term(*a)?;
                let b = self.term(*b)?;
                if let (Fields(_), Fields(_)) = (&a, &b) {
                    let mut u = Unifier::new(self.sigma, self.loc);
                    match d {
                        Dir::Le => u.unify_fields_ord(&a, &b)?,
                        Dir::Ge => u.unify_fields_ord(&b, &a)?,
                    };
                }
                RowOrd(Box::new(a), d, Box::new(b))
            }
            RowEq(a, b) => {
                let a = self.term(*a)?;
                let b = self.term(*b)?;
                if let (Fields(_), Fields(_)) = (&a, &b) {
                    Unifier::new(self.sigma, self.loc).unify_fields_eq(&a, &b)?;
                }
                RowEq(Box::new(a), Box::new(b))
            }
            Object(r) => Object(Box::new(self.term(*r)?)),
            Obj(a) => Obj(Box::new(self.term(*a)?)),
            Concat(a, b) => match (self.term(*a)?, self.term(*b)?) {
                (Obj(x), Obj(y)) => match (*x, *y) {
                    (Fields(mut x), Fields(y)) => {
                        x.extend(y.into_iter());
                        Obj(Box::new(Fields(x)))
                    }
                    (a, b) => Concat(Box::new(Obj(Box::new(a))), Box::new(Obj(Box::new(b)))),
                },
                (a, b) => Concat(Box::new(a), Box::new(b)),
            },
            Access(a, n) => match self.term(*a)? {
                Obj(x) => match *x {
                    Fields(fields) => fields.get(&n).unwrap().clone(),
                    a => Access(Box::new(Obj(Box::new(a))), n),
                },
                a => Access(Box::new(a), n),
            },
            Downcast(a, f) => match (self.term(*a)?, *f) {
                (Obj(o), Fields(y)) => match (*o, y) {
                    (Fields(x), y) => Obj(Box::new(Fields(
                        y.into_keys()
                            .map(|n| {
                                let tm = x.get(&n).unwrap().clone();
                                (n, tm)
                            })
                            .collect(),
                    ))),
                    (a, f) => Downcast(Box::new(Obj(Box::new(a))), Box::new(Fields(f))),
                },
                (a, f) => Downcast(Box::new(a), Box::new(f)),
            },
            Enum(r) => Enum(Box::new(self.term(*r)?)),
            Variant(r) => Variant(Box::new(self.term(*r)?)),
            Upcast(a, f) => match (self.term(*a)?, *f) {
                (Variant(o), Fields(y)) => match (*o, y) {
                    (Fields(x), y) => {
                        let name = x.iter().next().unwrap().0;
                        if !y.contains_key(name) {
                            return Err(UnresolvedField(name.clone(), Fields(y), self.loc));
                        }
                        Variant(Box::new(Fields(x)))
                    }
                    (a, f) => Upcast(Box::new(Variant(Box::new(a))), Box::new(Fields(f))),
                },
                (a, f) => Upcast(Box::new(a), Box::new(f)),
            },
            Switch(a, cs) => match self.term(*a)? {
                Variant(r) => match *r {
                    Fields(f) => {
                        let (n, x) = f.into_iter().next().unwrap();
                        let (v, tm) = cs.get(&n).unwrap();
                        self.with(&[(v, &x)], tm.clone())?
                    }
                    r => Switch(Box::new(Variant(Box::new(r))), self.case_map(cs)?),
                },
                a => Switch(Box::new(a), self.case_map(cs)?),
            },
            Vptr(r, ts) => {
                let mut types = Vec::default();
                for t in ts {
                    types.push(self.term(t)?)
                }
                Vptr(r, types)
            }
            Vp(r, ts) => {
                let mut types = Vec::default();
                for t in ts {
                    types.push(self.term(t)?)
                }
                Vp(r, types)
            }
            Lookup(a) => Lookup(Box::new(self.term(*a)?)),
            ImplementsOf(a, i) => ImplementsOf(
                match self.term(*a)? {
                    Ref(r) => Box::new(Ref(r)),
                    MetaRef(k, r, sp) => Box::new(MetaRef(k, r, sp)),
                    ty => {
                        let ty = Box::new(ty);
                        self.check_constraint(&ty, &i)?;
                        ty
                    }
                },
                i,
            ),
            Find(ty, i, f) => Find(
                Box::new(match self.term(*ty)? {
                    Ref(r) => Ref(r),
                    MetaRef(k, r, sp) => MetaRef(k, r, sp),
                    ty => return self.find_implementation(ty, i, f),
                }),
                i,
                f,
            ),

            tm => tm,
        })
    }

    pub fn with(&mut self, rho: &[(&Var, &Term)], tm: Term) -> Result<Term, Error> {
        for &(x, v) in rho {
            self.rho.insert(x.clone(), Box::new(v.clone()));
        }
        self.term(tm)
    }

    pub fn apply(&mut self, f: Term, ai: ArgInfo, args: &[Term]) -> Result<Term, Error> {
        let mut ret = f;
        for x in args {
            match ret {
                Lam(p, b) => {
                    ret = self.with(&[(&p.var, x)], *b)?;
                }
                _ => ret = App(Box::new(ret), ai.clone(), Box::new(x.clone())),
            }
        }
        Ok(ret)
    }

    fn param(&mut self, p: Param<Term>) -> Result<Param<Term>, Error> {
        Ok(Param {
            var: p.var,
            info: p.info,
            typ: Box::new(self.term(*p.typ)?),
        })
    }

    fn case_map(&mut self, cs: CaseMap) -> Result<CaseMap, Error> {
        let mut ret = CaseMap::default();
        for (n, (v, tm)) in cs {
            ret.insert(n, (v, self.term(tm)?));
        }
        Ok(ret)
    }

    fn auto_implicit(tm: &Term) -> Option<Term> {
        use Term::*;
        match tm {
            RowEq(_, _) => Some(RowRefl),
            RowOrd(_, _, _) => Some(RowSat),
            ImplementsOf(_, _) => Some(ImplementsSat),
            _ => None,
        }
    }

    fn check_constraint(&mut self, x: &Term, i: &Var) -> Result<(), Error> {
        use Body::*;

        let ims = match &self.sigma.get(i).unwrap().body {
            Interface { ims, .. } => ims.clone(),
            _ => unreachable!(),
        };
        for im in ims {
            let y = match &self.sigma.get(&im).unwrap().body {
                Implements { i: (_, im), .. } => self.sigma.get(im).unwrap().to_term(im.clone()),
                _ => unreachable!(),
            };
            match Unifier::new(self.sigma, self.loc).unify(&y, x) {
                Ok(_) => return Ok(()),
                Err(_) => continue,
            }
        }
        Err(UnresolvedImplementation(x.clone(), self.loc))
    }

    fn find_implementation(&mut self, ty: Term, i: Var, f: Var) -> Result<Term, Error> {
        use Body::*;

        let ims = match &self.sigma.get(&i).unwrap().body {
            Interface { ims, .. } => ims.clone(),
            _ => unreachable!(),
        };

        for im in ims.into_iter().rev() {
            let (im_ty, im_fn) = match &self.sigma.get(&im).unwrap().body {
                Implements {
                    i: (_, im_ty), fns, ..
                } => (
                    self.sigma.get(im_ty).unwrap().to_term(im_ty.clone()),
                    fns.get(&f).unwrap().clone(),
                ),
                _ => unreachable!(),
            };

            if Unifier::new(self.sigma, self.loc)
                .unify(&ty, &im_ty)
                .is_err()
            {
                continue;
            }

            return Ok(self.sigma.get(&im_fn).unwrap().to_term(im_fn));
        }

        Err(UnresolvedImplementation(ty, self.loc))
    }
}
