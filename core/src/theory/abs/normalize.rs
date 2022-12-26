use crate::theory::abs::data::Term::{App, Lam};
use crate::theory::abs::data::{Dir, FieldMap, Term};
use crate::theory::abs::def::{Body, Rho, Sigma};
use crate::theory::abs::rename::{rename, Renamer};
use crate::theory::abs::unify::Unifier;
use crate::theory::{Loc, Param, Var};
use crate::Error;

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

    pub fn term(&mut self, tm: Box<Term>) -> Result<Box<Term>, Error> {
        use Body::*;
        use Term::*;

        Ok(match *tm {
            Ref(ref x) => {
                if let Some(y) = self.rho.get(&x) {
                    self.term(Renamer::default().term(y.clone()))?
                } else {
                    tm.clone()
                }
            }
            MetaRef(x, sp) => {
                let mut def = self.sigma.get(&x).unwrap().clone();
                def.ret = self.term(def.ret)?;
                let ret = match &def.body {
                    Meta(s) => {
                        if let Some(solved) = s {
                            let mut ret = rename(Term::lam(&def.tele, Box::new(solved.clone())));
                            for (_, x) in sp {
                                ret = Box::new(App(ret, Box::new(x)))
                            }
                            self.term(ret)?
                        } else {
                            Box::new(Self::auto_implicit(&*def.ret).map_or_else(
                                || MetaRef(x.clone(), sp),
                                |tm| {
                                    def.body = Meta(Some(tm.clone()));
                                    tm
                                },
                            ))
                        }
                    }
                    _ => unreachable!(),
                };
                self.sigma.insert(x, def);
                ret
            }
            Let(p, a, b) => {
                let a = self.term(a)?;
                match &*a {
                    MetaRef(_, _) => Box::new(Let(p, a, b)),
                    _ => self.with(&[(&p.var, &a)], b)?,
                }
            }
            Pi(p, b) => Box::new(Pi(self.param(p)?, self.term(b)?)),
            Lam(p, b) => Box::new(Lam(self.param(p)?, self.term(b)?)),
            App(f, x) => {
                let f = self.term(f)?;
                let x = self.term(x)?;
                if let MetaRef(_, _) = &*x {
                    Box::new(App(f, x))
                } else if let Lam(p, b) = *f {
                    self.rho.insert(p.var, x);
                    self.term(b)?
                } else {
                    Box::new(App(f, x))
                }
            }
            Sigma(p, b) => Box::new(Sigma(self.param(p)?, self.term(b)?)),
            Tuple(a, b) => Box::new(Tuple(self.term(a)?, self.term(b)?)),
            TupleLet(p, q, a, b) => {
                let a = self.term(a)?;
                if let MetaRef(_, _) = &*a {
                    Box::new(TupleLet(p, q, a, b))
                } else if let Tuple(x, y) = *a {
                    self.rho.insert(p.var, x);
                    self.rho.insert(q.var, y);
                    self.term(b)?
                } else {
                    Box::new(TupleLet(p, q, a, b))
                }
            }
            UnitLet(a, b) => {
                let a = self.term(a)?;
                if let MetaRef(_, _) = &*a {
                    Box::new(UnitLet(a, b))
                } else if let TT = *a {
                    self.term(b)?
                } else {
                    Box::new(UnitLet(a, b))
                }
            }
            If(p, t, e) => {
                let p = self.term(p)?;
                match *p {
                    True => self.term(t)?,
                    False => self.term(e)?,
                    _ => Box::new(If(p, t, e)),
                }
            }
            Fields(fields) => {
                let mut nf = FieldMap::default();
                for (f, tm) in fields {
                    nf.insert(f, *self.term(Box::new(tm.clone()))?);
                }
                Box::new(Fields(nf))
            }
            Combine(a, b) => {
                let a = self.term(a)?;
                let b = self.term(b)?;
                match (&*a, &*b) {
                    (Fields(a), Fields(b)) => {
                        let mut m = FieldMap::default();
                        for (n, x) in a {
                            m.insert(n.clone(), x.clone());
                        }
                        for (n, x) in b {
                            m.insert(n.clone(), x.clone());
                        }
                        Box::new(Fields(m))
                    }
                    _ => Box::new(Combine(a, b)),
                }
            }
            RowOrd(a, d, b) => {
                let a = self.term(a)?;
                let b = self.term(b)?;
                if let (Fields(_), Fields(_)) = (&*a, &*b) {
                    let mut u = Unifier::new(&mut self.sigma, self.loc);
                    match d {
                        Dir::Le => u.unify_fields_ord(&*a, &*b)?,
                        Dir::Ge => u.unify_fields_ord(&*b, &*a)?,
                    };
                }
                Box::new(RowOrd(a, d, b))
            }
            RowEq(a, b) => {
                let a = self.term(a)?;
                let b = self.term(b)?;
                if let (Fields(_), Fields(_)) = (&*a, &*b) {
                    Unifier::new(&mut self.sigma, self.loc).unify_fields_eq(&*a, &*b)?;
                }
                Box::new(RowEq(a, b))
            }
            Object(r) => Box::new(Object(self.term(r)?)),
            Obj(a) => Box::new(Obj(self.term(a)?)),
            Concat(a, b) => {
                let a = self.term(a)?;
                let b = self.term(b)?;
                Box::new(match (&*a, &*b) {
                    (Obj(x), Obj(y)) => match (&**x, &**y) {
                        (Fields(x), Fields(y)) => {
                            let mut m = x.clone();
                            for (n, t) in y {
                                m.insert(n.clone(), t.clone());
                            }
                            Obj(Box::new(Fields(m)))
                        }
                        _ => Concat(a, b),
                    },
                    _ => Concat(a, b),
                })
            }
            Access(a, n) => {
                let a = self.term(a)?;
                Box::new(match &*a {
                    Obj(x) => match &**x {
                        Fields(fields) => fields.get(&n).unwrap().clone(),
                        _ => Access(a, n),
                    },
                    _ => Access(a, n),
                })
            }
            Cast(a, ty) => {
                let a = self.term(a)?;
                Box::new(match (&*a, &*ty) {
                    (Obj(o), Object(t)) => match (&**o, &**t) {
                        (Fields(x), Fields(y)) => {
                            let mut m = FieldMap::default();
                            for (n, _) in y {
                                if let Some(tm) = x.get(n) {
                                    m.insert(n.clone(), tm.clone());
                                }
                            }
                            Obj(Box::new(Fields(m)))
                        }
                        _ => Cast(a, ty),
                    },
                    _ => Cast(a, ty),
                })
            }

            Univ => Box::new(Univ),
            Unit => Box::new(Unit),
            TT => Box::new(TT),
            Boolean => Box::new(Boolean),
            False => Box::new(False),
            True => Box::new(True),
            String => Box::new(String),
            Str(v) => Box::new(Str(v)),
            Number => Box::new(Number),
            Num(r, v) => Box::new(Num(r, v)),
            BigInt => Box::new(BigInt),
            Big(v) => Box::new(Big(v)),
            Row => Box::new(Row),
            RowSat => Box::new(RowSat),
            RowRefl => Box::new(RowRefl),
        })
    }

    pub fn with(&mut self, rho: &[(&Var, &Box<Term>)], tm: Box<Term>) -> Result<Box<Term>, Error> {
        for (x, v) in rho {
            let x = *x;
            let v = *v;
            self.rho.insert(x.clone(), v.clone());
        }
        self.term(tm)
    }

    pub fn apply(&mut self, f: Box<Term>, args: &[&Box<Term>]) -> Result<Box<Term>, Error> {
        let mut ret = f.clone();
        for &x in args {
            match *ret {
                Lam(p, b) => {
                    ret = self.with(&[(&p.var, x)], b)?;
                }
                _ => ret = Box::new(App(ret, x.clone())),
            }
        }
        Ok(ret)
    }

    fn param(&mut self, p: Param<Term>) -> Result<Param<Term>, Error> {
        Ok(Param {
            var: p.var,
            info: p.info,
            typ: self.term(p.typ)?,
        })
    }

    fn auto_implicit(tm: &Term) -> Option<Term> {
        use Term::*;
        match tm {
            RowEq(_, _) => Some(RowRefl),
            RowOrd(_, _, _) => Some(RowSat),
            _ => None,
        }
    }
}
