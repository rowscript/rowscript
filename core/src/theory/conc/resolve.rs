use std::collections::HashMap;

use crate::theory::abs::def::Body;
use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::theory::conc::data::Expr::Unresolved;
use crate::theory::{Param, RawNameSet, Tele, Var};
use crate::Error;
use crate::Error::UnresolvedVar;

#[derive(Default)]
pub struct Resolver(HashMap<String, Var>);

impl Resolver {
    pub fn defs(&mut self, defs: Vec<Def<Expr>>) -> Result<Vec<Def<Expr>>, Error> {
        let mut ret = Vec::default();
        let mut names = RawNameSet::default();
        for d in defs {
            names.var(d.loc, &d.name)?;
            ret.push(self.def(d)?);
        }
        Ok(ret)
    }

    fn def(&mut self, mut d: Def<Expr>) -> Result<Def<Expr>, Error> {
        use Body::*;

        let mut recoverable = Vec::default();
        let mut removable = Vec::default();

        let mut tele = Tele::default();
        for p in d.tele {
            if let Some(old) = self.insert(&p.var) {
                recoverable.push(old);
            } else {
                removable.push(p.var.clone());
            }
            tele.push(Param {
                var: p.var,
                info: p.info,
                typ: Box::new(self.expr(*p.typ)?),
            });
        }
        d.tele = tele;
        d.ret = Box::new(self.expr(*d.ret)?);
        d.body = match d.body {
            Fn(f) => Fn(Box::new(self.self_referencing_fn(&d.name, *f)?)),
            Postulate => Postulate,
            Alias(t) => Alias(Box::new(self.expr(*t)?)),

            Class {
                object,
                methods,
                ctor,
                vptr,
                vptr_ctor,
                vtbl,
                vtbl_lookup,
            } => Class {
                object: Box::new(self.expr(*object)?),
                methods,
                ctor,
                vptr,
                vptr_ctor,
                vtbl,
                vtbl_lookup,
            },
            Ctor(f) => Ctor(Box::new(self.self_referencing_fn(&d.name, *f)?)),
            Method(f) => Method(Box::new(self.expr(*f)?)), // FIXME: currently cannot be recursive
            VptrType(t) => VptrType(Box::new(self.expr(*t)?)),
            VptrCtor(t) => VptrCtor(t),
            VtblType(t) => VtblType(Box::new(self.expr(*t)?)),
            VtblLookup => VtblLookup,

            Interface { fns, ims } => Interface { fns, ims },
            Implements { i: (i, im), fns } => {
                let loc = d.loc;
                let i = self.expr(Unresolved(loc, i))?.resolved();
                let im = self.expr(Unresolved(loc, im))?.resolved();
                let mut resolved = HashMap::default();
                for (i_fn, im_fn) in fns {
                    resolved.insert(
                        self.expr(Unresolved(loc, i_fn))?.resolved(),
                        self.expr(Unresolved(loc, im_fn))?.resolved(),
                    );
                }
                Implements {
                    i: (i, im),
                    fns: resolved,
                }
            }
            ImplementsFn(f) => ImplementsFn(Box::new(self.expr(*f)?)), // FIXME: currently cannot be recursive
            Findable(i) => Findable(i),

            Undefined => unreachable!(),
            Meta(_, _) => unreachable!(),
        };

        for x in removable {
            self.0.remove(x.as_str());
        }
        for x in recoverable {
            self.insert(&x);
        }
        self.insert(&d.name);

        Ok(d)
    }

    fn insert(&mut self, v: &Var) -> Option<Var> {
        self.0.insert(v.to_string(), v.clone())
    }

    fn bodied(&mut self, vars: &[&Var], e: Expr) -> Result<Expr, Error> {
        let mut olds = Vec::default();

        for &v in vars {
            olds.push(self.insert(v));
        }

        let ret = self.expr(e)?;

        for i in 0..vars.len() {
            let old = olds.get(i).unwrap();
            if let Some(v) = old {
                self.insert(v);
            } else {
                self.0.remove(&*vars.get(i).unwrap().name);
            }
        }

        Ok(ret)
    }

    fn param(&mut self, p: Param<Expr>) -> Result<Param<Expr>, Error> {
        Ok(Param {
            var: p.var,
            info: p.info,
            typ: Box::new(self.expr(*p.typ)?),
        })
    }

    fn expr(&mut self, e: Expr) -> Result<Expr, Error> {
        use Expr::*;
        Ok(match e {
            Unresolved(loc, r) => {
                if let Some(v) = self.0.get(&*r.name) {
                    Resolved(loc, v.clone())
                } else {
                    return Err(UnresolvedVar(loc));
                }
            }
            Let(loc, x, typ, a, b) => {
                let b = self.bodied(&[&x], *b)?;
                Let(
                    loc,
                    x,
                    if let Some(ty) = typ {
                        Some(Box::new(self.expr(*ty)?))
                    } else {
                        None
                    },
                    Box::new(self.expr(*a)?),
                    Box::new(b),
                )
            }
            Pi(loc, p, b) => {
                let b = self.bodied(&[&p.var], *b)?;
                Pi(loc, self.param(p)?, Box::new(b))
            }
            TupledLam(loc, vars, b) => {
                let x = Var::tupled();
                let wrapped = Expr::wrap_tuple_lets(loc, &x, vars, b);
                let desugared = Lam(loc, x.clone(), wrapped);
                self.bodied(&[&x], desugared)?
            }
            AnnoLam(loc, p, b) => {
                let b = Box::new(self.bodied(&[&p.var], *b)?);
                AnnoLam(loc, self.param(p)?, b)
            }
            Lam(loc, x, b) => {
                let b = Box::new(self.bodied(&[&x], *b)?);
                Lam(loc, x, b)
            }
            App(loc, f, i, x) => App(loc, Box::new(self.expr(*f)?), i, Box::new(self.expr(*x)?)),
            Sigma(loc, p, b) => {
                let b = Box::new(self.bodied(&[&p.var], *b)?);
                Sigma(loc, self.param(p)?, b)
            }
            Tuple(loc, a, b) => Tuple(loc, Box::new(self.expr(*a)?), Box::new(self.expr(*b)?)),
            TupleLet(loc, x, y, a, b) => {
                let b = Box::new(self.bodied(&[&x, &y], *b)?);
                TupleLet(loc, x, y, Box::new(self.expr(*a)?), b)
            }
            AnnoTupleLet(loc, p, q, a, b) => {
                let b = Box::new(self.bodied(&[&p.var, &q.var], *b)?);
                AnnoTupleLet(
                    loc,
                    self.param(p)?,
                    self.param(q)?,
                    Box::new(self.expr(*a)?),
                    b,
                )
            }
            UnitLet(loc, a, b) => UnitLet(loc, Box::new(self.expr(*a)?), Box::new(self.expr(*b)?)),
            If(loc, p, t, e) => If(
                loc,
                Box::new(self.expr(*p)?),
                Box::new(self.expr(*t)?),
                Box::new(self.expr(*e)?),
            ),
            Fields(loc, fields) => {
                let mut names = RawNameSet::default();
                let mut resolved = Vec::default();
                for (f, typ) in fields {
                    names.raw(loc, f.clone())?;
                    resolved.push((f, self.expr(typ)?));
                }
                Fields(loc, resolved)
            }
            Combine(loc, a, b) => Combine(loc, Box::new(self.expr(*a)?), Box::new(self.expr(*b)?)),
            RowOrd(loc, a, d, b) => {
                RowOrd(loc, Box::new(self.expr(*a)?), d, Box::new(self.expr(*b)?))
            }
            RowEq(loc, a, b) => RowEq(loc, Box::new(self.expr(*a)?), Box::new(self.expr(*b)?)),
            Object(loc, a) => Object(loc, Box::new(self.expr(*a)?)),
            Obj(loc, a) => Obj(loc, Box::new(self.expr(*a)?)),
            Concat(loc, a, b) => Concat(loc, Box::new(self.expr(*a)?), Box::new(self.expr(*b)?)),
            Downcast(loc, a) => Downcast(loc, Box::new(self.expr(*a)?)),
            Enum(loc, a) => Enum(loc, Box::new(self.expr(*a)?)),
            Variant(loc, n, a) => Variant(loc, n, Box::new(self.expr(*a)?)),
            Upcast(loc, a) => Upcast(loc, Box::new(self.expr(*a)?)),
            Switch(loc, a, cs) => {
                let mut names = RawNameSet::default();
                let mut new = Vec::default();
                for (n, v, e) in cs {
                    names.raw(loc, n.clone())?;
                    let e = self.bodied(&[&v], e)?;
                    new.push((n, v, e));
                }
                Switch(loc, Box::new(self.expr(*a)?), new)
            }
            Lookup(loc, o, n, a) => {
                Lookup(loc, Box::new(self.expr(*o)?), n, Box::new(self.expr(*a)?))
            }
            Vptr(loc, r, ts) => {
                let mut types = Vec::default();
                for t in ts {
                    types.push(self.expr(t)?);
                }
                Vptr(loc, r, types)
            }
            Constraint(loc, r) => Constraint(loc, Box::new(self.expr(*r)?)),
            ImplementsOf(loc, a) => ImplementsOf(loc, Box::new(self.expr(*a)?)),

            Resolved(loc, r) => Resolved(loc, r),
            Hole(loc) => Hole(loc),
            InsertedHole(loc) => InsertedHole(loc),
            Univ(loc) => Univ(loc),
            Unit(loc) => Unit(loc),
            TT(loc) => TT(loc),
            Boolean(loc) => Boolean(loc),
            False(loc) => False(loc),
            True(loc) => True(loc),
            String(loc) => String(loc),
            Str(loc, v) => Str(loc, v),
            Number(loc) => Number(loc),
            Num(loc, v) => Num(loc, v),
            BigInt(loc) => BigInt(loc),
            Big(loc, v) => Big(loc, v),
            Row(loc) => Row(loc),
            Access(loc, n) => Access(loc, n),
            Find(loc, i, f) => Find(loc, i, f),
        })
    }

    fn self_referencing_fn(&mut self, name: &Var, f: Expr) -> Result<Expr, Error> {
        self.insert(name);
        self.expr(f)
    }
}
