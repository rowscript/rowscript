use std::collections::HashMap;

use crate::theory::abs::def::Body;
use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::theory::{Param, RawNameSet, Tele, Var};
use crate::Error;
use crate::Error::UnresolvedVar;

#[derive(Default)]
pub struct Resolver(HashMap<String, Var>);

impl Resolver {
    pub fn def(&mut self, mut d: Def<Expr>) -> Result<Def<Expr>, Error> {
        use Body::*;

        let mut recoverable = Vec::default();
        let mut removable = Vec::default();

        let mut tele = Tele::default();
        for p in d.tele {
            if let Some(old) = self.0.insert(p.var.to_string(), p.var.clone()) {
                recoverable.push(old);
            } else {
                removable.push(p.var.clone());
            }
            tele.push(Param {
                var: p.var,
                info: p.info,
                typ: self.expr(p.typ)?,
            });
        }
        d.tele = tele;
        d.ret = self.expr(d.ret)?;

        let name = d.name.clone();
        self.0.insert(name.to_string(), name);
        d.body = match d.body {
            Fun(f) => Fun(self.expr(f)?),
            Postulate => Postulate,
            Alias(t) => Alias(self.expr(t)?),
            _ => unreachable!(),
        };

        for x in removable {
            self.0.remove(x.as_str());
        }
        for x in recoverable {
            self.0.insert(x.to_string(), x);
        }

        Ok(d)
    }

    fn bodied(&mut self, vars: &[&Var], e: Box<Expr>) -> Result<Box<Expr>, Error> {
        let mut olds = Vec::default();

        for &v in vars {
            olds.push(self.0.insert(v.to_string(), v.clone()));
        }

        let ret = self.expr(e)?;

        for i in 0..vars.len() {
            let old = olds.get(i).unwrap();
            if let Some(v) = old {
                self.0.insert(v.to_string(), v.clone());
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
            typ: self.expr(p.typ)?,
        })
    }

    fn expr(&mut self, e: Box<Expr>) -> Result<Box<Expr>, Error> {
        use Expr::*;
        Ok(Box::new(match *e {
            Unresolved(loc, r) => {
                if let Some(v) = self.0.get(&*r.name) {
                    Resolved(loc, v.clone())
                } else {
                    return Err(UnresolvedVar(loc));
                }
            }
            Let(loc, x, typ, a, b) => {
                let vx = x.clone();
                Let(
                    loc,
                    x,
                    if let Some(ty) = typ {
                        Some(self.expr(ty)?)
                    } else {
                        None
                    },
                    self.expr(a)?,
                    self.bodied(&[&vx], b)?,
                )
            }
            Pi(loc, p, b) => {
                let x = p.var.clone();
                Pi(loc, self.param(p)?, self.bodied(&[&x], b)?)
            }
            TupledLam(loc, vars, b) => {
                let x = Var::tupled();
                let wrapped = Expr::wrap_tuple_lets(loc, &x, vars, b);
                let desugared = Box::new(Lam(loc, x.clone(), wrapped));
                *self.bodied(&[&x], desugared)?
            }
            Lam(loc, x, b) => {
                let vx = x.clone();
                Lam(loc, x, self.bodied(&[&vx], b)?)
            }
            App(loc, f, i, x) => App(loc, self.expr(f)?, i, self.expr(x)?),
            Sigma(loc, p, b) => {
                let x = p.var.clone();
                Sigma(loc, self.param(p)?, self.bodied(&[&x], b)?)
            }
            Tuple(loc, a, b) => Tuple(loc, self.expr(a)?, self.expr(b)?),
            TupleLet(loc, x, y, a, b) => {
                let vx = x.clone();
                let vy = y.clone();
                TupleLet(loc, x, y, self.expr(a)?, self.bodied(&[&vx, &vy], b)?)
            }
            UnitLet(loc, a, b) => UnitLet(loc, self.expr(a)?, self.expr(b)?),
            If(loc, p, t, e) => If(loc, self.expr(p)?, self.expr(t)?, self.expr(e)?),
            Fields(loc, fields) => {
                let mut names = RawNameSet::default();
                let mut resolved = Vec::default();
                for (f, typ) in fields {
                    names.raw(loc, &f)?;
                    resolved.push((f, *self.expr(Box::new(typ))?));
                }
                Fields(loc, resolved)
            }
            Combine(loc, a, b) => Combine(loc, self.expr(a)?, self.expr(b)?),
            RowOrd(loc, a, d, b) => RowOrd(loc, self.expr(a)?, d, self.expr(b)?),
            RowEq(loc, a, b) => RowEq(loc, self.expr(a)?, self.expr(b)?),
            Object(loc, a) => Object(loc, self.expr(a)?),
            Obj(loc, a) => Obj(loc, self.expr(a)?),
            Concat(loc, a, b) => Concat(loc, self.expr(a)?, self.expr(b)?),
            Downcast(loc, a) => Downcast(loc, self.expr(a)?),
            Enum(loc, a) => Enum(loc, self.expr(a)?),
            Variant(loc, n, a) => Variant(loc, n, self.expr(a)?),
            Upcast(loc, a) => Upcast(loc, self.expr(a)?),
            Switch(loc, a, cs) => {
                let mut names = RawNameSet::default();
                let mut new = Vec::default();
                for (n, v, e) in cs {
                    names.raw(loc, &n)?;
                    let e = *self.bodied(&[&v], Box::new(e))?;
                    new.push((n, v, e));
                }
                Switch(loc, self.expr(a)?, new)
            }

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
            RowSat(loc) => RowSat(loc),
            RowRefl(loc) => RowRefl(loc),
            Access(loc, n) => Access(loc, n),
        }))
    }
}
