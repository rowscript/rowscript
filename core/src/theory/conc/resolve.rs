use std::collections::HashMap;

use crate::theory::abs::def::Body::Fun;
use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::theory::{LocalVar, Param};
use crate::Error;
use crate::Error::UnresolvedVar;

pub struct Resolver(HashMap<String, LocalVar>);

impl Default for Resolver {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl Resolver {
    pub fn def(&mut self, mut d: Def<Expr>) -> Result<Def<Expr>, Error> {
        let mut recoverable: Vec<LocalVar> = Default::default();
        let mut removable: Vec<LocalVar> = Default::default();

        let mut tele: Vec<Param<Expr>> = Default::default();
        for p in d.tele {
            if let Some(old) = self.0.insert(p.var.to_string(), p.var.clone()) {
                recoverable.push(old);
            } else {
                removable.push(p.var.clone());
            }
            tele.push(Param {
                var: p.var,
                typ: self.expr(p.typ)?,
            });
        }
        d.tele = tele;

        d = self.body(d)?;

        for x in removable {
            self.0.remove(x.as_str());
        }
        for x in recoverable {
            self.0.insert(x.to_string(), x);
        }

        Ok(d)
    }

    fn body(&mut self, d: Def<Expr>) -> Result<Def<Expr>, Error> {
        // TODO: Self-referencing definition.
        let name = d.name.clone();
        self.0.insert(name.to_string(), name);
        Ok(Def {
            loc: d.loc,
            name: d.name,
            tele: d.tele,
            ret: self.expr(d.ret)?,
            body: match d.body {
                Fun(f) => Fun(self.expr(f)?),
            },
        })
    }

    fn bodied(&mut self, e: Box<Expr>, vars: &[&LocalVar]) -> Result<Box<Expr>, Error> {
        let mut olds: Vec<Option<LocalVar>> = Default::default();

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
                    self.bodied(b, &[&vx])?,
                )
            }
            Pi(loc, p, b) => {
                let x = p.var.clone();
                Pi(loc, self.param(p)?, self.bodied(b, &[&x])?)
            }
            TupledLam(loc, vars, b) => {
                let untupled = LocalVar::tupled();
                let mut untupled_vars: Vec<Expr> = vec![Unresolved(loc, untupled.clone())];
                for x in vars.iter() {
                    untupled_vars.push(match x {
                        Unresolved(l, r) => Unresolved(l.clone(), r.untupled_right()),
                        _ => unreachable!(),
                    });
                }
                let mut desugared_body = b;
                for (i, v) in vars.into_iter().rev().enumerate() {
                    let (loc, lhs, rhs) = match (v, untupled_vars.get(i + 1).unwrap()) {
                        (Unresolved(loc, lhs), Unresolved(_, rhs)) => (loc, lhs, rhs),
                        _ => unreachable!(),
                    };
                    let tm = untupled_vars.get(i).unwrap();
                    desugared_body = Box::new(TupleLet(
                        loc,
                        lhs,
                        rhs.clone(),
                        Box::new(tm.clone()),
                        desugared_body,
                    ));
                }
                let desugared = Box::new(Lam(loc, LocalVar::tupled(), desugared_body));
                *self.bodied(desugared, &[&untupled])?
            }
            Lam(loc, x, b) => {
                let vx = x.clone();
                Lam(loc, x, self.bodied(b, &[&vx])?)
            }
            App(loc, f, x) => App(loc, self.expr(f)?, self.expr(x)?),
            Sigma(loc, p, b) => {
                let x = p.var.clone();
                Sigma(loc, self.param(p)?, self.bodied(b, &[&x])?)
            }
            Tuple(loc, a, b) => Tuple(loc, self.expr(a)?, self.expr(b)?),
            TupleLet(loc, x, y, a, b) => {
                let vx = x.clone();
                let vy = y.clone();
                TupleLet(loc, x, y, self.expr(a)?, self.bodied(b, &[&vx, &vy])?)
            }
            UnitLet(loc, a, b) => UnitLet(loc, self.expr(a)?, self.expr(b)?),
            If(loc, p, t, e) => If(loc, self.expr(p)?, self.expr(t)?, self.expr(e)?),
            e => e,
        }))
    }
}
