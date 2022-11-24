use std::collections::HashMap;
use std::rc::Rc;

use crate::theory::abs::def::Body::Fun;
use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::theory::{LocalVar, Param};
use crate::Error;
use crate::Error::UnresolvedVar;

pub struct Resolver(HashMap<Rc<String>, LocalVar>);

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
            if let Some(old) = self.0.insert(p.var.name.clone(), p.var.clone()) {
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
            self.0.remove(&x.name);
        }
        for x in recoverable {
            self.0.insert(x.name.clone(), x);
        }

        Ok(d)
    }

    fn body(&mut self, d: Def<Expr>) -> Result<Def<Expr>, Error> {
        // TODO: Self-referencing definition.
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
            olds.push(self.0.insert(v.name.clone(), v.clone()));
        }

        let ret = self.expr(e)?;

        for i in 0..vars.len() {
            let old = olds.get(i).unwrap();
            let var = vars.get(i).unwrap();
            if let Some(v) = old {
                self.0.insert(v.name.clone(), v.clone());
            } else {
                self.0.remove(&var.name.as_str().to_string());
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
                if let Some(v) = self.0.get(r.name.as_ref()) {
                    Resolved(loc, v.clone())
                } else {
                    return Err(UnresolvedVar(loc));
                }
            }
            Let(loc, x, typ, a, b) => {
                let b = self.bodied(b, &[&x])?;
                Let(
                    loc,
                    x,
                    if let Some(ty) = typ {
                        Some(self.expr(ty)?)
                    } else {
                        None
                    },
                    self.expr(a)?,
                    b,
                )
            }
            Pi(loc, p, b) => {
                let b = self.bodied(b, &[&p.var])?;
                Pi(loc, self.param(p)?, b)
            }
            TupledLam(loc, vars, b) => {
                let mut untupled_vars: Vec<Expr> = vec![Unresolved(loc, LocalVar::tupled())];
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
                let desugared = Box::new(Lam(loc, LocalVar::unbound(), desugared_body));
                *self.expr(desugared)?
            }
            Lam(loc, v, b) => {
                let b = self.bodied(b, &[&v])?;
                Lam(loc, v, b)
            }
            App(loc, f, x) => App(loc, self.expr(f)?, self.expr(x)?),
            Sigma(loc, p, b) => {
                let b = self.bodied(b, &[&p.var])?;
                Sigma(loc, self.param(p)?, b)
            }
            Tuple(loc, a, b) => Tuple(loc, self.expr(a)?, self.expr(b)?),
            TupleLet(loc, x, y, a, b) => {
                let b = self.bodied(b, &[&x, &y])?;
                TupleLet(loc, x, y, self.expr(a)?, b)
            }
            UnitLet(loc, a, b) => UnitLet(loc, self.expr(a)?, self.expr(b)?),
            If(loc, p, t, e) => If(loc, self.expr(p)?, self.expr(t)?, self.expr(e)?),
            e => e,
        }))
    }
}
