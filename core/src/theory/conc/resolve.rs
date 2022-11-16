use std::collections::HashMap;
use std::rc::Rc;

use crate::theory::abs::def::Body::Fun;
use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::theory::conc::data::Expr::{
    App, If, Let, Pi, Resolved, Sigma, Tuple, TupleLet, TupledLam, UnitLet, Unresolved,
};
use crate::theory::{LocalVar, Param};
use crate::Error::UnresolvedVar;
use crate::{Driver, Error};

pub struct Resolver<'a> {
    file: &'a str,
    r: HashMap<Rc<String>, LocalVar>,
}

impl<'a> From<Driver<'a>> for Resolver<'a> {
    fn from(d: Driver<'a>) -> Self {
        Self {
            file: d.file,
            r: Default::default(),
        }
    }
}

impl<'a> Resolver<'a> {
    pub fn def(&mut self, mut d: Def<Expr>) -> Result<Def<Expr>, Error> {
        let mut recoverable: Vec<LocalVar> = Default::default();
        let mut removable: Vec<LocalVar> = Default::default();

        let mut tele: Vec<Param<Expr>> = Default::default();
        for p in d.tele {
            if let Some(old) = self.r.insert(p.var.name.clone(), p.var.clone()) {
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
            self.r.remove(&x.name);
        }
        for x in recoverable {
            self.r.insert(x.name.clone(), x);
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

    fn bodied(&mut self, e: Box<Expr>, vars: &[LocalVar]) -> Result<Box<Expr>, Error> {
        let mut olds: Vec<Option<LocalVar>> = Default::default();

        for v in vars {
            olds.push(self.r.insert(v.name.clone(), v.clone()));
        }

        let ret = self.expr(e)?;

        for i in 0..vars.len() {
            let old = olds.get(i).unwrap();
            let var = vars.get(i).unwrap();
            if let Some(v) = old {
                self.r.insert(v.name.clone(), v.clone());
            } else {
                self.r.remove(&var.name.as_str().to_string());
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
        Ok(Box::new(match *e {
            Unresolved(loc, r) => {
                if let Some(v) = self.r.get(r.name.as_ref()) {
                    Resolved(loc, v.clone())
                } else {
                    return Err(UnresolvedVar(self.file.to_string(), loc, r));
                }
            }
            Let(loc, x, typ, a, b) => {
                let v = x.clone();
                Let(
                    loc,
                    x,
                    if let Some(ty) = typ {
                        Some(self.expr(ty)?)
                    } else {
                        None
                    },
                    self.expr(a)?,
                    self.bodied(b, &[v])?,
                )
            }
            Pi(loc, p, b) => {
                let var = p.var.clone();
                Pi(loc, self.param(p)?, self.bodied(b, &[var])?)
            }
            TupledLam(loc, vs, b) => {
                let vars = vs.clone();
                TupledLam(loc, vs, self.bodied(b, vars.as_slice())?)
            }
            App(loc, f, x) => App(loc, self.expr(f)?, self.expr(x)?),
            Sigma(loc, p, b) => {
                let var = p.var.clone();
                Sigma(loc, self.param(p)?, self.bodied(b, &[var])?)
            }
            Tuple(loc, a, b) => Tuple(loc, self.expr(a)?, self.expr(b)?),
            TupleLet(loc, x, y, a, b) => {
                let vx = x.clone();
                let vy = y.clone();
                TupleLet(loc, x, y, self.expr(a)?, self.bodied(b, &[vx, vy])?)
            }
            UnitLet(loc, a, b) => UnitLet(loc, self.expr(a)?, self.expr(b)?),
            If(loc, p, t, e) => If(loc, self.expr(p)?, self.expr(t)?, self.expr(e)?),
            e => e,
        }))
    }
}
