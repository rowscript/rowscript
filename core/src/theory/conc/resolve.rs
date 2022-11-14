use std::collections::HashMap;

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
    r: HashMap<String, LocalVar>,
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
            if let Some(old) = self.r.insert(p.var.name.to_owned(), p.var.to_owned()) {
                recoverable.push(old);
            } else {
                removable.push(p.var.to_owned());
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
            self.r.insert(x.name.to_owned(), x);
        }

        Ok(d)
    }

    fn body(&mut self, d: Def<Expr>) -> Result<Def<Expr>, Error> {
        todo!()
    }

    fn bodied(&mut self, e: Box<Expr>, vars: &[LocalVar]) -> Result<Box<Expr>, Error> {
        let mut olds: Vec<Option<LocalVar>> = Default::default();

        for v in vars {
            olds.push(self.r.insert(v.name.to_owned(), v.to_owned()));
        }

        let ret = self.expr(e)?;

        for i in 0..vars.len() {
            let old = olds.get(i).unwrap();
            let var = vars.get(i).unwrap();
            if let Some(v) = old {
                self.r.insert(v.name.to_owned(), v.to_owned());
            } else {
                self.r.remove(&var.name.to_owned());
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
                if let Some(v) = self.r.get(&r.name) {
                    Resolved(loc, v.to_owned())
                } else {
                    return Err(UnresolvedVar(self.file.to_string(), loc, r));
                }
            }
            Let(loc, x, typ, a, b) => todo!(),
            Pi(loc, p, b) => {
                let var = p.var.to_owned();
                Pi(loc, self.param(p)?, self.bodied(b, &[var])?)
            }
            TupledLam(loc, vs, _) => todo!(),
            App(loc, f, x) => App(loc, self.expr(f)?, self.expr(x)?),
            Sigma(loc, p, b) => {
                let var = p.var.to_owned();
                Sigma(loc, self.param(p)?, self.bodied(b, &[var])?)
            }
            Tuple(loc, a, b) => Tuple(loc, self.expr(a)?, self.expr(b)?),
            TupleLet(loc, x, y, a, b) => {
                let vx = x.to_owned();
                let vy = y.to_owned();
                TupleLet(loc, x, y, self.expr(a)?, self.bodied(b, &[vx, vy])?)
            }
            UnitLet(loc, a, b) => UnitLet(loc, self.expr(a)?, self.expr(b)?),
            If(loc, p, t, e) => If(loc, self.expr(p)?, self.expr(t)?, self.expr(e)?),
            e => e,
        }))
    }
}