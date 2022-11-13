use std::collections::HashMap;

use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::theory::conc::data::Expr::{
    App, IfThenElse, Let, Pair, PairLet, Pi, Resolved, Sigma, TupledLam, UnitLet, Unresolved,
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

    fn expr(&self, e: Box<Expr>) -> Result<Box<Expr>, Error> {
        Ok(Box::new(match *e {
            Unresolved(loc, r) => {
                if let Some(v) = self.r.get(&r.name) {
                    Resolved(loc, v.to_owned())
                } else {
                    return Err(UnresolvedVar(self.file.to_string(), loc, r));
                }
            }
            Let(_, _, _, _) => todo!(),
            Pi(_, _, _) => todo!(),
            TupledLam(_, _, _) => todo!(),
            App(_, _, _) => todo!(),
            Sigma(_, _, _) => todo!(),
            Pair(_, _, _) => todo!(),
            PairLet(_, _, _, _, _) => todo!(),
            UnitLet(_, _, _) => todo!(),
            IfThenElse(_, _, _, _) => todo!(),
            e => e,
        }))
    }
}
