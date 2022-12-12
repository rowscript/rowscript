use std::collections::HashMap;

use crate::theory::abs::def::Body;
use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::theory::{Param, RawNameSet, Tele, Var};
use crate::Error;
use crate::Error::{DuplicateField, UnresolvedVar};

#[derive(Default)]
pub struct Resolver(HashMap<String, Var>);

impl Resolver {
    pub fn def(&mut self, mut d: Def<Expr>) -> Result<Def<Expr>, Error> {
        use Body::*;

        let mut recoverable: Vec<Var> = Default::default();
        let mut removable: Vec<Var> = Default::default();

        if let Fun { local_holes, f: _ } = &d.body {
            for (_, v) in local_holes {
                self.0.insert(v.to_string(), v.clone());
                removable.push(v.clone());
            }
        }

        let mut tele: Tele<Expr> = Default::default();
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
        use Body::*;
        let name = d.name.clone();
        self.0.insert(name.to_string(), name);
        Ok(Def {
            loc: d.loc,
            name: d.name,
            tele: d.tele,
            ret: self.expr(d.ret)?,
            body: match d.body {
                Fun { local_holes, f } => Fun {
                    local_holes,
                    f: self.expr(f)?,
                },
                Postulate => Postulate,
                _ => unreachable!(),
            },
        })
    }

    fn bodied(&mut self, vars: &[&Var], e: Box<Expr>) -> Result<Box<Expr>, Error> {
        let mut olds: Vec<Option<Var>> = Default::default();

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
            RowHole(loc, r) => RowHole(loc, self.0.get(&*r.name).unwrap().clone()),
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
                let untupled = Var::tupled();
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
                let desugared = Box::new(Lam(loc, Var::tupled(), desugared_body));
                *self.bodied(&[&untupled], desugared)?
            }
            Lam(loc, x, b) => {
                let vx = x.clone();
                Lam(loc, x, self.bodied(&[&vx], b)?)
            }
            App(loc, f, x) => App(loc, self.expr(f)?, self.expr(x)?),
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
                    if !names.insert(f.clone()) {
                        return Err(DuplicateField(f, loc));
                    }
                    resolved.push((f, *self.expr(Box::new(typ))?));
                }
                Fields(loc, resolved)
            }
            Combine(loc, a, b) => Combine(loc, self.expr(a)?, self.expr(b)?),
            RowOrd(loc, a, d, b) => RowOrd(loc, self.expr(a)?, d, self.expr(b)?),
            RowEq(loc, a, b) => RowEq(loc, self.expr(a)?, self.expr(b)?),
            Object(loc, o) => Object(loc, self.expr(o)?),
            e => e,
        }))
    }
}
