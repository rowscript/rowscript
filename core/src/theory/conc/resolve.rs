use std::collections::HashMap;

use crate::theory::abs::def::Def;
use crate::theory::abs::def::{Body, ImplementsBody};
use crate::theory::conc::data::Expr;
use crate::theory::conc::data::Expr::Unresolved;
use crate::theory::conc::load::{Import, ImportedDefs, Loaded};
use crate::theory::{NameMap, Param, RawNameSet, ResolvedVar, Tele, Var, VarKind, UNBOUND};
use crate::Error;
use crate::Error::UnresolvedVar;

pub struct Resolver<'a> {
    ubiquitous: &'a NameMap,
    loaded: &'a Loaded,
    names: NameMap,
}

impl<'a> Resolver<'a> {
    pub fn new(ubiquitous: &'a NameMap, loaded: &'a Loaded) -> Self {
        Self {
            ubiquitous,
            loaded,
            names: Default::default(),
        }
    }

    pub fn file(
        &mut self,
        imports: &mut Vec<Import>,
        defs: Vec<Def<Expr>>,
    ) -> Result<Vec<Def<Expr>>, Error> {
        let mut names = RawNameSet::default();
        self.imports(&mut names, imports)?;
        self.defs(&mut names, defs)
    }

    fn imports(&mut self, names: &mut RawNameSet, imports: &mut Vec<Import>) -> Result<(), Error> {
        use ImportedDefs::*;
        for Import { loc, module, defs } in imports {
            match defs {
                Unqualified(xs) => {
                    for (loc, name) in xs {
                        names.raw(*loc, name.clone())?;
                        match self.loaded.get(module, name) {
                            Some(v) => self.insert_imported(v),
                            None => return Err(UnresolvedVar(*loc)),
                        };
                    }
                }
                Qualified => names.raw(*loc, module.to_string())?,
                Loaded => continue,
            }
        }
        Ok(())
    }

    fn defs(
        &mut self,
        names: &mut RawNameSet,
        defs: Vec<Def<Expr>>,
    ) -> Result<Vec<Def<Expr>>, Error> {
        let mut ret = Vec::default();
        for d in defs {
            if d.name.as_str() != UNBOUND {
                names.var(d.loc, &d.name)?;
            }
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
            Fn(f) => Fn(self.self_referencing_fn(&d.name, f)?),
            Postulate => Postulate,
            Alias(t) => Alias(self.expr(t)?),
            Const(anno, f) => Const(anno, self.expr(f)?),

            Interface { fns, ims } => Interface { fns, ims },
            Implements(body) => {
                let loc = d.loc;
                let i = self.expr(Unresolved(loc, None, body.i.0))?.resolved();
                let im = self.expr(*body.i.1)?;
                let mut fns = HashMap::default();
                for (i_fn, im_fn) in body.fns {
                    fns.insert(
                        self.expr(Unresolved(loc, None, i_fn))?.resolved(),
                        self.expr(Unresolved(loc, None, im_fn))?.resolved(),
                    );
                }
                Implements(Box::new(ImplementsBody {
                    i: (i, Box::new(im)),
                    fns,
                }))
            }
            ImplementsFn(f) => ImplementsFn(self.expr(f)?), // FIXME: currently cannot be recursive
            Findable(i) => Findable(i),

            Class(ms, meths) => {
                let mut names = RawNameSet::default();
                let mut resolved = Vec::default();
                for (loc, id, typ) in ms {
                    names.raw(loc, id.clone())?;
                    resolved.push((loc, id, self.expr(typ)?));
                }
                Class(resolved, meths)
            }
            Method(t, f) => Method(t, self.expr(f)?),

            Undefined => unreachable!(),
            Meta(_, _) => unreachable!(),
        };

        for x in removable {
            self.remove(&x);
        }
        for x in recoverable {
            self.insert_resolved(x);
        }
        self.insert(&d.name);

        Ok(d)
    }

    fn get(&self, v: &Var) -> Option<&ResolvedVar> {
        let k = v.as_str();
        self.names.get(k).or_else(|| self.ubiquitous.get(k))
    }

    fn insert(&mut self, v: &Var) -> Option<ResolvedVar> {
        self.names
            .insert(v.to_string(), ResolvedVar(VarKind::InModule, v.clone()))
    }

    fn insert_imported(&mut self, v: &Var) -> Option<ResolvedVar> {
        self.names
            .insert(v.to_string(), ResolvedVar(VarKind::Imported, v.clone()))
    }

    fn insert_resolved(&mut self, v: ResolvedVar) {
        self.names.insert(v.1.to_string(), v);
    }

    fn remove(&mut self, v: &Var) {
        self.names.remove(v.as_str());
    }

    fn bodied(&mut self, vars: &[&Var], e: Expr) -> Result<Expr, Error> {
        let mut olds = Vec::default();

        for &v in vars {
            olds.push(self.insert(v));
        }

        let ret = self.expr(e)?;

        for i in 0..vars.len() {
            match olds.get(i).unwrap() {
                Some(v) => self.insert_resolved(v.clone()),
                None => self.remove(vars.get(i).unwrap()),
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
            Unresolved(loc, m, r) => match m {
                Some(m) => match self.loaded.get(&m, &r.to_string()) {
                    Some(r) => Qualified(loc, m, r.clone()),
                    None => return Err(UnresolvedVar(loc)),
                },
                None => match self.get(&r) {
                    Some(v) => {
                        let k = v.0;
                        let v = v.1.clone();
                        match k {
                            VarKind::InModule => Resolved(loc, v),
                            VarKind::Imported => Imported(loc, v),
                        }
                    }
                    None => return Err(UnresolvedVar(loc)),
                },
            },
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
            While(loc, p, b, r) => While(
                loc,
                Box::new(self.expr(*p)?),
                Box::new(self.expr(*b)?),
                Box::new(self.expr(*r)?),
            ),
            Guard(loc, p, b, r) => Guard(
                loc,
                Box::new(self.expr(*p)?),
                Box::new(self.expr(*b)?),
                Box::new(self.expr(*r)?),
            ),
            Pi(loc, p, b) => {
                let b = self.bodied(&[&p.var], *b)?;
                Pi(loc, self.param(p)?, Box::new(b))
            }
            TupledLam(loc, vars, b) => {
                let x = Var::tupled();
                let wrapped = Box::new(Expr::wrap_tuple_lets(loc, &x, vars, *b));
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
            RevApp(loc, f, x) => {
                let unresolved = f.clone();
                match self.expr(*f) {
                    Ok(f) => RevApp(loc, Box::new(f), Box::new(self.expr(*x)?)),
                    Err(_) => RevApp(loc, unresolved, Box::new(self.expr(*x)?)),
                }
            }
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
            Arr(loc, xs) => {
                let mut resolved = Vec::default();
                for x in xs {
                    resolved.push(self.expr(x)?);
                }
                Arr(loc, resolved)
            }
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
            Constraint(loc, r) => Constraint(loc, Box::new(self.expr(*r)?)),
            ImplementsOf(loc, a) => ImplementsOf(loc, Box::new(self.expr(*a)?)),

            e => e,
        })
    }

    fn self_referencing_fn(&mut self, name: &Var, f: Expr) -> Result<Expr, Error> {
        self.insert(name);
        self.expr(f)
    }
}
