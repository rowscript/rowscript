use std::collections::HashMap;

use log::debug;

use crate::theory::abs::def::Def;
use crate::theory::abs::def::{Body, InstanceBody};
use crate::theory::conc::data::Expr;
use crate::theory::conc::data::Expr::Unresolved;
use crate::theory::conc::load::{Import, ImportedDefs, Loaded};
use crate::theory::{
    NameMap, Param, RawNameSet, ResolvedVar, Tele, Var, VarKind, TUPLED, UNBOUND, UNTUPLED_ENDS,
};
use crate::Error;
use crate::Error::{DuplicateName, NonAnonVariadicDef, UnresolvedVar};

pub struct Resolver<'a> {
    ubiquitous: &'a NameMap,
    loaded: &'a Loaded,
    names: NameMap,
    is_def_anon_variadic: bool,
}

impl<'a> Resolver<'a> {
    pub fn new(ubiquitous: &'a NameMap, loaded: &'a Loaded) -> Self {
        Self {
            ubiquitous,
            loaded,
            names: Default::default(),
            is_def_anon_variadic: Default::default(),
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
                if self.ubiquitous.contains_key(d.name.as_str()) {
                    return Err(DuplicateName(d.loc));
                }
                names.var(d.loc, &d.name)?;
            }
            let resolved = self.def(d)?;
            debug!(target: "resolve", "definition resolved successfully: {resolved}");
            ret.push(resolved);
        }
        Ok(ret)
    }

    fn def(&mut self, mut d: Def<Expr>) -> Result<Def<Expr>, Error> {
        use Body::*;

        self.is_def_anon_variadic = false;
        let mut recoverable = Vec::default();
        let mut removable = Vec::default();

        match &d.body {
            Method { associated, .. } | Class { associated, .. } => {
                for (raw, v) in associated.iter() {
                    let old = self
                        .names
                        .insert(raw.clone(), ResolvedVar(VarKind::InModule, v.clone()));
                    if let Some(old) = old {
                        recoverable.push(old);
                    } else {
                        removable.push(v.clone());
                    }
                }
            }
            _ => {}
        }

        let mut tele = Tele::default();
        for p in d.tele {
            if matches!(p.typ.as_ref(), Expr::AnonVarargs(..)) {
                self.is_def_anon_variadic = true;
            }
            if let Some(old) = self.insert(&p.var) {
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
        d.body = match d.body {
            Fn { is_async, f } => Fn {
                is_async,
                f: self.self_referencing_fn(&d.name, f)?,
            },
            Postulate => Postulate,
            Alias(t) => Alias(self.expr(t)?),
            Constant(anno, f) => Constant(anno, self.expr(f)?),
            Verify(a) => Verify(self.expr(a)?),

            Interface {
                fns,
                instances: ims,
            } => Interface {
                fns,
                instances: ims,
            },
            Instance(body) => {
                let loc = d.loc;
                let i = self
                    .expr(Box::new(Unresolved(loc, None, body.i.0)))?
                    .resolved();
                let inst = self.expr(body.i.1)?;
                let mut fns = HashMap::default();
                for (i_fn, inst_fn) in body.fns {
                    fns.insert(
                        self.expr(Box::new(Unresolved(loc, None, i_fn)))?.resolved(),
                        self.expr(Box::new(Unresolved(loc, None, inst_fn)))?
                            .resolved(),
                    );
                }
                Instance(Box::new(InstanceBody { i: (i, inst), fns }))
            }
            InstanceFn(f) => InstanceFn(self.expr(f)?), // FIXME: currently cannot be recursive
            Findable(i) => Findable(i),

            Class {
                ctor,
                associated,
                members,
                methods,
            } => {
                let mut names = RawNameSet::default();
                let mut resolved_members = Vec::default();
                for (loc, id, typ) in members {
                    names.raw(loc, id.clone())?;
                    resolved_members.push((loc, id, *self.expr(Box::new(typ))?));
                }
                Class {
                    ctor,
                    associated,
                    members: resolved_members,
                    methods,
                }
            }
            Associated(t) => Associated(self.expr(t)?),
            Method {
                class,
                associated,
                f,
            } => Method {
                class,
                associated,
                f: self.expr(f)?,
            },

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
        self.names
            .get(k)
            .or_else(|| self.names.get(v.bind_let().as_str()))
            .or_else(|| self.ubiquitous.get(k))
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

    fn bodied(&mut self, vars: &[&Var], e: Box<Expr>) -> Result<Box<Expr>, Error> {
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
            typ: self.expr(p.typ)?,
        })
    }

    fn expr(&mut self, #[allow(clippy::boxed_local)] e: Box<Expr>) -> Result<Box<Expr>, Error> {
        use Expr::*;
        Ok(Box::new(match *e {
            Unresolved(loc, m, r) => match m {
                Some(m) => match self.loaded.get(&m, &r.to_string()) {
                    Some(r) => Qualified(loc, m, r.clone()),
                    None => return Err(UnresolvedVar(loc)),
                },
                None => {
                    let bind = self.get(&r.bind_let());
                    let global = self.get(&r);
                    match (bind, global) {
                        (Some(v), _) | (_, Some(v)) => {
                            let k = v.0;
                            let v = v.1.clone();
                            match k {
                                VarKind::InModule => Resolved(loc, v),
                                VarKind::Imported => Imported(loc, v),
                            }
                        }
                        _ => return Err(UnresolvedVar(loc)),
                    }
                }
            },
            Const(loc, x, typ, a, b) => {
                let b = self.bodied(&[&x], b)?;
                Const(
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
            Let(loc, mut x, typ, a, b) => {
                if x.as_str() != UNBOUND {
                    x = x.bind_let();
                    if self.names.contains_key(x.as_str()) {
                        return Err(DuplicateName(loc));
                    }
                }
                let b = self.bodied(&[&x], b)?;
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
            Update(loc, x, a, b) => match self.names.get(x.bind_let().as_str()) {
                Some(x) => Update(loc, x.1.clone(), self.expr(a)?, self.expr(b)?),
                None => return Err(UnresolvedVar(loc)),
            },
            While(loc, p, b, r) => While(loc, self.expr(p)?, self.expr(b)?, self.expr(r)?),
            Fori(loc, b, r) => Fori(loc, self.expr(b)?, self.expr(r)?),
            Guard(loc, p, b, e, r) => Guard(
                loc,
                self.expr(p)?,
                self.expr(b)?,
                if let Some(e) = e {
                    Some(self.expr(e)?)
                } else {
                    None
                },
                self.expr(r)?,
            ),
            Return(loc, a) => Return(loc, self.expr(a)?),
            Pi(loc, p, b) => {
                let b = self.bodied(&[&p.var], b)?;
                Pi(loc, self.param(p)?, b)
            }
            TupledLam(loc, vars, b) => {
                let x = Var::tupled();
                let wrapped = Expr::wrap_tuple_binds(loc, x.clone(), vars, *b);
                let desugared = Lam(loc, x.clone(), Box::new(wrapped));
                *self.bodied(&[&x], Box::new(desugared))?
            }
            Lam(loc, x, b) => {
                let b = self.bodied(&[&x], b)?;
                Lam(loc, x, b)
            }
            App(loc, f, i, x) => App(loc, self.expr(f)?, i, self.expr(x)?),
            RevApp(loc, f, tys, x) => {
                let mut resolved_tys = Vec::default();
                for ty in tys {
                    resolved_tys.push(*self.expr(Box::new(ty))?);
                }

                let unresolved = f.clone();
                match self.expr(f) {
                    Ok(f) => RevApp(loc, f, resolved_tys, self.expr(x)?),
                    Err(_) => RevApp(loc, unresolved, resolved_tys, self.expr(x)?),
                }
            }
            Sigma(loc, p, b) => {
                let b = self.bodied(&[&p.var], b)?;
                Sigma(loc, self.param(p)?, b)
            }
            Tuple(loc, a, b) => Tuple(loc, self.expr(a)?, self.expr(b)?),
            TupleBind(loc, x, y, a, b) => {
                let b = self.bodied(&[&x, &y], b)?;
                TupleBind(loc, x, y, self.expr(a)?, b)
            }
            UnitBind(loc, a, b) => UnitBind(loc, self.expr(a)?, self.expr(b)?),
            If(loc, p, t, e) => If(loc, self.expr(p)?, self.expr(t)?, self.expr(e)?),
            Arr(loc, xs) => {
                let mut resolved = Vec::default();
                for x in xs {
                    resolved.push(*self.expr(Box::new(x))?);
                }
                Arr(loc, resolved)
            }
            Kv(loc, xs) => {
                let mut resolved = Vec::default();
                for (k, v) in xs {
                    resolved.push((*self.expr(Box::new(k))?, *self.expr(Box::new(v))?));
                }
                Kv(loc, resolved)
            }
            Associate(loc, a, n) => Associate(loc, self.expr(a)?, n),
            Fields(loc, fields) => {
                let mut names = RawNameSet::default();
                let mut resolved = Vec::default();
                for (f, typ) in fields {
                    names.raw(loc, f.clone())?;
                    resolved.push((f, *self.expr(Box::new(typ))?));
                }
                Fields(loc, resolved)
            }
            Combine(loc, a, b) => Combine(loc, self.expr(a)?, self.expr(b)?),
            RowOrd(loc, a, b) => RowOrd(loc, self.expr(a)?, self.expr(b)?),
            RowEq(loc, a, b) => RowEq(loc, self.expr(a)?, self.expr(b)?),
            Object(loc, a) => Object(loc, self.expr(a)?),
            Obj(loc, a) => Obj(loc, self.expr(a)?),
            Concat(loc, a, b) => Concat(loc, self.expr(a)?, self.expr(b)?),
            Downcast(loc, a) => Downcast(loc, self.expr(a)?),
            Enum(loc, a) => Enum(loc, self.expr(a)?),
            Variant(loc, n, a) => Variant(loc, n, self.expr(a)?),
            Upcast(loc, a) => Upcast(loc, self.expr(a)?),
            Switch(loc, a, cs, d) => {
                let mut names = RawNameSet::default();
                let mut new = Vec::default();
                for (n, v, e) in cs {
                    names.raw(loc, n.clone())?;
                    let e = self.bodied(&[&v], Box::new(e))?;
                    new.push((n, v, *e));
                }
                let d = match d {
                    Some((v, e)) => {
                        let e = self.bodied(&[&v], Box::new(*e))?;
                        Some((v, e))
                    }
                    None => None,
                };
                Switch(loc, self.expr(a)?, new, d)
            }
            Instanceof(loc, a) => Instanceof(loc, self.expr(a)?),
            Varargs(loc, a) => Varargs(loc, self.expr(a)?),
            AnonVarargs(loc, a) => AnonVarargs(loc, self.expr(a)?),
            Spread(loc, a) => Spread(loc, self.expr(a)?),
            AnonSpread(loc) => Resolved(
                loc,
                match self.names.get(UNTUPLED_ENDS) {
                    Some(v) => v,
                    None if self.is_def_anon_variadic => self.names.get(TUPLED).unwrap(),
                    _ => return Err(NonAnonVariadicDef(loc)),
                }
                .1
                .clone(),
            ),
            EmitAsync(loc, a) => EmitAsync(loc, self.expr(a)?),

            e => e,
        }))
    }

    fn self_referencing_fn(&mut self, name: &Var, f: Box<Expr>) -> Result<Box<Expr>, Error> {
        self.insert(name);
        self.expr(f)
    }
}
