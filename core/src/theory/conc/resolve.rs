use std::collections::HashMap;

use crate::theory::abs::def::{Body, InstanceBody};
use crate::theory::abs::def::{ClassMembers, Def};
use crate::theory::conc::data::Expr::Unresolved;
use crate::theory::conc::data::{Catch, Expr};
use crate::theory::conc::load::{Import, ImportedDefs, Loaded};
use crate::theory::VarKind::{Inside, Outside, Reserved};
use crate::theory::{
    Loc, NameMap, Param, RawNameSet, ResolvedVar, Tele, Var, TUPLED, UNBOUND, UNTUPLED_ENDS,
};
use crate::Error::{DuplicateName, NonAnonVariadicDef, UnresolvedVar};
use crate::{maybe_grow, print_err, Error, File};

pub struct Resolver<'a> {
    ubiquitous: &'a NameMap,
    loaded: &'a Loaded,
    locals: NameMap,
    imported: NameMap,
    globals: NameMap,
    is_def_anon_variadic: bool,
}

impl<'a> Resolver<'a> {
    pub fn new(ubiquitous: &'a NameMap, loaded: &'a Loaded) -> Self {
        Self {
            ubiquitous,
            loaded,
            locals: Default::default(),
            imported: Default::default(),
            globals: Default::default(),
            is_def_anon_variadic: false,
        }
    }

    pub fn files(&mut self, mut files: Vec<File<Expr>>) -> Result<Box<[File<Expr>]>, Error> {
        for f in &mut files {
            for d in &mut f.defs {
                let name_str = d.name.as_str();
                if name_str != UNBOUND {
                    if let Some(rv) = self.ubiquitous.get(name_str) {
                        if !matches!(rv.0, Reserved) {
                            return Err(print_err(DuplicateName(d.loc), &f.path));
                        }
                        // Use the reserved definition name.
                        d.name = rv.1.clone();
                    }
                }
                self.insert_global(d.loc, d.name.clone())
                    .map_err(|e| print_err(e, &f.path))?;
            }
        }
        files.into_iter().map(|d| self.file(d)).collect()
    }

    fn file(&mut self, mut file: File<Expr>) -> Result<File<Expr>, Error> {
        self.imports(&file.imports)?;
        file.defs = file
            .defs
            .into_vec()
            .into_iter()
            .map(|d| self.def(d))
            .collect::<Result<_, _>>()
            .map_err(|e| print_err(e, &file.path))?;
        Ok(file)
    }

    fn imports(&mut self, imports: &[Import]) -> Result<(), Error> {
        use ImportedDefs::*;
        for Import { module, defs, .. } in imports {
            match defs {
                Unqualified(xs) => {
                    for (loc, name) in xs {
                        match self.loaded.get(module, name) {
                            Some(v) => self.insert_imported(v.clone()),
                            None => return Err(UnresolvedVar(*loc)),
                        };
                    }
                }
                _ => continue,
            }
        }
        Ok(())
    }

    fn def(&mut self, mut d: Def<Expr>) -> Result<Def<Expr>, Error> {
        use Body::*;

        self.is_def_anon_variadic = false;

        match &d.body {
            Method { associated, .. } | Class { associated, .. } => {
                for (raw, v) in associated.iter() {
                    self.locals
                        .insert(raw.clone(), ResolvedVar(Inside, v.clone()));
                }
            }
            _ => {}
        }

        let mut tele = Tele::default();
        for p in d.tele {
            if matches!(p.typ.as_ref(), Expr::AnonVarargs(..)) {
                self.is_def_anon_variadic = true;
            }
            self.insert_local(p.var.clone());
            tele.push(Param {
                var: p.var,
                info: p.info,
                typ: self.expr(p.typ)?,
            });
        }
        d.tele = tele;
        d.eff = self.expr(d.eff)?;
        d.ret = self.expr(d.ret)?;
        d.body = match d.body {
            Fn(f) => Fn(self.expr(f)?),
            Postulate => Postulate,
            Alias { ty, implements } => Alias {
                ty: self.expr(ty)?,
                implements: implements.map(|t| self.expr(t)).transpose()?,
            },
            Constant(anno, f) => Constant(anno, self.expr(f)?),
            Verify(a) => Verify(self.expr(a)?),

            Interface {
                is_capability,
                fns,
                instances,
                implements,
            } => Interface {
                is_capability,
                fns,
                instances,
                implements,
            },
            InterfaceFn(i) => InterfaceFn(i),
            Instance(body) => {
                let loc = d.loc;
                let i = self
                    .expr(Box::new(Unresolved(loc, None, body.i)))?
                    .resolved();
                let inst = self.expr(body.inst)?;
                let mut fns = HashMap::default();
                for (i_fn, inst_fn) in body.fns {
                    fns.insert(
                        self.expr(Box::new(Unresolved(loc, None, i_fn)))?.resolved(),
                        inst_fn,
                    );
                }
                Instance(Box::new(InstanceBody { i, inst, fns }))
            }
            InstanceFn(f) => InstanceFn(self.expr(f)?),
            ImplementsFn { name, f } => ImplementsFn {
                name,
                f: self.expr(f)?,
            },

            Class {
                ctor,
                associated,
                members,
                methods,
            } => {
                let members = match members {
                    ClassMembers::Wrapper(ty) => ClassMembers::Wrapper(self.expr(ty)?),
                    ClassMembers::Members(m) => {
                        let mut names = RawNameSet::default();
                        let mut resolved_members = Vec::default();
                        for (loc, id, typ) in m {
                            names.raw(loc, id.clone())?;
                            resolved_members.push((loc, id, *self.expr(Box::new(typ))?));
                        }
                        ClassMembers::Members(resolved_members)
                    }
                };
                Class {
                    ctor,
                    associated,
                    members,
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

        self.clear_locals();

        Ok(d)
    }

    fn get(&self, v: &Var) -> Option<&ResolvedVar> {
        let k = v.as_str();
        self.locals
            .get(k)
            .or_else(|| self.locals.get(v.bind_let().as_str()))
            .or_else(|| self.globals.get(k))
            .or_else(|| self.imported.get(k))
            .or_else(|| self.ubiquitous.get(k))
    }

    fn insert_local(&mut self, v: Var) -> Option<ResolvedVar> {
        self.locals.insert(v.to_string(), ResolvedVar(Inside, v))
    }

    fn insert_imported(&mut self, v: Var) {
        self.imported.insert(v.to_string(), ResolvedVar(Outside, v));
    }

    fn insert_global(&mut self, loc: Loc, v: Var) -> Result<(), Error> {
        match self.globals.insert(v.to_string(), ResolvedVar(Inside, v)) {
            Some(old) if old.1.as_str() != UNBOUND => Err(DuplicateName(loc)),
            _ => Ok(()),
        }
    }

    fn remove_local(&mut self, v: &Var) {
        self.locals.remove(v.as_str());
    }

    fn clear_locals(&mut self) {
        self.locals.clear();
    }

    fn bodied<const N: usize>(
        &mut self,
        vars: [&Var; N],
        e: Box<Expr>,
    ) -> Result<Box<Expr>, Error> {
        let olds = vars.map(|v| self.insert_local(v.clone()));

        let ret = self.expr(e)?;

        for (old, var) in olds.into_iter().zip(vars.into_iter()) {
            match old {
                Some(v) => {
                    self.locals.insert(v.1.to_string(), v);
                }
                None => self.remove_local(var),
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
        maybe_grow(move || self.expr_impl(e))
    }

    fn expr_impl(
        &mut self,
        #[allow(clippy::boxed_local)] e: Box<Expr>,
    ) -> Result<Box<Expr>, Error> {
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
                                Reserved | Inside => Resolved(loc, v),
                                Outside => Imported(loc, v),
                            }
                        }
                        _ => return Err(UnresolvedVar(loc)),
                    }
                }
            },
            Const(loc, x, typ, a, b) => {
                let b = self.bodied([&x], b)?;
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
                    if self.locals.contains_key(x.as_str()) {
                        return Err(DuplicateName(loc));
                    }
                }
                let b = self.bodied([&x], b)?;
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
            Update(loc, x, a, b) => match self.locals.get(x.bind_let().as_str()) {
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
                let b = self.bodied([&p.var], b)?;
                Pi(loc, self.param(p)?, b)
            }
            TupledLam(loc, vars, b) => {
                let x = Var::tupled();
                let wrapped = Expr::wrap_tuple_binds(loc, x.clone(), vars, *b);
                let desugared = Lam(loc, x.clone(), Box::new(wrapped));
                *self.bodied([&x], Box::new(desugared))?
            }
            Lam(loc, x, b) => {
                let b = self.bodied([&x], b)?;
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
                let b = self.bodied([&p.var], b)?;
                Sigma(loc, self.param(p)?, b)
            }
            Tuple(loc, a, b) => Tuple(loc, self.expr(a)?, self.expr(b)?),
            TupleBind(loc, x, y, a, b) => {
                let b = self.bodied([&x, &y], b)?;
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
            At(loc, a, k) => At(loc, self.expr(a)?, self.expr(k)?),
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
            Cat(loc, a, b) => Cat(loc, self.expr(a)?, self.expr(b)?),
            Downcast(loc, a) => Downcast(loc, self.expr(a)?),
            Enum(loc, a) => Enum(loc, self.expr(a)?),
            Variant(loc, n, a) => Variant(loc, n, self.expr(a)?),
            Upcast(loc, a) => Upcast(loc, self.expr(a)?),
            Switch(loc, a, cs, d) => {
                let mut names = RawNameSet::default();
                let mut new = Vec::default();
                for (n, v, e) in cs {
                    names.raw(loc, n.clone())?;
                    let e = self.bodied([&v], Box::new(e))?;
                    new.push((n, v, *e));
                }
                let d = match d {
                    Some((v, e)) => {
                        let e = self.bodied([&v], Box::new(*e))?;
                        Some((v, e))
                    }
                    None => None,
                };
                Switch(loc, self.expr(a)?, new, d)
            }
            Unionify(loc, a) => Unionify(loc, self.expr(a)?),
            Union(loc, a, b) => Union(loc, self.expr(a)?, self.expr(b)?),
            Instanceof(loc, a) => Instanceof(loc, self.expr(a)?),
            Varargs(loc, a) => Varargs(loc, self.expr(a)?),
            AnonVarargs(loc, a) => AnonVarargs(loc, self.expr(a)?),
            Spread(loc, a) => Spread(loc, self.expr(a)?),
            AnonSpread(loc) => Resolved(
                loc,
                match self.locals.get(UNTUPLED_ENDS) {
                    Some(v) => v,
                    None if self.is_def_anon_variadic => self.locals.get(TUPLED).unwrap(),
                    _ => return Err(NonAnonVariadicDef(loc)),
                }
                .1
                .clone(),
            ),
            Typeof(loc, a) => Typeof(loc, self.expr(a)?),
            Keyof(loc, a) => Keyof(loc, self.expr(a)?),
            Effect(loc, a) => {
                let mut resolved = Vec::default();
                for e in a {
                    resolved.push(*self.expr(Box::new(e))?);
                }
                Effect(loc, resolved)
            }
            EmitAsync(loc, a) => EmitAsync(loc, self.expr(a)?),
            TryCatch(loc, b, catches) => {
                let body = self.expr(b)?;
                let mut resolved = Vec::default();
                for catch in catches {
                    let i = *self.expr(Box::new(catch.i))?;
                    let inst_ty = *self.expr(Box::new(catch.inst_ty))?;
                    let mut inst_fns = Vec::default();
                    for (name, d) in catch.inst_fns {
                        inst_fns.push((name, self.def(d)?));
                    }
                    resolved.push(Catch {
                        i,
                        inst_ty,
                        inst_fns,
                    });
                }
                TryCatch(loc, body, resolved)
            }

            e => e,
        }))
    }
}
