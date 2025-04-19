use std::collections::{HashMap, HashSet};
use std::ops::Not;

use log::{debug, trace};
use serde_json::Value;
use ustr::{Ustr, UstrMap};

use crate::Error::{
    ClassMethodNotImplemented, ExpectedInterface, ExpectedReflectable, FieldsNonExtendable,
    NonExhaustive, UnresolvedField, UnresolvedInstance, UnsatisfiedConstraint,
};

use crate::theory::abs::data::{CaseDefault, CaseMap, FieldMap, PartialClass, Term};
use crate::theory::abs::def::{Body, Rho, Sigma};
use crate::theory::abs::inline::noinline;
use crate::theory::abs::unify::Unifier;
use crate::theory::conc::data::ArgInfo;
use crate::theory::conc::data::ArgInfo::UnnamedImplicit;
use crate::theory::{ASYNC, NameMap};
use crate::theory::{Loc, Param, Var};
use crate::{Error, maybe_grow};

pub struct Normalizer<'a> {
    ubiquitous: &'a NameMap,
    sigma: &'a mut Sigma,
    rho: Rho,
    loc: Loc,

    instances: HashMap<Var, Term>,
    implements_interface: Option<Var>,

    expand_undef: bool,

    expand_mu: bool,
    expanded: HashSet<Var>,
}

impl<'a> Normalizer<'a> {
    pub fn new(ubiquitous: &'a NameMap, sigma: &'a mut Sigma, loc: Loc) -> Self {
        Self {
            ubiquitous,
            sigma,
            rho: Default::default(),
            loc,
            instances: Default::default(),
            implements_interface: Default::default(),
            expand_undef: true,
            expand_mu: false,
            expanded: Default::default(),
        }
    }

    fn unifier(&mut self) -> Unifier {
        Unifier::new(self.ubiquitous, self.sigma, self.loc)
    }

    pub fn term(&mut self, tm: Term) -> Result<Term, Error> {
        maybe_grow(move || {
            self.term_impl(tm).inspect(|tm| {
                trace!(target: "normalize", "term normalized successfully: {tm}");
            })
        })
    }

    fn term_box(&mut self, mut tm: Box<Term>) -> Result<Box<Term>, Error> {
        *tm = self.term(*tm)?;
        Ok(tm)
    }

    fn term_impl(&mut self, tm: Term) -> Result<Term, Error> {
        use Term::*;

        debug!(target: "normalize", "normalizing term: {tm}");
        Ok(match tm {
            Ref(x) => {
                if let Some(y) = self.rho.get(&x) {
                    *y.clone()
                } else {
                    Ref(x)
                }
            }
            Undef(v) if self.expand_undef => {
                let ret = self.sigma.get(&v).unwrap().to_term();
                if noinline(&ret) { Undef(v) } else { ret }
            }
            Mu(v) if self.expand_mu && !self.expanded.contains(&v) => {
                self.expanded.insert(v.clone());
                self.sigma.get(&v).unwrap().to_term()
            }
            MetaRef(k, x, sp) => {
                let mut def = self.sigma.get(&x).unwrap().clone();
                *def.ret = self.term(*def.ret)?;
                let ret = match &def.body {
                    Body::Meta(_, s) => match s {
                        Some(solved) => self.term(*solved.clone())?,
                        None => {
                            if let Some(tm) = def.ret.auto_implicit() {
                                def.body = Body::Meta(k, Some(Box::new(tm.clone())));
                                tm
                            } else {
                                trace!(target: "unify", "cannot solve meta: def={def}");
                                MetaRef(k, x.clone(), sp)
                            }
                        }
                    },
                    _ => unreachable!(),
                };
                self.sigma.insert(x, def);
                ret
            }
            Cls {
                class,
                type_args,
                associated,
                object,
            } => {
                let mut a = HashMap::default();
                for (name, typ) in associated {
                    a.insert(name, self.term(typ)?);
                }
                let mut args = Vec::default();
                for arg in type_args {
                    args.push(self.term(arg)?);
                }
                Cls {
                    class,
                    type_args: args,
                    associated: a,
                    object: self.term_box(object)?,
                }
            }
            Const(p, a, b) => {
                let p = self.param(p)?;
                let a = self.term_box(a)?;
                if noinline(a.as_ref()) {
                    Const(p, a, Box::new(self.without_expand_undef(*b)?))
                } else {
                    self.insert_rho(p.var, a);
                    self.term(*b)?
                }
            }
            Let(p, a, b) => Let(self.param(p)?, self.term_box(a)?, self.term_box(b)?),
            Update(p, a, b) => Update(p, self.term_box(a)?, self.term_box(b)?),
            While(p, b, r) => While(self.term_box(p)?, self.term_box(b)?, self.term_box(r)?),
            Fori(b, r) => Fori(self.term_box(b)?, self.term_box(r)?),
            Guard(p, b, e, r) => {
                let p = self.term_box(p)?;
                let b = self.term_box(b)?;
                let e = match e {
                    Some(e) => Some(self.term_box(e)?),
                    None => None,
                };
                let r = self.term_box(r)?;
                match *p {
                    False => match e {
                        Some(e) => self.term(UnitBind(e, r))?,
                        None => *r,
                    },
                    p => Guard(Box::new(p), b, e, r),
                }
            }
            Return(a) => Return(self.term_box(a)?),
            Pi { param, eff, body } => Pi {
                param: self.param(param)?,
                eff: self.term_box(eff)?,
                body: self.term_box(body)?,
            },
            Lam(p, b) => Lam(self.param(p)?, self.term_box(b)?),
            App(f, ai, x) => match self.term(*f)? {
                Lam(p, b) => {
                    let x = self.term_box(x)?;
                    self.insert_rho(p.var, x);
                    self.term(*b)?
                }
                f => App(Box::new(f), ai, self.term_box(x)?),
            },
            Sigma(p, b) => Sigma(self.param(p)?, self.term_box(b)?),
            Tuple(a, b) => Tuple(self.term_box(a)?, self.term_box(b)?),
            TupleBind(p, q, a, b) => {
                let p = self.param(p)?;
                let q = self.param(q)?;
                let a = self.term_box(a)?;
                if noinline(a.as_ref()) {
                    TupleBind(p, q, a, Box::new(self.without_expand_undef(*b)?))
                } else {
                    match *a {
                        Tuple(x, y) => {
                            self.insert_rho(p.var, x);
                            self.insert_rho(q.var, y);
                            *self.term_box(b)?
                        }
                        _ => TupleBind(p, q, a, Box::new(self.without_expand_undef(*b)?)),
                    }
                }
            }
            UnitBind(a, b) => match self.term(*a)? {
                TT => self.term(*b)?,
                a => UnitBind(Box::new(a), Box::new(self.without_expand_undef(*b)?)),
            },
            If(p, t, e) => match self.term(*p)? {
                True => self.term(*t)?,
                False => self.term(*e)?,
                p => If(
                    Box::new(p),
                    Box::new(self.without_expand_undef(*t)?),
                    Box::new(self.without_expand_undef(*e)?),
                ),
            },
            BoolOr(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (*a, *b) {
                    (True, _) => True,
                    (False, b) => b,
                    (a, b) => BoolOr(Box::new(a), Box::new(b)),
                }
            }
            BoolAnd(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (*a, *b) {
                    (True, b) => b,
                    (False, _) => False,
                    (a, b) => BoolAnd(Box::new(a), Box::new(b)),
                }
            }
            BoolNot(a) => {
                let a = self.term_box(a)?;
                match *a {
                    True => False,
                    False => True,
                    a => BoolNot(Box::new(a)),
                }
            }
            BoolEq(a, b) => match (*self.term_box(a)?, *self.term_box(b)?) {
                (True, True) | (False, False) => True,
                (True, False) | (False, True) => False,
                (a, b) => BoolEq(Box::new(a), Box::new(b)),
            },
            BoolNeq(a, b) => match (*self.term_box(a)?, *self.term_box(b)?) {
                (True, True) | (False, False) => False,
                (True, False) | (False, True) => True,
                (a, b) => BoolNeq(Box::new(a), Box::new(b)),
            },
            StrAdd(a, b) => match (*self.term_box(a)?, *self.term_box(b)?) {
                (Str(a), Str(b)) => {
                    let mut a = a[..a.len() - 1].to_string();
                    a.push_str(&b[1..]);
                    Str(a.into())
                }
                (a, b) => StrAdd(Box::new(a), Box::new(b)),
            },
            StrEq(a, b) => match (*self.term_box(a)?, *self.term_box(b)?) {
                (Str(a), Str(b)) => Term::bool(a == b),
                (a, b) => StrEq(Box::new(a), Box::new(b)),
            },
            StrNeq(a, b) => match (*self.term_box(a)?, *self.term_box(b)?) {
                (Str(a), Str(b)) => Term::bool(a != b),
                (a, b) => StrNeq(Box::new(a), Box::new(b)),
            },
            StrToLowerCase(a) => match *self.term_box(a)? {
                Str(a) => Str(a.to_string().to_lowercase().into()),
                a => StrToLowerCase(Box::new(a)),
            },
            NumAdd(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (*a, *b) {
                    (Num(a), Num(b)) => Num(a + b),
                    (a, b) => NumAdd(Box::new(a), Box::new(b)),
                }
            }
            NumSub(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (*a, *b) {
                    (Num(a), Num(b)) => Num(a - b),
                    (a, b) => NumSub(Box::new(a), Box::new(b)),
                }
            }
            NumMul(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (*a, *b) {
                    (Num(a), Num(b)) => Num(a * b),
                    (a, b) => NumMul(Box::new(a), Box::new(b)),
                }
            }
            NumDiv(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (*a, *b) {
                    (Num(a), Num(b)) if b != 0.0 => Num(a / b),
                    (a, b) => NumDiv(Box::new(a), Box::new(b)),
                }
            }
            NumMod(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (*a, *b) {
                    (Num(a), Num(b)) => Num(a % b),
                    (a, b) => NumMod(Box::new(a), Box::new(b)),
                }
            }
            NumEq(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (*a, *b) {
                    (Num(a), Num(b)) => Term::bool(a == b),
                    (a, b) => NumEq(Box::new(a), Box::new(b)),
                }
            }
            NumNeq(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (*a, *b) {
                    (Num(a), Num(b)) => Term::bool(a != b),
                    (a, b) => NumNeq(Box::new(a), Box::new(b)),
                }
            }
            NumLe(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (*a, *b) {
                    (Num(a), Num(b)) => Term::bool(a <= b),
                    (a, b) => NumLe(Box::new(a), Box::new(b)),
                }
            }
            NumGe(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (*a, *b) {
                    (Num(a), Num(b)) => Term::bool(a >= b),
                    (a, b) => NumGe(Box::new(a), Box::new(b)),
                }
            }
            NumLt(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (*a, *b) {
                    (Num(a), Num(b)) => Term::bool(a < b),
                    (a, b) => NumLt(Box::new(a), Box::new(b)),
                }
            }
            NumGt(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (*a, *b) {
                    (Num(a), Num(b)) => Term::bool(a > b),
                    (a, b) => NumGt(Box::new(a), Box::new(b)),
                }
            }
            NumNeg(a) => match *self.term_box(a)? {
                Num(a) => Num(-a),
                a => NumNeg(Box::new(a)),
            },
            NumToStr(a) => match *self.term_box(a)? {
                Num(a) => Str(format!("\"{a}\"").into()),
                a => NumToStr(Box::new(a)),
            },
            BigintToStr(a) => match *self.term_box(a)? {
                Big(a) => Str(format!("\"{}\"", a.strip_suffix('n').unwrap_or(a.as_ref())).into()),
                a => BigintToStr(Box::new(a)),
            },
            ArrayIterator(t) => ArrayIterator(self.term_box(t)?),
            ArrIterNext(it) => ArrIterNext(self.term_box(it)?),
            Array(t) => Array(self.term_box(t)?),
            Arr(xs) => {
                let mut ret = Vec::default();
                for x in xs {
                    ret.push(self.term(x)?);
                }
                Arr(ret)
            }
            ArrLength(a) => ArrLength(self.term_box(a)?),
            ArrPush(a, v) => ArrPush(self.term_box(a)?, self.term_box(v)?),
            ArrForeach(a, f) => ArrForeach(self.term_box(a)?, self.term_box(f)?),
            ArrAt(a, i) => ArrAt(self.term_box(a)?, self.term_box(i)?),
            ArrInsert(a, i, v) => {
                ArrInsert(self.term_box(a)?, self.term_box(i)?, self.term_box(v)?)
            }
            ArrIter(a) => ArrIter(self.term_box(a)?),
            MapIterator(t) => MapIterator(self.term_box(t)?),
            MapIterNext(it) => MapIterNext(self.term_box(it)?),
            Map(k, v) => Map(self.term_box(k)?, self.term_box(v)?),
            Kv(xs) => {
                let mut ret = Vec::default();
                for (k, v) in xs {
                    ret.push((self.term(k)?, self.term(v)?));
                }
                Kv(ret)
            }
            MapHas(m, k) => MapHas(self.term_box(m)?, self.term_box(k)?),
            MapGet(m, k) => MapGet(self.term_box(m)?, self.term_box(k)?),
            MapSet(m, k, v) => MapSet(self.term_box(m)?, self.term_box(k)?, self.term_box(v)?),
            MapDelete(m, k) => MapDelete(self.term_box(m)?, self.term_box(k)?),
            MapClear(m) => MapClear(self.term_box(m)?),
            MapIter(a) => MapIter(self.term_box(a)?),
            RkToStr(a) => match *self.term_box(a)? {
                Rk(k) => Str(format!("\"{k}\"").into()),
                a => RkToStr(Box::new(a)),
            },
            AtResult { ty, key } => {
                let ty = self.term_box(ty)?;
                let key = self.term_box(key)?;
                if ty.is_unsolved() {
                    return Ok(AtResult { ty, key });
                }
                match *key {
                    Rk(k) => {
                        let mut fields = match *ty {
                            Object(f) | Enum(f) => match *f {
                                Fields(f) => f,
                                _ => unreachable!(),
                            },
                            _ => unreachable!(),
                        };
                        match fields.remove(&k) {
                            Some(ty) => ty,
                            None => return Err(UnresolvedField(k, Fields(fields), self.loc)),
                        }
                    }
                    _ => return Ok(AtResult { ty, key }),
                }
            }
            At(a, k) => match self.term(*k)? {
                Rk(k) => match *self.term_box(a)? {
                    Obj(a) => match *a {
                        Fields(f) => self.at(f, k)?,
                        a => At(Box::new(Obj(Box::new(a))), Box::new(Rk(k))),
                    },
                    Variant(a) => match *a {
                        Fields(f) => self.at(f, k)?,
                        a => At(Box::new(Variant(Box::new(a))), Box::new(Rk(k))),
                    },
                    a => At(Box::new(a), Box::new(Rk(k))),
                },
                k => At(self.term_box(a)?, Box::new(k)),
            },
            Fields(fields) => {
                let mut f = FieldMap::default();
                for (n, tm) in fields {
                    f.insert(n, self.term(tm)?);
                }
                Fields(f)
            }
            Associate(a, n) => {
                let a = *self.term_box(a)?;
                let (params, assoc) = match a.class_methods(self.sigma) {
                    Some(PartialClass {
                        type_params,
                        associated,
                        ..
                    }) => (type_params, associated),
                    None => return Ok(Associate(Box::new(a), n)),
                };
                let typ = match assoc.get(&n) {
                    Some(v) => v,
                    None => return Err(UnresolvedField(n, a, self.loc)),
                };
                let f = self.sigma.get(typ).unwrap().to_term();
                self.apply(f, UnnamedImplicit, params.as_ref())?
            }
            Combine(inplace_only, a, b) => {
                let mut a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (a.as_mut(), b.as_ref()) {
                    (Fields(x), Fields(y)) => {
                        let l = x.len();
                        // TODO: eliminate clone
                        x.extend(y.iter().map(|(n, tm)| (*n, tm.clone())));
                        if inplace_only && x.len() > l {
                            return Err(FieldsNonExtendable(*b, self.loc));
                        }
                        *a
                    }
                    _ => Combine(inplace_only, a, b),
                }
            }
            RowOrd(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (a.as_ref(), b.as_ref()) {
                    (Fields(x), Fields(y)) => self.unifier().fields_ord(x, y)?,
                    (Fields(x), Union(ys)) => ys.iter().try_fold((), |_, y| match y {
                        Fields(y) => self.unifier().fields_ord(x, y),
                        _ => unreachable!(),
                    })?,
                    _ => {}
                }
                RowOrd(a, b)
            }
            RowEq(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                if let (Fields(a), Fields(b)) = (a.as_ref(), b.as_ref()) {
                    self.unifier().fields_eq(a, b)?;
                }
                RowEq(a, b)
            }
            Object(r) => Object(self.term_box(r)?),
            Obj(a) => Obj(self.term_box(a)?),
            Concat(a, b) => match (self.term(*a)?, self.term(*b)?) {
                (Object(a), Object(b)) => self.term(Object(Box::new(Combine(false, a, b))))?,
                (a, b) => Concat(Box::new(a), Box::new(b)),
            },
            Cat(a, b) => {
                let mut a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (a.as_mut(), b.as_ref()) {
                    (Obj(x), Obj(y)) => match (x.as_mut(), y.as_ref()) {
                        (Fields(x), Fields(y)) => {
                            // TODO: eliminate clone
                            x.extend(y.iter().map(|(n, tm)| (*n, tm.clone())));
                            *a
                        }
                        _ => Cat(a, b),
                    },
                    _ => Cat(a, b),
                }
            }
            Access(a, n) => match *self.term_box(a)? {
                Obj(x) => match *x {
                    Fields(mut fields) => fields.remove(&n).unwrap(),
                    f => Access(Box::new(Obj(Box::new(f))), n),
                },
                a => Access(Box::new(a), n),
            },
            Downcast(r, m) => Downcast(self.term_box(r)?, self.term_box(m)?),
            Down(a, m) => {
                let a = self.term_box(a)?;
                let mut m = self.term_box(m)?;
                match a.as_ref() {
                    Obj(o) => match (o.as_ref(), m.as_mut()) {
                        (Fields(x), Fields(y)) => {
                            // TODO: eliminate clone
                            *y = y
                                .keys()
                                .map(|n| {
                                    let tm = x.get(n).unwrap().clone();
                                    (*n, tm)
                                })
                                .collect();
                            Obj(m)
                        }
                        _ => Down(a, m),
                    },
                    _ => Down(a, m),
                }
            }
            Enum(r) => Enum(self.term_box(r)?),
            Variant(r) => Variant(self.term_box(r)?),
            Upcast(r) => Upcast(self.term_box(r)?),
            Disjoint(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                if let (Enum(a), Enum(b)) = (*a, *b) {
                    if let (Fields(a), Fields(b)) = (*a, *b) {
                        return Ok(Enum(Box::new(Fields(self.fields_disjoint(a, b)?))));
                    }
                }
                unreachable!()
            }
            Up(r, from, to) => {
                let r = self.term_box(r)?;
                let from = self.term_box(from)?;
                let to = self.term_box(to)?;
                match (*from, *to) {
                    (Fields(from), Fields(to)) => {
                        self.unifier().fields_ord(&from, &to)?;
                        *r
                    }
                    (from, to) => Up(r, Box::new(from), Box::new(to)),
                }
            }
            Switch(a, cs, d) => {
                let a = self.term_box(a)?;
                match a.as_ref() {
                    Variant(r) => match r.as_ref() {
                        Fields(f) => {
                            // TODO: eliminate clone
                            let (n, x) = f.iter().next().unwrap();
                            match (cs.get(n), d) {
                                (Some((v, tm)), _) => {
                                    self.insert_rho(v.clone(), Box::new(x.clone()));
                                    self.term(tm.clone())?
                                }
                                (None, Some((v, tm))) => {
                                    self.insert_rho(v, a);
                                    self.term(*tm)?
                                }
                                _ => return Err(NonExhaustive(*a, self.loc)),
                            }
                        }
                        _ => Switch(a, self.case_map(cs)?, self.case_default(d)?),
                    },
                    _ => Switch(a, self.case_map(cs)?, self.case_default(d)?),
                }
            }
            Unionify(a) => match *self.term_box(a)? {
                Variant(a) => match *a {
                    Fields(f) => f.into_iter().next().unwrap().1,
                    v => Unionify(Box::new(Variant(Box::new(v)))),
                },
                a => Unionify(Box::new(a)),
            },
            Union(ts) => Union(
                ts.into_iter()
                    .map(|t| self.term(t))
                    .collect::<Result<_, _>>()?,
            ),
            Varargs(t) => Varargs(self.term_box(t)?),
            AnonVarargs(t) => AnonVarargs(self.term_box(t)?),
            Spread(a) => Spread(self.term_box(a)?),
            Find {
                interface_fn: f,
                instance_ty: ty,
            } => {
                let ty = self.term_box(ty)?;
                let (i, args) = match ty.as_ref() {
                    Interface { name, args, .. } => (name, args),
                    _ => unreachable!(),
                };
                if let Some(ty) = self.instances.get(i) {
                    return self.find_instance(ty.clone(), f);
                }
                if args.iter().any(|a| a.is_unsolved())
                    || i.as_str() == ASYNC
                    || matches!(&self.implements_interface, Some(j) if i == j)
                {
                    Find {
                        interface_fn: f,
                        instance_ty: ty,
                    }
                } else {
                    self.find_instance(*ty, f)?
                }
            }
            Interface {
                name,
                args,
                should_check,
            } => {
                let args = args
                    .into_iter()
                    .map(|a| self.term(a))
                    .collect::<Result<Box<_>, _>>()?;
                if should_check && args.iter().all(|a| !a.is_unsolved()) {
                    self.check_interface(name, args, should_check)?
                } else {
                    Interface {
                        name,
                        args,
                        should_check,
                    }
                }
            }
            Typeof(ty) => {
                let ty = self.term(*ty)?;
                if ty.is_unsolved() {
                    Typeof(Box::new(ty))
                } else {
                    let mut m = UstrMap::default();
                    m.insert(
                        match ty {
                            Number => "TypeofNumber",
                            String => "TypeofString",
                            Boolean => "TypeofBoolean",
                            Bigint => "TypeofBigint",
                            Unit => "TypeofUnit",
                            Object(..) => "TypeofObject",
                            Enum(..) => "TypeofEnum",
                            _ => return Err(ExpectedReflectable(ty, self.loc)),
                        }
                        .into(),
                        TT,
                    );
                    Variant(Box::new(Fields(m)))
                }
            }
            Keyof(o) => match self.term(*o)? {
                Obj(a) | Variant(a) => match *a {
                    Fields(m) => Term::rowkey_list(m),
                    ty => return Err(ExpectedReflectable(ty, self.loc)),
                },
                o if o.is_unsolved() => Keyof(Box::new(o)),
                o => return Err(ExpectedReflectable(o, self.loc)),
            },
            Discriminants(ty) => match self.term(*ty)? {
                Fields(m) => Term::rowkey_list(m),
                ty => Discriminants(Box::new(ty)),
            },
            Panic(a) => Panic(self.term_box(a)?),
            ConsoleLog(m) => ConsoleLog(self.term_box(m)?),
            SetTimeout(f, d, x) => {
                SetTimeout(self.term_box(f)?, self.term_box(d)?, self.term_box(x)?)
            }
            JSONStringify(a) => match *self.term_box(a)? {
                Str(s) => Str(Value::String(s.to_string()).to_string().into()),
                a => JSONStringify(Box::new(a)),
            },
            HtmlElementAddEventListener(n, e, l) => {
                HtmlElementAddEventListener(self.term_box(n)?, self.term_box(e)?, self.term_box(l)?)
            }
            DocumentGetElementById(a) => DocumentGetElementById(self.term_box(a)?),
            EmitAsync(a) => EmitAsync(self.term_box(a)?),
            tm => tm,
        })
    }

    fn insert_rho(&mut self, v: Var, tm: Box<Term>) {
        v.is_unbound().not().then(|| self.rho.insert(v.clone(), tm));
    }

    pub fn with(&mut self, rho: &[(&Var, &Term)], tm: Term) -> Result<Term, Error> {
        for &(x, v) in rho {
            self.insert_rho(x.clone(), Box::new(v.clone()));
        }
        self.term(tm)
    }

    pub fn with_instances(&mut self, m: HashMap<Var, Term>, tm: Term) -> Result<Term, Error> {
        self.instances = m;
        self.term(tm)
    }

    pub fn with_expand_mu(&mut self, tm: Term) -> Result<Term, Error> {
        self.expand_mu = true;
        self.term(tm)
    }

    fn without_expand_undef(&mut self, tm: Term) -> Result<Term, Error> {
        let old = self.expand_undef;
        self.expand_undef = false;
        let ret = self.term(tm);
        self.expand_undef = old;
        ret
    }

    pub fn with_implements_interface(mut self, i: &Var) -> Self {
        self.implements_interface = Some(i.clone());
        self
    }

    pub fn apply(&mut self, f: Term, ai: ArgInfo, args: &[Term]) -> Result<Term, Error> {
        use Term::*;
        let mut ret = f;
        for x in args {
            match ret {
                Lam(p, b) => {
                    ret = self.with(&[(&p.var, x)], *b)?;
                }
                _ => ret = App(Box::new(ret), ai.clone(), Box::new(x.clone())),
            }
        }
        Ok(ret)
    }

    pub fn apply_type(&mut self, f: Term, args: &[Term]) -> Result<Term, Error> {
        use Term::*;
        let mut ret = f;
        for x in args {
            match ret {
                Pi { param, body, .. } => ret = self.with(&[(&param.var, x)], *body)?,
                _ => unreachable!(),
            }
        }
        Ok(ret)
    }

    fn param(&mut self, mut p: Param<Term>) -> Result<Param<Term>, Error> {
        *p.typ = self.term(*p.typ)?;
        Ok(p)
    }

    fn case_map(&mut self, cs: CaseMap) -> Result<CaseMap, Error> {
        cs.into_iter()
            .map(|(k, (v, tm))| {
                let tm = self.without_expand_undef(tm)?;
                Ok::<_, Error>((k, (v, tm)))
            })
            .collect()
    }

    fn case_default(&mut self, d: CaseDefault) -> Result<CaseDefault, Error> {
        Ok(match d {
            Some((v, tm)) => Some((v, Box::new(self.without_expand_undef(*tm)?))),
            None => None,
        })
    }

    fn find_instance(&mut self, ty: Term, f: Var) -> Result<Term, Error> {
        use Body::*;

        let i = match &ty {
            Term::Interface { name, .. } => name,
            _ => unreachable!(),
        };

        let instances = match &self.sigma.get(i).unwrap().body {
            Interface { instances, .. } => instances.iter().rev().cloned().collect::<Box<_>>(),
            _ => unreachable!(),
        };

        for inst in instances {
            let (inst_ty, inst_fn) = match &self.sigma.get(&inst).unwrap().body {
                Instance(body) => (body.inst.clone(), body.fns.get(&f).unwrap().clone()),
                _ => unreachable!(),
            };

            if self.unifier().unify(&ty, &inst_ty).is_err() {
                continue;
            }

            return Ok(self.sigma.get(&inst_fn).unwrap().to_term());
        }

        let (args, meth_ref) = match ty.class_methods(self.sigma) {
            Some(PartialClass {
                applied_types,
                methods,
                ..
            }) => match methods.get(f.as_str()) {
                Some(m) => (applied_types, m.clone()),
                None => return Err(UnresolvedInstance(ty, self.loc)),
            },
            None => return Err(UnresolvedInstance(ty, self.loc)),
        };
        let mut meth = self.sigma.get(&meth_ref).unwrap().to_term();
        if !args.is_empty() {
            meth = self.apply(meth, UnnamedImplicit, args.as_ref())?;
        }

        Ok(meth)
    }

    fn check_interface(
        &mut self,
        name: Var,
        args: Box<[Term]>,
        should_check: bool,
    ) -> Result<Term, Error> {
        let i_def = self.sigma.get(&name).unwrap();
        let i_def_tele_len = i_def.tele.len();

        let (i_fns, instances) = match &self.sigma.get(&name).unwrap().body {
            Body::Interface { fns, instances, .. } => (fns.clone(), instances.clone()),
            _ => return Err(ExpectedInterface(Term::Ref(name), self.loc)),
        };

        let i_name = name.clone();
        let i_ty = Term::Interface {
            name,
            args,
            should_check,
        };
        for inst in instances.into_iter().rev() {
            let inst_ty = match &self.sigma.get(&inst).unwrap().body {
                Body::Instance(body) => body.inst.clone(),
                _ => unreachable!(),
            };

            if self.unifier().unify(&i_ty, &inst_ty).is_ok() {
                return Ok(i_ty);
            }
        }

        let (cls_args, meths) = match i_ty.class_methods(self.sigma) {
            Some(PartialClass {
                applied_types,
                methods,
                ..
            }) if i_def_tele_len == 1 => (applied_types, methods),
            _ => return Err(UnsatisfiedConstraint(i_name, i_ty, self.loc)),
        };
        let (name, args, should_check) = match i_ty {
            Term::Interface {
                name,
                args,
                should_check,
            } => (name, args, should_check),
            _ => unreachable!(),
        };
        let cls = args[0].clone();
        for i_fn in i_fns {
            let mut m_ty = match meths.get(i_fn.as_str()) {
                Some(m) => self.sigma.get(m).unwrap().to_type(),
                None => {
                    return Err(ClassMethodNotImplemented(
                        i_fn,
                        i_name,
                        Term::Ref(name),
                        self.loc,
                    ));
                }
            };
            if !cls_args.is_empty() {
                m_ty = self.apply_type(m_ty, cls_args.as_ref())?;
            }

            let i_fn_def = self.sigma.get(&i_fn).unwrap();
            let mut i_fn_type = i_fn_def.to_type_skip(i_def_tele_len + 1);
            let i_v = i_fn_def.tele[0].var.clone();
            let i_fn_rho = Box::new([(&i_v, &cls)]);
            i_fn_type = self.with(i_fn_rho.as_ref(), i_fn_type)?;

            self.unifier().unify(&i_fn_type, &m_ty)?
        }

        Ok(Term::Interface {
            name,
            args,
            should_check,
        })
    }

    fn fields_disjoint(&mut self, mut a: FieldMap, b: FieldMap) -> Result<FieldMap, Error> {
        for (x, x_ty) in a.iter() {
            match b.get(x) {
                Some(y_ty) => self.unifier().unify(x_ty, y_ty)?,
                None => continue,
            }
        }
        a.extend(b);
        Ok(a)
    }

    fn at(&self, mut fields: FieldMap, k: Ustr) -> Result<Term, Error> {
        match fields.remove(&k) {
            Some(tm) => Ok(tm),
            None => Err(UnresolvedField(k, Term::Fields(fields), self.loc)),
        }
    }
}
