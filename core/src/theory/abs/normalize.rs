use std::collections::{HashMap, HashSet};

use log::{debug, trace};

use crate::theory::abs::data::{CaseDefault, CaseMap, FieldMap, PartialClass, Term};
use crate::theory::abs::def::{Body, Rho, Sigma};
use crate::theory::abs::inline::noinline;
use crate::theory::abs::unify::Unifier;
use crate::theory::conc::data::ArgInfo;
use crate::theory::conc::data::ArgInfo::UnnamedImplicit;
use crate::theory::{Loc, Param, Var};
use crate::theory::{NameMap, ASYNC};
use crate::Error::{
    ClassMethodNotImplemented, ExpectedReflectable, FieldsNonExtendable, NonExhaustive,
    UnresolvedField, UnresolvedInstance, UnsatisfiedConstraint,
};
use crate::{maybe_grow, Error};

pub struct Normalizer<'a> {
    ubiquitous: &'a NameMap,
    sigma: &'a mut Sigma,
    rho: Rho,
    loc: Loc,

    instances: HashMap<Var, Term>,

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
        use Body::*;
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
                let ret = self.sigma.get(&v).unwrap().to_term(v.clone());
                if noinline(&ret) {
                    Undef(v)
                } else {
                    ret
                }
            }
            Mu(v) if self.expand_mu && !self.expanded.contains(&v) => {
                self.expanded.insert(v.clone());
                self.sigma.get(&v).unwrap().to_term(v)
            }
            MetaRef(k, x, sp) => {
                let mut def = self.sigma.get(&x).unwrap().clone();
                *def.ret = self.term(*def.ret)?;
                let ret = match &def.body {
                    Meta(_, s) => match s {
                        Some(solved) => self.term(*solved.clone())?,
                        None => {
                            if let Some(tm) = def.ret.auto_implicit() {
                                def.body = Meta(k, Some(Box::new(tm.clone())));
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
                    self.rho.insert(p.var, a);
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
                    self.rho.insert(p.var, x);
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
                            self.rho.insert(p.var, x);
                            self.rho.insert(q.var, y);
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
                (Str(mut a), Str(mut b)) => {
                    a.pop();
                    b.remove(0);
                    a.push_str(b.as_str());
                    Str(a)
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
                Num(a) => Str(format!("\"{a}\"")),
                a => NumToStr(Box::new(a)),
            },
            BigintToStr(a) => match *self.term_box(a)? {
                Big(mut a) => {
                    if a.ends_with('n') {
                        a.pop();
                    }
                    Str(format!("\"{a}\""))
                }
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
                Rk(k) => Str(format!("\"{k}\"")),
                a => RkToStr(Box::new(a)),
            },
            Fields(mut fields) => {
                for tm in fields.values_mut() {
                    // FIXME: not unwind-safe, refactor `Self::term` to accept a `&mut Term`
                    unsafe {
                        let tmp = std::ptr::read(tm);
                        std::ptr::write(tm, self.term(tmp)?);
                    }
                }
                Fields(fields)
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
                let f = self.sigma.get(typ).unwrap().to_term(typ.clone());
                self.apply(f, UnnamedImplicit, params.as_ref())?
            }
            Combine(inplace_only, a, b) => {
                let mut a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (a.as_mut(), b.as_ref()) {
                    (Fields(x), Fields(y)) => {
                        let l = x.len();
                        // TODO: eliminate clone
                        x.extend(y.iter().map(|(n, tm)| (n.clone(), tm.clone())));
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
                if let (Fields(a), Fields(b)) = (a.as_ref(), b.as_ref()) {
                    self.unifier().fields_ord(a, b)?;
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
            Concat(a, b) => {
                let mut a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (a.as_mut(), b.as_ref()) {
                    (Obj(x), Obj(y)) => match (x.as_mut(), y.as_ref()) {
                        (Fields(x), Fields(y)) => {
                            // TODO: eliminate clone
                            x.extend(y.iter().map(|(n, tm)| (n.clone(), tm.clone())));
                            *a
                        }
                        _ => Concat(a, b),
                    },
                    _ => Concat(a, b),
                }
            }
            Access(a, n) => match *self.term_box(a)? {
                Obj(x) => match *x {
                    Fields(mut fields) => fields.remove(&n).unwrap(),
                    f => Access(Box::new(Obj(Box::new(f))), n),
                },
                a => Access(Box::new(a), n),
            },
            AtResult { fields_ty, key } => {
                match (*self.term_box(fields_ty)?, *self.term_box(key)?) {
                    (Fields(mut f), Rk(k)) => match f.remove(&k) {
                        Some(ty) => ty,
                        None => return Err(UnresolvedField(k, Fields(f), self.loc)),
                    },
                    (f, k) => AtResult {
                        fields_ty: Box::new(f),
                        key: Box::new(k),
                    },
                }
            }
            At(a, k) => match self.term(*k)? {
                Rk(k) => self.term(Access(a, k))?,
                k => At(self.term_box(a)?, Box::new(k)),
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
                                    (n.clone(), tm)
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
                                    self.rho.insert(v.clone(), Box::new(x.clone()));
                                    self.term(tm.clone())?
                                }
                                (None, Some((v, tm))) => {
                                    self.rho.insert(v, a);
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
            Unionify(a) => Unionify(self.term_box(a)?),
            Instanceof(a, i) => {
                let a = self.term_box(a)?;
                if !a.is_unsolved() {
                    self.check_constraint(&a, &i)?;
                }
                Instanceof(a, i)
            }
            Varargs(t) => Varargs(self.term_box(t)?),
            AnonVarargs(t) => AnonVarargs(self.term_box(t)?),
            Spread(a) => Spread(self.term_box(a)?),
            Find {
                instance_ty: ty,
                interface: i,
                interface_fn: f,
            } => {
                if let Some(ty) = self.instances.get(&i) {
                    return self.find_instance(ty.clone(), i, f);
                }
                let ty = self.term_box(ty)?;
                if ty.is_unsolved() || i.as_str() == ASYNC {
                    Find {
                        instance_ty: ty,
                        interface: i,
                        interface_fn: f,
                    }
                } else {
                    self.find_instance(*ty, i, f)?
                }
            }
            Typeof(ty) => {
                let ty = self.term(*ty)?;
                if ty.is_unsolved() {
                    Typeof(Box::new(ty))
                } else {
                    Variant(Box::new(Fields(FieldMap::from([(
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
                        .to_string(),
                        TT,
                    )]))))
                }
            }
            Keyof(ty) => {
                let ty = self.term(*ty)?;
                if ty.is_unsolved() {
                    Keyof(Box::new(ty))
                } else {
                    match ty {
                        Object(a) | Enum(a) => match *a {
                            Fields(m) => {
                                let mut ret = Term::list_empty();
                                for (key, _) in m {
                                    ret = Term::list_append(Rk(key), ret);
                                }
                                ret
                            }
                            ty => return Err(ExpectedReflectable(ty, self.loc)),
                        },
                        Downcast(a, ..) | Upcast(a) => self.term(*a)?,
                        _ => return Err(ExpectedReflectable(ty, self.loc)),
                    }
                }
            }
            Panic(a) => Panic(self.term_box(a)?),
            ConsoleLog(m) => ConsoleLog(self.term_box(m)?),
            SetTimeout(f, d, x) => {
                SetTimeout(self.term_box(f)?, self.term_box(d)?, self.term_box(x)?)
            }
            JSONStringify(a) => JSONStringify(self.term_box(a)?),
            EmitAsync(a) => EmitAsync(self.term_box(a)?),
            tm => tm,
        })
    }

    pub fn with<const N: usize>(
        &mut self,
        rho: [(&Var, &Term); N],
        tm: Term,
    ) -> Result<Term, Error> {
        for (x, v) in rho {
            self.rho.insert(x.clone(), Box::new(v.clone()));
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

    pub fn apply(&mut self, f: Term, ai: ArgInfo, args: &[Term]) -> Result<Term, Error> {
        use Term::*;
        let mut ret = f;
        for x in args {
            match ret {
                Lam(p, b) => {
                    ret = self.with([(&p.var, x)], *b)?;
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
                Pi { param, body, .. } => ret = self.with([(&param.var, x)], *body)?,
                _ => unreachable!(),
            }
        }
        Ok(ret)
    }

    fn param(&mut self, mut p: Param<Term>) -> Result<Param<Term>, Error> {
        *p.typ = self.term(*p.typ)?;
        Ok(p)
    }

    fn case_map(&mut self, mut cs: CaseMap) -> Result<CaseMap, Error> {
        for (_, tm) in cs.values_mut() {
            // FIXME: not unwind-safe, refactor `Self::term` to accept a `&mut Term`
            unsafe {
                let tmp = std::ptr::read(tm);
                std::ptr::write(tm, self.without_expand_undef(tmp)?);
            }
        }
        Ok(cs)
    }

    fn case_default(&mut self, d: CaseDefault) -> Result<CaseDefault, Error> {
        Ok(match d {
            Some((v, tm)) => Some((v, Box::new(self.without_expand_undef(*tm)?))),
            None => None,
        })
    }

    fn check_constraint(&mut self, x: &Term, i: &Var) -> Result<(), Error> {
        use Body::*;
        use Term::*;

        let (fns, instances) = match &self.sigma.get(i).unwrap().body {
            Interface { fns, instances, .. } => (fns.clone(), instances.clone()),
            _ => unreachable!(),
        };

        for inst in instances {
            let y = match &self.sigma.get(&inst).unwrap().body {
                Instance(body) => body.instance_type(self.sigma)?,
                _ => unreachable!(),
            };
            match self.unifier().unify(&y, x) {
                Ok(_) => return Ok(()),
                Err(_) => continue,
            }
        }

        let (args, meths) = match x.class_methods(self.sigma) {
            Some(PartialClass {
                applied_types,
                methods,
                ..
            }) => (applied_types, methods),
            None => return Err(UnsatisfiedConstraint(i.clone(), x.clone(), self.loc)),
        };
        for f in fns {
            let mut m_ty = match meths.get(f.as_str()) {
                Some(m) => self.sigma.get(m).unwrap().to_type(),
                None => return Err(ClassMethodNotImplemented(f, i.clone(), x.clone(), self.loc)),
            };
            if !args.is_empty() {
                m_ty = self.apply_type(m_ty, args.as_ref())?;
            }

            let f_ty = match self.sigma.get(&f).unwrap().to_type() {
                Pi { param: p, body, .. } => self.with([(&p.var, x)], *body)?,
                _ => unreachable!(),
            };

            if self.unifier().unify(&m_ty, &f_ty).is_ok() {
                continue;
            }
            return Err(ClassMethodNotImplemented(f, i.clone(), x.clone(), self.loc));
        }

        Ok(())
    }

    fn find_instance(&mut self, ty: Term, i: Var, f: Var) -> Result<Term, Error> {
        use Body::*;

        let instances = match &self.sigma.get(&i).unwrap().body {
            Interface { instances, .. } => instances.clone(),
            _ => unreachable!(),
        };

        for inst in instances.into_iter().rev() {
            let (inst_ty, inst_fn) = match &self.sigma.get(&inst).unwrap().body {
                Instance(body) => (
                    body.instance_type(self.sigma)?,
                    body.fns.get(&f).unwrap().clone(),
                ),
                _ => unreachable!(),
            };

            if self.unifier().unify(&ty, &inst_ty).is_err() {
                continue;
            }

            return Ok(self.sigma.get(&inst_fn).unwrap().to_term(inst_fn));
        }

        let (args, meth_ref) = match ty.class_methods(self.sigma) {
            Some(PartialClass {
                applied_types,
                methods,
                ..
            }) => (applied_types, methods.get(f.as_str()).unwrap().clone()),
            None => return Err(UnresolvedInstance(ty, self.loc)),
        };
        let mut meth = self.sigma.get(&meth_ref).unwrap().to_term(meth_ref);
        if !args.is_empty() {
            meth = self.apply(meth, UnnamedImplicit, args.as_ref())?;
        }

        Ok(meth)
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
}
