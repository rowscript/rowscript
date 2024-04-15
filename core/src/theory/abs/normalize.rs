use std::collections::HashMap;

use log::trace;

use crate::theory::abs::data::{CaseMap, PartialClass, Term};
use crate::theory::abs::def::{Body, Rho, Sigma};
use crate::theory::abs::effect::has_side_effect;
use crate::theory::abs::reflect::Reflector;
use crate::theory::abs::rename::rename;
use crate::theory::abs::unify::Unifier;
use crate::theory::conc::data::ArgInfo;
use crate::theory::conc::data::ArgInfo::UnnamedImplicit;
use crate::theory::NameMap;
use crate::theory::{Loc, Param, Var};
use crate::Error::{
    ClassMethodNotImplemented, FieldsNonExtendable, NonExhaustive, UnresolvedField,
    UnresolvedImplementation, UnsatisfiedConstraint,
};
use crate::{maybe_grow, Error};

pub struct Normalizer<'a> {
    ubiquitous: &'a NameMap,
    sigma: &'a mut Sigma,
    rho: Rho,
    loc: Loc,
}

impl<'a> Normalizer<'a> {
    pub fn new(ubiquitous: &'a NameMap, sigma: &'a mut Sigma, loc: Loc) -> Self {
        Self {
            ubiquitous,
            sigma,
            rho: Default::default(),
            loc,
        }
    }

    fn unifier(&mut self) -> Unifier {
        Unifier::new(self.ubiquitous, self.sigma, self.loc)
    }

    fn reflector(&self) -> Reflector {
        Reflector::new(self.ubiquitous, self.loc)
    }

    pub fn term(&mut self, tm: Term) -> Result<Term, Error> {
        maybe_grow(move || self.term_impl(tm))
    }

    fn term_box(&mut self, mut tm: Box<Term>) -> Result<Box<Term>, Error> {
        *tm = self.term(*tm)?;
        Ok(tm)
    }

    fn term_impl(&mut self, tm: Term) -> Result<Term, Error> {
        use Body::*;
        use Term::*;

        trace!(target: "normalize", "normalizing term: {tm}");
        Ok(match tm {
            Ref(x) => {
                if let Some(y) = self.rho.get(&x) {
                    *self.term_box(rename(y.clone()))?
                } else {
                    Ref(x)
                }
            }
            MetaRef(k, x, sp) => {
                let mut def = self.sigma.get(&x).unwrap().clone();
                *def.ret = self.term(*def.ret)?;
                let ret = match &def.body {
                    Meta(_, s) => match s {
                        Some(solved) => {
                            let mut ret = *rename(Box::new(Term::lam(&def.tele, *solved.clone())));
                            for (p, x) in sp {
                                ret = App(Box::new(ret), p.into(), Box::new(x))
                            }
                            self.term(ret)?
                        }
                        None => {
                            if let Some(tm) = Self::auto_implicit(&def.ret) {
                                def.body = Meta(k, Some(Box::new(tm.clone())));
                                tm
                            } else {
                                trace!(target: "unify", "cannot solve meta: {x}");
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
            Local(p, a, b) => {
                let a = self.term_box(a)?;
                if has_side_effect(a.as_ref()) {
                    Local(p, a, self.term_box(b)?)
                } else {
                    self.rho.insert(p.var, a);
                    self.term(*b)?
                }
            }
            LocalSet(p, a, b) => LocalSet(p, self.term_box(a)?, self.term_box(b)?),
            LocalUpdate(p, a, b) => LocalUpdate(p, self.term_box(a)?, self.term_box(b)?),
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
                        Some(e) => self.term(UnitLocal(e, r))?,
                        None => *r,
                    },
                    p => Guard(Box::new(p), b, e, r),
                }
            }
            Return(a) => Return(self.term_box(a)?),
            Pi(p, b) => Pi(self.param(p)?, self.term_box(b)?),
            Lam(p, b) => Lam(self.param(p)?, self.term_box(b)?),
            App(f, ai, x) => {
                let f = self.term_box(f)?;
                let x = self.term_box(x)?;
                match *f {
                    Lam(p, b) if !has_side_effect(x.as_ref()) => {
                        self.rho.insert(p.var, x);
                        self.term(*b)?
                    }
                    f => App(Box::new(f), ai, x),
                }
            }
            Sigma(p, b) => Sigma(self.param(p)?, self.term_box(b)?),
            Tuple(a, b) => Tuple(self.term_box(a)?, self.term_box(b)?),
            TupleLocal(p, q, a, b) => {
                let p = self.param(p)?;
                let q = self.param(q)?;
                let a = self.term_box(a)?;
                match *a {
                    Tuple(x, y) => {
                        let mut tms = vec![(p, x)];
                        let mut tm = *y;
                        let mut body = *b;
                        loop {
                            match (tm, body) {
                                (Tuple(x, y), TupleLocal(p, _, _, b)) => {
                                    tms.push((p, x));
                                    tm = *y;
                                    body = *b;
                                }
                                (_, b) => {
                                    body = b;
                                    break;
                                }
                            }
                        }
                        self.term(
                            tms.into_iter()
                                .rfold(body, |b, (p, a)| Local(p, a, Box::new(b))),
                        )?
                    }
                    a => TupleLocal(p, q, Box::new(a), self.term_box(b)?),
                }
            }
            UnitLocal(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match *a {
                    TT => *b,
                    _ => UnitLocal(a, b),
                }
            }
            If(p, t, e) => {
                let p = self.term_box(p)?;
                let t = self.term_box(t)?;
                let e = self.term_box(e)?;
                match *p {
                    True => *t,
                    False => *e,
                    _ => If(p, t, e),
                }
            }
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
            Access(a, n) => {
                let a = self.term_box(a)?;
                match a.as_ref() {
                    Obj(x) => match x.as_ref() {
                        Fields(fields) => fields.get(&n).unwrap().clone(),
                        _ => Access(a, n),
                    },
                    _ => Access(a, n),
                }
            }
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
                let cs = self.case_map(cs)?;
                let d = match d {
                    Some((v, tm)) => Some((v, Box::new(self.term(*tm)?))),
                    None => None,
                };
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
                        _ => Switch(a, cs, d),
                    },
                    _ => Switch(a, cs, d),
                }
            }
            Unionify(a) => Unionify(self.term_box(a)?),
            ImplementsOf(a, i) => {
                let a = self.term_box(a)?;
                if !matches!(*a, Ref(_) | MetaRef(_, _, _)) {
                    self.check_constraint(&a, &i)?;
                }
                ImplementsOf(a, i)
            }
            VarArr(t) => VarArr(self.term_box(t)?),
            Spread(a) => Spread(self.term_box(a)?),
            Find(ty, i, f) => {
                let ty = self.term_box(ty)?;
                match *ty {
                    Ref(_) | MetaRef(_, _, _) => Find(ty, i, f),
                    ty if self.is_reflector(&i) => {
                        let r = self.reflector();
                        *match f.as_str() {
                            "reflect" => r.reflect(ty)?,
                            "unreflect" => r.unreflect(ty),
                            _ => unreachable!(),
                        }
                    }
                    ty => self.find_implementation(ty, i, f)?,
                }
            }
            Reflected(a) => {
                let ty = *self.term_box(a)?;
                *self.reflector().reflected(ty, true)?
            }
            ErrorThrow(a) => ErrorThrow(self.term_box(a)?),
            ConsoleLog(m) => ConsoleLog(self.term_box(m)?),
            tm => tm,
        })
    }

    pub fn with(&mut self, rho: &[(&Var, &Term)], tm: Term) -> Result<Term, Error> {
        for &(x, v) in rho {
            self.rho.insert(x.clone(), Box::new(v.clone()));
        }
        self.term(tm)
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
                Pi(p, b) => {
                    ret = self.with(&[(&p.var, x)], *b)?;
                }
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
                std::ptr::write(tm, self.term(tmp)?);
            }
        }
        Ok(cs)
    }

    fn auto_implicit(tm: &Term) -> Option<Term> {
        use Term::*;
        match tm {
            RowEq(..) => Some(RowRefl),
            RowOrd(..) => Some(RowSat),
            ImplementsOf(..) => Some(ImplementsSat),
            _ => None,
        }
    }

    fn check_constraint(&mut self, x: &Term, i: &Var) -> Result<(), Error> {
        use Body::*;
        use Term::*;

        let (fns, ims) = match &self.sigma.get(i).unwrap().body {
            Interface { fns, ims } => (fns.clone(), ims.clone()),
            _ => unreachable!(),
        };

        for im in ims {
            let y = match &self.sigma.get(&im).unwrap().body {
                Implements(body) => body.implementor_type(self.sigma)?,
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
                Pi(p, body) => self.with(&[(&p.var, x)], *body)?,
                _ => unreachable!(),
            };

            match self.unifier().unify(&m_ty, &f_ty) {
                Ok(_) => continue,
                Err(_) => return Err(ClassMethodNotImplemented(f, i.clone(), x.clone(), self.loc)),
            }
        }

        Ok(())
    }

    fn find_implementation(&mut self, ty: Term, i: Var, f: Var) -> Result<Term, Error> {
        use Body::*;

        let ims = match &self.sigma.get(&i).unwrap().body {
            Interface { ims, .. } => ims.clone(),
            _ => unreachable!(),
        };

        for im in ims.into_iter().rev() {
            let (im_ty, im_fn) = match &self.sigma.get(&im).unwrap().body {
                Implements(body) => (
                    body.implementor_type(self.sigma)?,
                    body.fns.get(&f).unwrap().clone(),
                ),
                _ => unreachable!(),
            };

            if self.unifier().unify(&ty, &im_ty).is_err() {
                continue;
            }

            return Ok(self.sigma.get(&im_fn).unwrap().to_term(im_fn));
        }

        let (args, meth_ref) = match ty.class_methods(self.sigma) {
            Some(PartialClass {
                applied_types,
                methods,
                ..
            }) => (applied_types, methods.get(f.as_str()).unwrap().clone()),
            None => return Err(UnresolvedImplementation(ty, self.loc)),
        };
        let mut meth = self.sigma.get(&meth_ref).unwrap().to_term(meth_ref);
        if !args.is_empty() {
            meth = self.apply(meth, UnnamedImplicit, args.as_ref())?;
        }

        Ok(meth)
    }

    fn is_reflector(&self, i: &Var) -> bool {
        return &self.ubiquitous.get("Reflector").unwrap().1 == i;
    }
}
