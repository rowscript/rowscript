use crate::theory::abs::data::{CaseMap, Dir, Term};
use crate::theory::abs::def::{Body, Rho, Sigma};
use crate::theory::abs::effect::has_side_effect;
use crate::theory::abs::reflect::Reflector;
use crate::theory::abs::rename::rename;
use crate::theory::abs::unify::Unifier;
use crate::theory::conc::data::ArgInfo;
use crate::theory::conc::data::ArgInfo::UnnamedExplicit;
use crate::theory::NameMap;
use crate::theory::{Loc, Param, Var};
use crate::Error;
use crate::Error::{
    ClassMethodNotImplemented, FieldsNonExtendable, UnresolvedImplementation, UnsatisfiedConstraint,
};

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
        stacker::maybe_grow(512 * 1024, 4 * 1024 * 1024, move || self.term_impl(tm))
    }

    fn term_box(&mut self, mut tm: Box<Term>) -> Result<Box<Term>, Error> {
        *tm = self.term(*tm)?;
        Ok(tm)
    }

    fn term_impl(&mut self, tm: Term) -> Result<Term, Error> {
        use Body::*;
        use Term::*;

        Ok(match tm {
            Ref(x) => {
                if let Some(y) = self.rho.get(&x) {
                    self.term(rename(*y.clone()))?
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
                            let mut ret = rename(Term::lam(&def.tele, solved.clone()));
                            for (_, x) in sp {
                                ret = App(Box::new(ret), UnnamedExplicit, Box::new(x))
                            }
                            self.term(ret)?
                        }
                        None => {
                            if let Some(tm) = Self::auto_implicit(&def.ret) {
                                def.body = Meta(k, Some(tm.clone()));
                                tm
                            } else {
                                MetaRef(k, x.clone(), sp)
                            }
                        }
                    },
                    _ => unreachable!(),
                };
                self.sigma.insert(x, def);
                ret
            }
            Undef(x) => self.sigma.get(&x).unwrap().to_term(x),
            Cls(n, a) => Cls(n, self.term_box(a)?),
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
            While(p, b, r) => While(self.term_box(p)?, self.term_box(b)?, self.term_box(r)?),
            Fori(b, r) => Fori(self.term_box(b)?, self.term_box(r)?),
            Guard(p, b, r) => Guard(self.term_box(p)?, self.term_box(b)?, self.term_box(r)?),
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
                let a = self.term_box(a)?;
                if let Tuple(x, y) = *a {
                    self.rho.insert(p.var, x);
                    self.rho.insert(q.var, y);
                    self.term(*b)?
                } else {
                    TupleLocal(p, q, a, self.term_box(b)?)
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
            ArrayIterator(t) => ArrayIterator(self.term_box(t)?),
            ArrIter(a) => ArrIter(self.term_box(a)?),
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
            Combine(inplace, a, b) => {
                let mut a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (a.as_mut(), b.as_ref()) {
                    (Fields(x), Fields(y)) => {
                        let l = x.len();
                        // TODO: eliminate clone
                        x.extend(y.iter().map(|(n, tm)| (n.clone(), tm.clone())));
                        if inplace && x.len() > l {
                            return Err(FieldsNonExtendable(*b, self.loc));
                        }
                        *a
                    }
                    _ => Combine(inplace, a, b),
                }
            }
            RowOrd(a, d, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                if let (Fields(a), Fields(b)) = (a.as_ref(), b.as_ref()) {
                    let mut u = self.unifier();
                    match d {
                        Dir::Le => u.fields_ord(a, b)?,
                        Dir::Ge => u.fields_ord(b, a)?,
                    };
                }
                RowOrd(a, d, b)
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
            Switch(a, cs) => {
                let a = self.term_box(a)?;
                match a.as_ref() {
                    Variant(r) => match r.as_ref() {
                        Fields(f) => {
                            // TODO: eliminate clone
                            let (n, x) = f.iter().next().unwrap();
                            let (v, tm) = cs.get(n).unwrap();
                            self.rho.insert(v.clone(), Box::new(x.clone()));
                            self.term(tm.clone())?
                        }
                        _ => Switch(a, self.case_map(cs)?),
                    },
                    _ => Switch(a, self.case_map(cs)?),
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
            RowEq(_, _) => Some(RowRefl),
            RowOrd(_, _, _) => Some(RowSat),
            ImplementsOf(_, _) => Some(ImplementsSat),
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

        let meths = match x.class_methods(self.sigma) {
            Some(meths) => meths,
            None => return Err(UnsatisfiedConstraint(i.clone(), x.clone(), self.loc)),
        };
        for f in fns {
            let m_ty = match meths.get(f.as_str()) {
                Some(m) => self.sigma.get(m).unwrap().to_type(),
                None => return Err(ClassMethodNotImplemented(f, i.clone(), x.clone(), self.loc)),
            };
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

        let meth = match ty.class_methods(self.sigma) {
            Some(meths) => meths.get(f.as_str()).unwrap().clone(),
            None => return Err(UnresolvedImplementation(ty, self.loc)),
        };
        Ok(self.sigma.get(&meth).unwrap().to_term(meth))
    }

    fn is_reflector(&self, i: &Var) -> bool {
        return &self.ubiquitous.get("Reflector").unwrap().1 == i;
    }
}
