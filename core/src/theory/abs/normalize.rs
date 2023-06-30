use crate::theory::abs::builtin::Builtins;
use crate::theory::abs::data::{CaseMap, Dir, FieldMap, Term};
use crate::theory::abs::def::{Body, Rho, Sigma};
use crate::theory::abs::rename::rename;
use crate::theory::abs::unify::Unifier;
use crate::theory::conc::data::ArgInfo;
use crate::theory::conc::data::ArgInfo::UnnamedExplicit;
use crate::theory::{Loc, Param, Var};
use crate::Error;
use crate::Error::{ExpectedReflectable, UnresolvedImplementation};

const PROP_NAME: &str = "name";
const PROP_KIND: &str = "kind";
const PROP_VALUE: &str = "value";
const PROP_PROPS: &str = "props";
const PROP_VARIANTS: &str = "variants";

pub struct Normalizer<'a> {
    builtins: &'a Builtins,
    sigma: &'a mut Sigma,
    rho: Rho,
    loc: Loc,
}

impl<'a> Normalizer<'a> {
    pub fn new(builtins: &'a Builtins, sigma: &'a mut Sigma, loc: Loc) -> Self {
        Self {
            builtins,
            sigma,
            rho: Default::default(),
            loc,
        }
    }

    fn unifier(&mut self) -> Unifier {
        Unifier::new(self.builtins, self.sigma, self.loc)
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
            Let(p, a, b) => {
                let a = self.term_box(a)?;
                if let MetaRef(_, _, _) = *a {
                    Let(p, a, self.term_box(b)?)
                } else {
                    self.rho.insert(p.var, a);
                    self.term(*b)?
                }
            }
            Pi(p, b) => Pi(self.param(p)?, self.term_box(b)?),
            Lam(p, b) => Lam(self.param(p)?, self.term_box(b)?),
            App(f, ai, x) => {
                let f = self.term_box(f)?;
                let x = self.term_box(x)?;
                if let Lam(p, b) = *f {
                    self.rho.insert(p.var, x);
                    self.term(*b)?
                } else {
                    App(f, ai, x)
                }
            }
            Sigma(p, b) => Sigma(self.param(p)?, self.term_box(b)?),
            Tuple(a, b) => Tuple(self.term_box(a)?, self.term_box(b)?),
            TupleLet(p, q, a, b) => {
                let a = self.term_box(a)?;
                if let Tuple(x, y) = *a {
                    self.rho.insert(p.var, x);
                    self.rho.insert(q.var, y);
                    self.term(*b)?
                } else {
                    TupleLet(p, q, a, self.term_box(b)?)
                }
            }
            UnitLet(a, b) => {
                let a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match *a {
                    TT => *b,
                    _ => UnitLet(a, b),
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
            Combine(a, b) => {
                let mut a = self.term_box(a)?;
                let b = self.term_box(b)?;
                match (a.as_mut(), b.as_ref()) {
                    (Fields(x), Fields(y)) => {
                        // TODO: eliminate clone
                        x.extend(y.iter().map(|(n, tm)| (n.clone(), tm.clone())));
                        *a
                    }
                    _ => Combine(a, b),
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
            Vptr(r, ts) => {
                let types = ts
                    .into_iter()
                    .map(|t| self.term(t))
                    .collect::<Result<Vec<_>, _>>()?;
                Vptr(r, types)
            }
            Vp(r, ts) => {
                let types = ts
                    .into_iter()
                    .map(|t| self.term(t))
                    .collect::<Result<Vec<_>, _>>()?;
                Vp(r, types)
            }
            Lookup(a) => Lookup(self.term_box(a)?),
            ImplementsOf(a, i) => {
                let a = self.term_box(a)?;
                if !matches!(*a, Ref(_) | MetaRef(_, _, _)) {
                    self.check_constraint(&a, &i)?;
                }
                ImplementsOf(a, i)
            }
            Find(ty, i, f) => {
                let ty = self.term_box(ty)?;
                if !matches!(*ty, Ref(_) | MetaRef(_, _, _)) {
                    return self.find_implementation(*ty, i, f);
                }
                Find(ty, i, f)
            }
            Reflect(a) => {
                let ty = *self.term_box(a)?;
                *self.reflect_type(ty, true)?
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

        let ims = match &self.sigma.get(i).unwrap().body {
            Interface { ims, .. } => ims.clone(),
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
        Err(UnresolvedImplementation(x.clone(), self.loc))
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

        Err(UnresolvedImplementation(ty, self.loc))
    }

    fn reflect_type(&self, ty: Term, has_value: bool) -> Result<Box<Term>, Error> {
        use Term::*;
        Ok(match ty {
            Object(f) => self.reflect_object(*f, has_value)?,
            Enum(f) => self.reflect_enum(*f, has_value)?,

            Unit => self.reflect_simple(Unit),
            Boolean => self.reflect_simple(Boolean),
            String => self.reflect_simple(String),
            Number => self.reflect_simple(Number),
            BigInt => self.reflect_simple(BigInt),

            Ref(a) => Box::new(Reflect(Box::new(Ref(a)))),

            a => return Err(ExpectedReflectable(a, self.loc)),
        })
    }

    fn rep_kind(&self) -> Term {
        Term::Undef(self.builtins.ubiquitous.get("RepKind").unwrap().1.clone())
    }

    fn reflect_object(&self, fields: Term, has_value: bool) -> Result<Box<Term>, Error> {
        use Term::*;
        let fields = match fields {
            Fields(fields) => fields,
            a => return Err(ExpectedReflectable(a, self.loc)),
        };
        let mut ret = FieldMap::from([(PROP_KIND.to_string(), self.rep_kind())]);
        if has_value {
            ret.insert(
                PROP_VALUE.to_string(),
                Object(Box::new(Fields(fields.clone()))),
            );
        }
        let mut props = FieldMap::new();
        for (name, ty) in fields {
            props.insert(
                name,
                Object(Box::new(Fields(FieldMap::from([
                    (PROP_NAME.to_string(), String),
                    (PROP_KIND.to_string(), *self.reflect_field_type(ty)?),
                ])))),
            );
        }
        ret.insert(PROP_PROPS.to_string(), Object(Box::new(Fields(props))));
        Ok(Box::new(Object(Box::new(Fields(ret)))))
    }

    fn prefix_field(mut name: String, prefix: &str) -> String {
        name.insert_str(name.find('_').map_or(0, |x| x + 1), prefix);
        name
    }

    fn reflect_enum(&self, fields: Term, has_value: bool) -> Result<Box<Term>, Error> {
        use Term::*;
        let fields = match fields {
            Fields(fields) => fields,
            a => return Err(ExpectedReflectable(a, self.loc)),
        };
        let mut ret = FieldMap::from([(PROP_KIND.to_string(), self.rep_kind())]);
        if has_value {
            ret.insert(
                PROP_VALUE.to_string(),
                Enum(Box::new(Fields(fields.clone()))),
            );
        }
        let mut variants = FieldMap::new();
        for (name, ty) in fields {
            variants.insert(
                Self::prefix_field(name, "case"),
                Object(Box::new(Fields(FieldMap::from([
                    (PROP_NAME.to_string(), String),
                    (PROP_KIND.to_string(), *self.reflect_field_type(ty)?),
                ])))),
            );
        }
        ret.insert(
            PROP_VARIANTS.to_string(),
            Object(Box::new(Fields(variants))),
        );
        Ok(Box::new(Object(Box::new(Fields(ret)))))
    }

    fn reflect_field_type(&self, ty: Term) -> Result<Box<Term>, Error> {
        use Term::*;
        Ok(match ty {
            Unit | Boolean | String | Number | BigInt => Box::new(self.rep_kind()),
            a => self.reflect_type(a, false)?,
        })
    }

    fn reflect_simple(&self, ty: Term) -> Box<Term> {
        use Term::*;
        Box::new(Object(Box::new(Fields(FieldMap::from([
            (PROP_KIND.to_string(), self.rep_kind()),
            (PROP_VALUE.to_string(), ty),
        ])))))
    }
}
