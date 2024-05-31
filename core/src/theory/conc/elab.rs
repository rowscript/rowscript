use log::{debug, info, trace};

use crate::maybe_grow;
use crate::theory::abs::builtin::Builtins;
use crate::theory::abs::data::{CaseMap, FieldMap, MetaKind, PartialClass, Term};
use crate::theory::abs::def::{gamma_to_tele, tele_to_refs, Body, ImplementsBody};
use crate::theory::abs::def::{Def, Gamma, Sigma};
use crate::theory::abs::normalize::Normalizer;
use crate::theory::abs::rename::rename;
use crate::theory::abs::unify::Unifier;
use crate::theory::conc::data::ArgInfo::{NamedImplicit, UnnamedExplicit, UnnamedImplicit};
use crate::theory::conc::data::{ArgInfo, Expr};
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::{Loc, NameMap, Param, Tele, Var, VarGen, ARRAY, UNTUPLED_RHS_PREFIX};
use crate::Error;
use crate::Error::{
    ExpectedEnum, ExpectedImplementsOf, ExpectedInterface, ExpectedObject, ExpectedPi,
    ExpectedSigma, NonExhaustive, NonVariadicType, UnresolvedField, UnresolvedImplicitParam,
    UnresolvedVar,
};

#[derive(Debug)]
pub struct Elaborator {
    pub ubiquitous: NameMap,
    pub sigma: Sigma,
    gamma: Gamma,

    vg: VarGen,

    checking_ret: Option<Term>,
    checking_class_type_args: Option<Box<[Term]>>,
}

impl Elaborator {
    fn unifier(&mut self, loc: Loc) -> Unifier {
        Unifier::new(&self.ubiquitous, &mut self.sigma, loc)
    }

    fn nf(&mut self, loc: Loc) -> Normalizer {
        Normalizer::new(&self.ubiquitous, &mut self.sigma, loc)
    }

    pub fn defs(&mut self, defs: Vec<Def<Expr>>) -> Result<Vec<Def<Term>>, Error> {
        let mut ret = Vec::default();
        for d in defs {
            ret.push(self.def(d)?);
        }
        Ok(ret)
    }

    fn def(&mut self, d: Def<Expr>) -> Result<Def<Term>, Error> {
        use Body::*;

        info!(target: "elab", "checking definition: {}", d.name);

        // Help to sugar the associated type argument insertion, see `self.try_sugar_type_args`.
        if let Method { class, .. } = &d.body {
            self.checking_class_type_args =
                Some(tele_to_refs(&self.sigma.get(class).unwrap().tele));
        }

        let mut checked = Vec::default();
        let mut tele = Tele::default();
        for p in d.tele {
            let gamma_var = p.var.clone();
            let checked_var = p.var.clone();
            let var = p.var.clone();

            let gamma_typ = self.check(*p.typ, &Term::Univ)?;
            let typ = Box::new(gamma_typ.clone());

            self.gamma.insert(gamma_var, Box::new(gamma_typ));
            checked.push(checked_var);
            tele.push(Param {
                var,
                info: p.info,
                typ,
            })
        }

        // Help to sugar the associated type argument insertion, see `self.try_sugar_type_args`.
        if matches!(d.body, Class { .. }) {
            self.checking_class_type_args = Some(tele_to_refs(&tele));
        }

        let ret = self.check(*d.ret, &Term::Univ)?;
        self.checking_ret = Some(ret.clone());
        self.sigma.insert(
            d.name.clone(),
            Def {
                loc: d.loc,
                name: d.name.clone(),
                tele,
                ret: Box::new(ret.clone()),
                body: Undefined,
            },
        );

        let mut inferred_ret = None;
        let body = match d.body {
            Fn { f } => Fn {
                f: Box::new(self.check(*f, &ret)?),
            },
            Postulate => Postulate,
            Alias(t) => Alias(Box::new(self.check(*t, &ret)?)),
            Const(anno, f) => Const(
                anno,
                Box::new(if anno {
                    self.check(*f, &ret)?
                } else {
                    let (tm, ty) = self.infer(*f)?;
                    inferred_ret = Some(Box::new(ty));
                    tm
                }),
            ),
            Verify(a) => {
                let expected = self.sigma.get(&d.name).unwrap().to_type();
                Verify(Box::new(self.verify(d.loc, *a, expected)?))
            }

            Interface { fns, ims } => Interface { fns, ims },
            Implements(body) => Implements(self.check_implements_body(&d.name, *body)?),
            ImplementsFn(f) => ImplementsFn(Box::new(self.check(*f, &ret)?)),
            Findable(i) => Findable(i),

            Class {
                ctor,
                associated,
                members,
                methods,
            } => {
                let mut checked_members = Vec::default();
                for (loc, id, typ) in members {
                    checked_members.push((loc, id, self.check(typ, &ret)?));
                }
                Class {
                    ctor,
                    associated,
                    members: checked_members,
                    methods,
                }
            }
            Associated(t) => Associated(Box::new(self.check(*t, &ret)?)),
            Method {
                class,
                associated,
                f,
            } => Method {
                class,
                associated,
                f: Box::new(self.check(*f, &ret)?),
            },

            Undefined | Meta(..) => unreachable!(),
        };

        for n in checked {
            self.gamma.remove(&n);
        }

        let checked = self.sigma.get_mut(&d.name).unwrap();
        checked.body = body;
        if let Some(ret) = inferred_ret {
            checked.ret = ret;
        }
        self.checking_ret = None;
        self.checking_class_type_args = None;

        debug!(target: "elab", "definition checked successfully: {checked}");

        Ok(checked.clone())
    }

    fn check_implements_body(
        &mut self,
        d: &Var,
        body: ImplementsBody<Expr>,
    ) -> Result<Box<ImplementsBody<Term>>, Error> {
        use Body::*;
        use Expr::*;

        let (i, im) = body.i;
        let ret = Box::new(ImplementsBody {
            i: (i, Box::new(self.infer(*im)?.0)),
            fns: body.fns,
        });
        let im_tm = ret.implementor_type(&self.sigma)?;

        let i_def = self.sigma.get_mut(&ret.i.0).unwrap();
        let i_def_loc = i_def.loc;
        match &mut i_def.body {
            Interface { fns, ims, .. } => {
                ims.push(d.clone());
                for f in fns {
                    if ret.fns.contains_key(f) {
                        continue;
                    }
                    return Err(NonExhaustive(im_tm, i_def_loc));
                }
            }
            _ => return Err(ExpectedInterface(Term::Ref(ret.i.0.clone()), i_def_loc)),
        };

        for (i_fn, im_fn) in &ret.fns {
            let i_fn_def = self.sigma.get(i_fn).unwrap();

            let i_loc = i_fn_def.loc;
            let im_loc = self.sigma.get(im_fn).unwrap().loc;

            let (i_fn_ty_p, i_fn_ty_b) = match i_fn_def.to_type() {
                Term::Pi(p, _, b) => (p, b),
                _ => unreachable!(),
            };
            let i_fn_ty_applied = self
                .nf(i_loc)
                .with(&[(&i_fn_ty_p.var, &im_tm)], *i_fn_ty_b)?;
            let (_, im_fn_ty) = self.infer(Resolved(im_loc, im_fn.clone()))?;

            self.unifier(im_loc).unify(&i_fn_ty_applied, &im_fn_ty)?;
        }

        Ok(ret)
    }

    fn check_anno(&mut self, a: Expr, maybe_typ: Option<Box<Expr>>) -> Result<(Term, Term), Error> {
        Ok(if let Some(t) = maybe_typ {
            let checked_ty = self.check(*t, &Term::Univ)?;
            (self.check(a, &checked_ty)?, checked_ty)
        } else {
            self.infer(a)?
        })
    }

    fn check(&mut self, e: Expr, ty: &Term) -> Result<Term, Error> {
        maybe_grow(move || {
            self.check_impl(e, ty).inspect(|tm| {
                debug!(target: "elab", "expression checked successfully: tm={tm}, ty={ty}");
            })
        })
    }

    fn check_impl(&mut self, e: Expr, ty: &Term) -> Result<Term, Error> {
        use Expr::*;
        trace!(target: "elab", "checking expression: e={e}, ty={ty}");
        Ok(match e {
            Local(_, var, maybe_typ, a, b) => {
                let (tm, typ) = self.check_anno(*a, maybe_typ)?;
                let param = Param {
                    var,
                    info: Explicit,
                    typ: Box::new(typ),
                };
                let body = self.guarded_check(&[&param], *b, ty)?;
                Term::Local(param, Box::new(tm), Box::new(body))
            }
            LocalSet(_, var, maybe_typ, a, b) => {
                let (tm, typ) = self.check_anno(*a, maybe_typ)?;
                let param = Param {
                    var,
                    info: Explicit,
                    typ: Box::new(typ),
                };
                let body = self.guarded_check(&[&param], *b, ty)?;
                Term::LocalSet(param, Box::new(tm), Box::new(body))
            }
            LocalUpdate(_, v, a, b) => {
                let a_ty = self.gamma.get(&v).unwrap().clone();
                let a = self.check(*a, &a_ty)?;
                let b = self.check(*b, ty)?;
                Term::LocalUpdate(v, Box::new(a), Box::new(b))
            }
            While(_, p, b, r) => {
                let p = self.check(*p, &Term::Boolean)?;
                let b = self.check(*b, &Term::Unit)?;
                let r = self.check(*r, ty)?;
                Term::While(Box::new(p), Box::new(b), Box::new(r))
            }
            Fori(_, b, r) => {
                let b = self.check(*b, &Term::Unit)?;
                let r = self.check(*r, ty)?;
                Term::Fori(Box::new(b), Box::new(r))
            }
            Guard(_, p, b, e, r) => {
                let p = self.check(*p, &Term::Boolean)?;
                let b = self.check(*b, &Term::Unit)?;
                let e = if let Some(e) = e {
                    Some(Box::new(self.check(*e, &Term::Unit)?))
                } else {
                    None
                };
                let r = self.check(*r, ty)?;
                Term::Guard(Box::new(p), Box::new(b), e, Box::new(r))
            }
            Lam(loc, var, body) => {
                let pi = self.nf(loc).term(ty.clone())?;
                match pi {
                    Term::Pi(ty_param, _, ty_body) => {
                        let param = Param {
                            var: var.clone(),
                            info: Explicit,
                            typ: ty_param.typ.clone(),
                        };
                        let body_type = self
                            .nf(loc)
                            .with(&[(&ty_param.var, &Term::Ref(var))], *ty_body)?;
                        let checked_body = self.guarded_check(&[&param], *body, &body_type)?;
                        Term::Lam(param.clone(), Default::default(), Box::new(checked_body))
                    }
                    ty => return Err(ExpectedPi(ty, loc)),
                }
            }
            Tuple(loc, a, b) => {
                let sig = self.nf(loc).term(ty.clone())?;
                match sig {
                    Term::Sigma(p, body) => match p.typ.as_ref() {
                        Term::Varargs(t) => {
                            let args = match *a {
                                Spread(_, a) => *a,
                                a => {
                                    let mut args = vec![a];
                                    let mut rest = b;
                                    loop {
                                        match *rest {
                                            TT(..) => break,
                                            Tuple(.., arg, body) => {
                                                args.push(*arg);
                                                rest = body;
                                            }
                                            _ => unreachable!(),
                                        }
                                    }
                                    App(
                                        loc,
                                        Box::new(self.array_ctor_ref(loc)),
                                        UnnamedExplicit,
                                        Box::new(Tuple(
                                            loc,
                                            Box::new(Arr(loc, args)),
                                            Box::new(TT(loc)),
                                        )),
                                    )
                                }
                            };
                            Term::Tuple(Box::new(self.check(args, t)?), Box::new(Term::TT))
                        }
                        _ => {
                            let a = self.check(*a, &p.typ)?;
                            let body = self.nf(loc).with(&[(&p.var, &a)], *body)?;
                            Term::Tuple(Box::new(a), Box::new(self.check(*b, &body)?))
                        }
                    },
                    Term::AnonVarargs(ty) => {
                        let (a, a_ty) = self.infer(Tuple(loc, a, b))?;
                        self.unifier(loc).unify(&ty, &a_ty)?;
                        a
                    }
                    ty => return Err(ExpectedSigma(ty, loc)),
                }
            }
            TupleLocal(_, x, y, a, b) => {
                let a_loc = a.loc();
                let (a, a_ty) = self.infer(*a)?;
                match a_ty {
                    Term::Sigma(ty_param, typ) => {
                        let x = Param {
                            var: x,
                            info: Explicit,
                            typ: ty_param.typ,
                        };
                        let y = Param {
                            var: y,
                            info: Explicit,
                            typ,
                        };
                        let b = self.guarded_check(&[&x, &y], *b, ty)?;
                        Term::TupleLocal(x, y, Box::new(a), Box::new(b))
                    }
                    ty => return Err(ExpectedSigma(ty, a_loc)),
                }
            }
            UnitLocal(_, a, b) => Term::UnitLocal(
                Box::new(self.check(*a, &Term::Unit)?),
                Box::new(self.check(*b, ty)?),
            ),
            If(_, p, t, e) => Term::If(
                Box::new(self.check(*p, &Term::Boolean)?),
                Box::new(self.check(*t, ty)?),
                Box::new(self.check(*e, ty)?),
            ),
            Downcast(loc, a) => {
                let (a, a_ty) = self.infer(*a)?;
                let to = match self.nf(loc).term(ty.clone())? {
                    Term::Object(to) => to,
                    ty => return Err(ExpectedObject(ty, loc)),
                };
                match a_ty {
                    Term::Object(_) => Term::Down(Box::new(a), to),
                    ty => return Err(ExpectedObject(ty, loc)),
                }
            }
            Upcast(loc, a) => {
                let (a, a_ty) = self.infer(*a)?;
                let to = match self.nf(loc).term(ty.clone())? {
                    Term::Enum(to) => to,
                    ty => return Err(ExpectedEnum(ty, loc)),
                };
                match a_ty {
                    Term::Enum(from) => Term::Up(Box::new(a), from, to),
                    ty => return Err(ExpectedEnum(ty, loc)),
                }
            }
            _ => {
                let loc = e.loc();
                let f_e = e.clone();

                let (mut inferred_tm, inferred_ty) = self.infer(e)?;
                let mut inferred = self.nf(loc).term(inferred_ty)?;
                let expected = self.nf(loc).term(ty.clone())?;

                if Self::is_hole_insertable(&expected) {
                    if let Some(f_e) = Self::app_insert_holes(f_e, UnnamedExplicit, &inferred)? {
                        let (new_tm, new_ty) = self.infer(f_e)?;
                        inferred_tm = new_tm;
                        inferred = new_ty;
                    }
                }

                self.unifier(loc).unify(&expected, &inferred)?;

                inferred_tm
            }
        })
    }

    fn infer(&mut self, e: Expr) -> Result<(Term, Term), Error> {
        maybe_grow(move || {
            self.infer_impl(e).map(|(tm, ty)| {
                debug!(target: "elab", "expression inferred successfully: tm={tm}, ty={ty}");
                Term::unwrap_solved_implicit_lambda(tm, ty)
            })
        })
    }

    fn infer_impl(&mut self, e: Expr) -> Result<(Term, Term), Error> {
        use Expr::*;
        use MetaKind::*;
        trace!(target: "elab", "inferring expression: e={e}");
        Ok(match e {
            Resolved(loc, v) => match self.gamma.get(&v) {
                Some(ty) => (Term::Ref(v), *ty.clone()),
                None => {
                    let d = self.sigma.get(&v).unwrap();
                    let tm = d.to_term(v);
                    let ty = d.to_type();
                    if matches!(d.body, Body::Associated(..)) {
                        self.try_sugar_type_args(loc, tm, ty)?
                    } else {
                        (tm, ty)
                    }
                }
            },
            Imported(_, v) => {
                let ty = self.sigma.get(&v).unwrap().to_type();
                (Term::Ref(v), ty)
            }
            Qualified(_, m, v) => {
                let ty = self.sigma.get(&v).unwrap().to_type();
                (Term::Qualified(m, v), ty)
            }
            Hole(loc) => self.insert_meta(loc, UserMeta),
            InsertedHole(loc) => self.insert_meta(loc, InsertedMeta),
            Return(_, a) => {
                let a = self.check(*a, &self.checking_ret.clone().unwrap())?;
                (Term::Return(Box::new(a)), Term::Unit)
            }
            Continue(_) => (Term::Continue, Term::Unit),
            Break(_) => (Term::Break, Term::Unit),
            Pi(_, p, b) => {
                let (param_ty, _) = self.infer(*p.typ)?;
                let param = Param {
                    var: p.var,
                    info: p.info,
                    typ: Box::new(param_ty),
                };
                let (b, b_ty) = self.guarded_infer(&[&param], *b)?;
                (Term::Pi(param, Default::default(), Box::new(b)), b_ty)
            }
            Lam(loc, var, b) => {
                let mut typ = Box::new(Term::Unit);
                let mut body = b.as_ref();
                // Our lambda parameters are mostly tupled, hence we could cheat here.
                loop {
                    match body {
                        TupleLocal(_, x, y, _, b)
                            if y.as_str().starts_with(UNTUPLED_RHS_PREFIX) =>
                        {
                            typ = Box::new(Term::Sigma(
                                Param {
                                    var: x.clone(),
                                    info: Explicit,
                                    typ: Box::new(self.insert_meta(loc, InsertedMeta).0),
                                },
                                typ,
                            ));
                            body = b.as_ref();
                        }
                        _ => break,
                    }
                }
                let p = Param {
                    var,
                    info: Explicit,
                    typ,
                };
                let (b, b_ty) = self.guarded_infer(&[&p], *b)?;
                (
                    Term::Lam(p.clone(), Default::default(), Box::new(b)),
                    Term::Pi(p, Default::default(), Box::new(b_ty)),
                )
            }
            App(_, f, ai, x) => {
                let f_loc = f.loc();
                let f_e = f.clone();
                let (f, f_ty) = self.infer(*f)?;

                if let Some(f_e) = Self::app_insert_holes(*f_e, ai.clone(), &f_ty)? {
                    return self.infer(App(f_loc, Box::new(f_e), ai, x));
                }

                match f_ty {
                    Term::Pi(p, _, b) => {
                        let x = self.guarded_check(
                            &[&Param {
                                var: p.var.clone(),
                                info: p.info,
                                typ: p.typ.clone(),
                            }],
                            *x,
                            &p.typ,
                        )?;
                        let applied_ty = self.nf(f_loc).with(&[(&p.var, &x)], *b)?;
                        let applied = self.nf(f_loc).apply(f, p.info.into(), &[x])?;
                        (applied, applied_ty)
                    }
                    ty => return Err(ExpectedPi(ty, f_loc)),
                }
            }
            RevApp(loc, f, x) => {
                if let Term::Sigma(p, _) = self.infer(*x.clone())?.1 {
                    if let Some(PartialClass { methods, .. }) = p.typ.class_methods(&self.sigma) {
                        let (f_loc, f_var, globally_found) = match *f {
                            Resolved(f_loc, v) => (f_loc, v, true),
                            Unresolved(f_loc, _, v) => (f_loc, v, false),
                            _ => unreachable!(),
                        };
                        return self.infer(App(
                            loc,
                            Box::new(match methods.get(f_var.as_str()) {
                                Some(v) => Resolved(f_loc, v.clone()),
                                None if globally_found => Resolved(f_loc, f_var),
                                _ => return Err(UnresolvedVar(f_loc)),
                            }),
                            UnnamedExplicit,
                            x,
                        ));
                    }
                }
                if let Unresolved(f_loc, ..) = *f {
                    return Err(UnresolvedVar(f_loc));
                }
                self.infer(App(loc, f, UnnamedExplicit, x))?
            }
            Sigma(_, p, b) => {
                let (param_ty, _) = self.infer(*p.typ)?;
                let param = Param {
                    var: p.var,
                    info: p.info,
                    typ: Box::new(param_ty),
                };
                let (b, b_ty) = self.guarded_infer(&[&param], *b)?;
                (Term::Sigma(param, Box::new(b)), b_ty)
            }
            Tuple(_, a, b) => {
                let (a, a_ty) = self.infer(*a)?;
                let (b, b_ty) = self.infer(*b)?;
                (
                    Term::Tuple(Box::new(a), Box::new(b)),
                    Term::Sigma(
                        Param {
                            var: Var::unbound(),
                            info: Explicit,
                            typ: Box::new(a_ty),
                        },
                        Box::new(b_ty),
                    ),
                )
            }
            TupleLocal(_, x, y, a, b) => {
                let a_loc = a.loc();
                let x_ty = self.insert_meta(a_loc, InsertedMeta).0;
                let y_ty = self.insert_meta(a_loc, InsertedMeta).0;
                let x = Param {
                    var: x,
                    info: Explicit,
                    typ: Box::new(x_ty),
                };
                let y = Param {
                    var: y,
                    info: Explicit,
                    typ: Box::new(y_ty.clone()),
                };
                let a = self.check(*a, &Term::Sigma(x.clone(), Box::new(y_ty)))?;
                let (b, b_ty) = self.guarded_infer(&[&x, &y], *b)?;
                (Term::TupleLocal(x, y, Box::new(a), Box::new(b)), b_ty)
            }
            UnitLocal(_, a, b) => {
                let a = self.check(*a, &Term::Unit)?;
                let (b, ty) = self.infer(*b)?;
                (Term::UnitLocal(Box::new(a), Box::new(b)), ty)
            }
            Arr(loc, xs) => {
                let mut v_ty = None;
                let mut checked = Vec::default();
                for (i, x) in xs.into_iter().enumerate() {
                    if i > 0 {
                        checked.push(self.check(x, v_ty.as_ref().unwrap())?);
                        continue;
                    }
                    let (x_tm, x_ty) = self.infer(x)?;
                    v_ty = Some(x_ty);
                    checked.push(x_tm);
                }
                if checked.is_empty() {
                    (
                        Term::Arr(Default::default()),
                        self.insert_meta(loc, InsertedMeta).0,
                    )
                } else {
                    (Term::Arr(checked), Term::Array(Box::new(v_ty.unwrap())))
                }
            }
            Kv(loc, xs) => {
                let mut k_ty = None;
                let mut v_ty = None;
                let mut checked = Vec::default();
                for (i, (k, v)) in xs.into_iter().enumerate() {
                    if i > 0 {
                        checked.push((
                            self.check(k, k_ty.as_ref().unwrap())?,
                            self.check(v, v_ty.as_ref().unwrap())?,
                        ));
                        continue;
                    }
                    let (key, key_ty) = self.infer(k)?;
                    let (val, val_ty) = self.infer(v)?;
                    k_ty = Some(key_ty);
                    v_ty = Some(val_ty);
                    checked.push((key, val));
                }
                if checked.is_empty() {
                    (
                        Term::Kv(Default::default()),
                        self.insert_meta(loc, InsertedMeta).0,
                    )
                } else {
                    (
                        Term::Kv(checked),
                        Term::Map(Box::new(k_ty.unwrap()), Box::new(v_ty.unwrap())),
                    )
                }
            }
            Associate(loc, a, n) => (
                Term::Associate(Box::new(self.check(*a, &Term::Univ)?), n),
                self.insert_meta(loc, InsertedMeta).0,
            ),
            Fields(_, fields) => {
                let mut inferred = FieldMap::default();
                for (f, e) in fields {
                    inferred.insert(f, self.infer(e)?.0);
                }
                (Term::Fields(inferred), Term::Row)
            }
            Combine(_, a, b) => {
                let a = self.check(*a, &Term::Row)?;
                let b = self.check(*b, &Term::Row)?;
                (Term::Combine(false, Box::new(a), Box::new(b)), Term::Row)
            }
            RowOrd(_, a, b) => {
                let a = self.check(*a, &Term::Row)?;
                let b = self.check(*b, &Term::Row)?;
                (Term::RowOrd(Box::new(a), Box::new(b)), Term::Univ)
            }
            RowEq(_, a, b) => {
                let a = self.check(*a, &Term::Row)?;
                let b = self.check(*b, &Term::Row)?;
                (Term::RowEq(Box::new(a), Box::new(b)), Term::Univ)
            }
            Object(_, r) => {
                let r = self.check(*r, &Term::Row)?;
                (Term::Object(Box::new(r)), Term::Univ)
            }
            Obj(_, r) => match *r {
                Fields(_, fields) => {
                    let mut tm_fields = FieldMap::default();
                    let mut ty_fields = FieldMap::default();
                    for (n, e) in fields {
                        let (tm, ty) = self.infer(e)?;
                        tm_fields.insert(n.clone(), tm);
                        ty_fields.insert(n, ty);
                    }
                    (
                        Term::Obj(Box::new(Term::Fields(tm_fields))),
                        Term::Object(Box::new(Term::Fields(ty_fields))),
                    )
                }
                _ => unreachable!(),
            },
            Concat(_, a, b) => {
                let x_loc = a.loc();
                let y_loc = b.loc();
                let (x, x_ty) = self.infer(*a)?;
                let (y, y_ty) = self.infer(*b)?;
                let (x_ty, x_associated, x_type_args, x_name) = if let Term::Cls {
                    class,
                    type_args,
                    associated,
                    object,
                } = x_ty
                {
                    (*object, Some(associated), Some(type_args), Some(class))
                } else {
                    (x_ty, None, None, None)
                };
                let ty = match (x_ty, y_ty) {
                    (Term::Object(rx), Term::Object(ry)) => match x_name {
                        Some(n) => Term::Cls {
                            class: n,
                            type_args: x_type_args.unwrap(),
                            associated: x_associated.unwrap(),
                            object: Box::new(Term::Object(Box::new(Term::Combine(true, rx, ry)))),
                        },
                        None => Term::Object(Box::new(Term::Combine(false, rx, ry))),
                    },
                    (Term::Object(_), y_ty) => return Err(ExpectedObject(y_ty, y_loc)),
                    (x_ty, _) => return Err(ExpectedObject(x_ty, x_loc)),
                };
                (Term::Concat(Box::new(x), Box::new(y)), ty)
            }
            Access(_, n) => {
                let t = Var::new("T");
                let a = Var::new("'A");
                let o = Var::new("o");
                let tele = vec![
                    Param {
                        var: t.clone(),
                        info: Implicit,
                        typ: Box::new(Term::Univ),
                    },
                    Param {
                        var: a.clone(),
                        info: Implicit,
                        typ: Box::new(Term::Row),
                    },
                    Param {
                        var: o.clone(),
                        info: Explicit,
                        typ: Box::new(Term::Object(Box::new(Term::Ref(a.clone())))),
                    },
                    Param {
                        var: Var::unbound(),
                        info: Implicit,
                        typ: Box::new(Term::RowOrd(
                            Box::new(Term::Fields(FieldMap::from([(
                                n.clone(),
                                Term::Ref(t.clone()),
                            )]))),
                            Box::new(Term::Ref(a)),
                        )),
                    },
                ];
                (
                    *rename(Box::new(Term::lam(
                        &tele,
                        Term::Access(Box::new(Term::Ref(o)), n),
                    ))),
                    *rename(Box::new(Term::pi(&tele, Term::Ref(t)))),
                )
            }
            Downcast(loc, a) => {
                let (a, ty) = self.infer(*a)?;
                let m = self.insert_meta(loc, InsertedMeta).0;
                match ty {
                    Term::Object(r) => (
                        Term::Down(Box::new(a), Box::new(m.clone())),
                        Term::Downcast(Box::new(Term::Object(r)), Box::new(m)),
                    ),
                    ty => return Err(ExpectedObject(ty, loc)),
                }
            }
            Enum(_, r) => (
                Term::Enum(Box::new(self.check(*r, &Term::Row)?)),
                Term::Univ,
            ),
            Variant(_, n, a) => {
                let (a, a_ty) = self.infer(*a)?;
                let tm = Term::Fields(FieldMap::from([(n.clone(), a)]));
                let ty = Term::Fields(FieldMap::from([(n, a_ty)]));
                (
                    Term::Variant(Box::new(tm)),
                    Term::Upcast(Box::new(Term::Enum(Box::new(ty)))),
                )
            }
            Upcast(loc, a) => {
                let (a, ty) = self.infer(*a)?;
                match ty {
                    Term::Enum(r) => (a, Term::Upcast(Box::new(Term::Enum(r)))),
                    Term::Upcast(r) => (a, Term::Upcast(r)),
                    ty => return Err(ExpectedEnum(ty, loc)),
                }
            }
            Switch(loc, a, cs, d) => {
                let mut ret_ty = None;
                let a_loc = a.loc();
                let (a, a_ty) = self.infer(*a)?;
                let en = self.nf(loc).term(a_ty)?;
                let fields = match &en {
                    Term::Enum(y) => match y.as_ref() {
                        Term::Fields(f) => {
                            if d.is_none() && f.len() != cs.len() {
                                return Err(NonExhaustive(Term::Fields(f.clone()), loc));
                            }
                            Some(f)
                        }
                        _ => None,
                    },
                    _ => return Err(ExpectedEnum(en, a_loc)),
                };
                let mut m = CaseMap::default();
                for (n, v, e) in cs {
                    let ty = match fields {
                        Some(f) => f
                            .get(&n)
                            .ok_or(UnresolvedField(n.clone(), Term::Fields(f.clone()), loc))?
                            .clone(),
                        None => self.insert_meta(e.loc(), InsertedMeta).0,
                    };
                    let pat = Param {
                        var: v.clone(),
                        info: Explicit,
                        typ: Box::new(ty),
                    };
                    let tm = match &ret_ty {
                        None => {
                            let (tm, ty) = self.guarded_infer(&[&pat], e)?;
                            ret_ty = Some(ty);
                            tm
                        }
                        Some(ret) => self.guarded_check(&[&pat], e, ret)?,
                    };
                    m.insert(n, (v, tm));
                }
                let d = match d {
                    Some((v, e)) => {
                        let typ = Box::new(match fields {
                            Some(f) => Term::Enum(Box::new(Term::Fields(f.clone()))),
                            None => en,
                        });
                        let p = Param {
                            var: v.clone(),
                            info: Explicit,
                            typ,
                        };
                        Some((
                            v,
                            Box::new(self.guarded_check(&[&p], *e, ret_ty.as_ref().unwrap())?),
                        ))
                    }
                    None => None,
                };
                (Term::Switch(Box::new(a), m, d), ret_ty.unwrap())
            }
            ImplementsOf(loc, a) => {
                let (tm, ty) = self.infer(*a)?;
                match tm {
                    Term::ImplementsOf(a, i) => (Term::ImplementsOf(a, i), ty),
                    tm => return Err(ExpectedImplementsOf(tm, loc)),
                }
            }
            Varargs(loc, t) => {
                let t = self.check(*t, &Term::Univ)?;
                if !self.is_variadic(&t) {
                    return Err(NonVariadicType(t, loc));
                }
                (Term::Varargs(Box::new(t)), Term::Univ)
            }
            AnonVarargs(_, t) => (
                Term::AnonVarargs(Box::new(self.check(*t, &Term::Univ)?)),
                Term::Univ,
            ),
            Spread(loc, a) => {
                let (a, ty) = self.infer(*a)?;
                if !self.is_variadic(&ty) {
                    return Err(NonVariadicType(ty, loc));
                }
                (Term::Spread(Box::new(a)), ty)
            }

            Univ(_) => (Term::Univ, Term::Univ),
            Unit(_) => (Term::Unit, Term::Univ),
            TT(_) => (Term::TT, Term::Unit),
            Boolean(_) => (Term::Boolean, Term::Univ),
            False(_) => (Term::False, Term::Boolean),
            True(_) => (Term::True, Term::Boolean),
            String(_) => (Term::String, Term::Univ),
            Str(_, v) => (Term::Str(v), Term::String),
            Number(_) => (Term::Number, Term::Univ),
            Num(_, r) => (Term::Num(r.parse().unwrap()), Term::Number),
            BigInt(_) => (Term::BigInt, Term::Univ),
            Big(_, v) => (Term::Big(v), Term::BigInt),
            Row(_) => (Term::Row, Term::Univ),

            _ => unreachable!(),
        })
    }

    fn guarded_check(&mut self, ps: &[&Param<Term>], e: Expr, ty: &Term) -> Result<Term, Error> {
        for &p in ps {
            self.gamma.insert(p.var.clone(), p.typ.clone());
        }
        let ret = self.check(e, &ty.clone())?;
        for p in ps {
            self.gamma.remove(&p.var);
        }
        Ok(ret)
    }

    fn guarded_infer(&mut self, ps: &[&Param<Term>], e: Expr) -> Result<(Term, Term), Error> {
        for &p in ps {
            self.gamma.insert(p.var.clone(), p.typ.clone());
        }
        let ret = self.infer(e)?;
        for p in ps {
            self.gamma.remove(&p.var);
        }
        Ok(ret)
    }

    fn insert_meta(&mut self, loc: Loc, k: MetaKind) -> (Term, Term) {
        use Body::*;

        let ty_meta_var = self.vg.fresh();
        self.sigma.insert(
            ty_meta_var.clone(),
            Def {
                loc,
                name: ty_meta_var.clone(),
                tele: Default::default(),
                ret: Box::new(Term::Univ),
                body: Meta(k.clone(), None),
            },
        );
        let ty = Term::MetaRef(k.clone(), ty_meta_var, Default::default());

        let tm_meta_var = self.vg.fresh();
        let tele = gamma_to_tele(&self.gamma);
        let spine = Term::tele_to_spine(&tele);
        self.sigma.insert(
            tm_meta_var.clone(),
            Def {
                loc,
                name: tm_meta_var.clone(),
                tele,
                ret: Box::new(ty.clone()),
                body: Meta(k.clone(), None),
            },
        );
        (Term::MetaRef(k, tm_meta_var, spine), ty)
    }

    fn is_hole_insertable(expected: &Term) -> bool {
        match expected {
            Term::Pi(p, ..) => p.info != Implicit,
            _ => true,
        }
    }

    fn app_insert_holes(f_e: Expr, i: ArgInfo, f_ty: &Term) -> Result<Option<Expr>, Error> {
        fn holes_to_insert(loc: Loc, name: String, mut ty: &Term) -> Result<usize, Error> {
            let mut ret = Default::default();
            loop {
                match ty {
                    Term::Pi(p, _, b) => {
                        if p.info != Implicit {
                            return Err(UnresolvedImplicitParam(name, loc));
                        }
                        if *p.var.name == name {
                            return Ok(ret);
                        }
                        ty = b;
                        ret += 1;
                    }
                    _ => unreachable!(),
                }
            }
        }

        Ok(match f_ty {
            Term::Pi(p, ..) if p.info == Implicit => match i {
                UnnamedExplicit => Some(Expr::holed_app(f_e)),
                NamedImplicit(name) => match holes_to_insert(f_e.loc(), name.to_string(), f_ty)? {
                    0 => None,
                    n => Some((0..n).fold(f_e, |e, _| Expr::holed_app(e))),
                },
                _ => None,
            },
            _ => None,
        })
    }

    fn verify(&mut self, loc: Loc, target: Expr, expected: Term) -> Result<Term, Error> {
        let (tm, ty) = self.infer(target)?;
        #[cfg(not(test))]
        {
            let _ = loc;
            let _ = expected;
            let _ = ty;
        }
        #[cfg(test)]
        {
            let expected = self.nf(loc).term(expected)?;
            self.unifier(loc).unify(&ty, &expected)?;
        }
        Ok(tm)
    }

    fn try_sugar_type_args(&mut self, loc: Loc, tm: Term, ty: Term) -> Result<(Term, Term), Error> {
        let args = match &self.checking_class_type_args {
            Some(args) => args.clone(),
            None => return Ok((tm, ty)),
        };
        let tm = args.iter().fold(tm, |a, arg| {
            Term::App(Box::new(a), UnnamedImplicit, Box::new(arg.clone()))
        });
        let ty = self.nf(loc).apply_type(ty, args.as_ref())?;
        Ok((tm, ty))
    }

    fn is_variadic(&self, tm: &Term) -> bool {
        let name = match tm {
            Term::Cls { class, .. } => class,
            _ => return false,
        };
        self.ubiquitous
            .get(ARRAY)
            .map_or(Default::default(), |a| name == &a.1)
    }

    fn array_ctor_ref(&self, loc: Loc) -> Expr {
        let name = Var::new(ARRAY).ctor();
        Expr::Resolved(loc, self.ubiquitous.get(name.as_str()).unwrap().1.clone())
    }
}

impl Default for Elaborator {
    fn default() -> Self {
        let Builtins { ubiquitous, sigma } = Builtins::new();
        Self {
            ubiquitous,
            sigma,
            gamma: Default::default(),
            vg: Default::default(),
            checking_ret: Default::default(),
            checking_class_type_args: Default::default(),
        }
    }
}
