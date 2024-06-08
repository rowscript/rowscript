use log::{debug, info, trace};

use crate::maybe_grow;
use crate::theory::abs::builtin::Builtins;
use crate::theory::abs::data::{CaseMap, FieldMap, FieldSet, MetaKind, PartialClass, Term};
use crate::theory::abs::def::{gamma_to_tele, tele_to_refs, Body, InstanceBody};
use crate::theory::abs::def::{Def, Gamma, Sigma};
use crate::theory::abs::normalize::Normalizer;
use crate::theory::abs::rename::rename;
use crate::theory::abs::unify::Unifier;
use crate::theory::conc::data::ArgInfo::{NamedImplicit, UnnamedExplicit, UnnamedImplicit};
use crate::theory::conc::data::{ArgInfo, Expr};
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::{
    Loc, NameMap, Param, Tele, Var, VarGen, ARRAY, ASYNC, UNTUPLED_ENDS, UNTUPLED_RHS_PREFIX,
};
use crate::Error;
use crate::Error::{
    ExpectedEnum, ExpectedInstanceof, ExpectedInterface, ExpectedObject, ExpectedPi, ExpectedSigma,
    NonExhaustive, NonVariadicType, UnresolvedField, UnresolvedImplicitParam, UnresolvedVar,
};

#[derive(Debug)]
pub struct Elaborator {
    pub ubiquitous: NameMap,
    pub sigma: Sigma,
    gamma: Gamma,

    vg: VarGen,

    checking_eff: Option<Term>,
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

            let gamma_typ = self.check(*p.typ, &Term::Pure, &Term::Univ)?;
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

        let eff = self.check(*d.eff, &Term::Pure, &Term::Row)?;
        let ret = self.check(*d.ret, &Term::Pure, &Term::Univ)?;
        self.checking_eff = Some(eff.clone());
        self.checking_ret = Some(ret.clone());
        self.sigma.insert(
            d.name.clone(),
            Def {
                loc: d.loc,
                name: d.name.clone(),
                tele,
                eff: Box::new(eff.clone()),
                ret: Box::new(ret.clone()),
                body: Undefined,
            },
        );

        let mut inferred_eff = None;
        let mut inferred_ret = None;
        let body = match d.body {
            Fn(f) => Fn(Box::new(self.check(*f, &eff, &ret)?)),
            Postulate => Postulate,
            Alias(t) => Alias(Box::new(self.check(*t, &eff, &ret)?)),
            Constant(anno, f) => Constant(
                anno,
                Box::new(if anno {
                    self.check(*f, &eff, &ret)?
                } else {
                    let InferResult { tm, ty, eff } = self.infer(*f)?;
                    inferred_eff = Some(Box::new(eff));
                    inferred_ret = Some(Box::new(ty));
                    tm
                }),
            ),
            Verify(a) => {
                let d = self.sigma.get(&d.name).unwrap();
                let expected_eff = d.to_eff();
                let expected_ty = d.to_type();
                Verify(Box::new(self.verify(
                    d.loc,
                    *a,
                    expected_eff,
                    expected_ty,
                )?))
            }

            Interface {
                is_capability,
                fns,
                instances,
            } => Interface {
                is_capability,
                fns,
                instances,
            },
            Instance(body) => Instance(self.check_instance_body(&d.name, *body)?),
            InstanceFn(f) => InstanceFn(Box::new(self.check(*f, &eff, &ret)?)),
            Findable(i) => Findable(i),

            Class {
                ctor,
                associated,
                members,
                methods,
            } => {
                let mut checked_members = Vec::default();
                for (loc, id, typ) in members {
                    checked_members.push((loc, id, self.check(typ, &eff, &ret)?));
                }
                Class {
                    ctor,
                    associated,
                    members: checked_members,
                    methods,
                }
            }
            Associated(t) => Associated(Box::new(self.check(*t, &eff, &ret)?)),
            Method {
                class,
                associated,
                f,
            } => Method {
                class,
                associated,
                f: Box::new(self.check(*f, &eff, &ret)?),
            },

            Undefined | Meta(..) => unreachable!(),
        };

        for n in checked {
            self.gamma.remove(&n);
        }

        let checked = self.sigma.get_mut(&d.name).unwrap();
        checked.body = body;
        if let Some(eff) = inferred_eff {
            checked.eff = eff;
        }
        if let Some(ret) = inferred_ret {
            checked.ret = ret;
        }
        self.checking_eff = None;
        self.checking_ret = None;
        self.checking_class_type_args = None;

        debug!(target: "elab", "definition checked successfully: {checked}");

        Ok(checked.clone())
    }

    fn check_instance_body(
        &mut self,
        d: &Var,
        body: InstanceBody<Expr>,
    ) -> Result<Box<InstanceBody<Term>>, Error> {
        use Body::*;
        use Expr::*;

        let (i, inst) = body.i;
        let ret = Box::new(InstanceBody {
            i: (i, Box::new(self.infer(*inst)?.tm)),
            fns: body.fns,
        });
        let inst_tm = ret.instance_type(&self.sigma)?;

        let i_def = self.sigma.get_mut(&ret.i.0).unwrap();
        let i_def_loc = i_def.loc;
        match &mut i_def.body {
            Interface {
                is_capability,
                fns,
                instances,
            } => {
                if *is_capability {
                    return Err(ExpectedInterface(Term::Ref(ret.i.0.clone()), i_def_loc));
                }
                instances.push(d.clone());
                for f in fns {
                    if ret.fns.contains_key(f) {
                        continue;
                    }
                    return Err(NonExhaustive(inst_tm, i_def_loc));
                }
            }
            _ => return Err(ExpectedInterface(Term::Ref(ret.i.0.clone()), i_def_loc)),
        };

        for (i_fn, inst_fn) in &ret.fns {
            let i_fn_def = self.sigma.get(i_fn).unwrap();

            let i_loc = i_fn_def.loc;
            let inst_loc = self.sigma.get(inst_fn).unwrap().loc;

            let (i_fn_ty_p, i_fn_ty_b) = match i_fn_def.to_type() {
                Term::Pi { param, body, .. } => (param, body),
                _ => unreachable!(),
            };
            let i_fn_ty_applied = self
                .nf(i_loc)
                .with([(&i_fn_ty_p.var, &inst_tm)], *i_fn_ty_b)?;
            let inst_fn_ty = self.infer(Resolved(inst_loc, inst_fn.clone()))?.ty;

            self.unifier(inst_loc)
                .unify(&i_fn_ty_applied, &inst_fn_ty)?;
        }

        Ok(ret)
    }

    fn check_anno(
        &mut self,
        a: Expr,
        eff: &Term,
        maybe_typ: Option<Box<Expr>>,
    ) -> Result<InferResult, Error> {
        if let Some(t) = maybe_typ {
            let ty = self.check(*t, &Term::Pure, &Term::Univ)?;
            Ok(InferResult {
                tm: self.check(a, eff, &ty)?,
                eff: eff.clone(),
                ty,
            })
        } else {
            self.infer(a)
        }
    }

    fn check(&mut self, e: Expr, eff: &Term, ty: &Term) -> Result<Term, Error> {
        maybe_grow(move || {
            self.check_impl(e, eff, ty).inspect(|tm| {
                debug!(target: "elab", "expression checked successfully: tm={tm}, eff={eff}, ty={ty}");
            })
        })
    }

    fn check_impl(&mut self, e: Expr, eff: &Term, ty: &Term) -> Result<Term, Error> {
        use Expr::*;
        trace!(target: "elab", "checking expression: e={e}, ty={ty}");
        Ok(match e {
            Const(_, var, maybe_typ, a, b) => {
                let a_loc = a.loc();
                let InferResult {
                    tm: a_tm,
                    eff: a_eff,
                    ty: a_ty,
                } = self.check_anno(*a, eff, maybe_typ)?;

                self.unifier(a_loc).unify(eff, &a_eff)?;

                let param = Param {
                    var,
                    info: Explicit,
                    typ: Box::new(a_ty),
                };
                let body = self.guarded_check([&param], *b, eff, ty)?;
                Term::Const(param, Box::new(a_tm), Box::new(body))
            }
            Let(_, var, maybe_typ, a, b) => {
                let a_loc = a.loc();
                let InferResult {
                    tm: a_tm,
                    eff: a_eff,
                    ty: a_ty,
                } = self.check_anno(*a, eff, maybe_typ)?;

                self.unifier(a_loc).unify(eff, &a_eff)?;

                let param = Param {
                    var,
                    info: Explicit,
                    typ: Box::new(a_ty),
                };
                let body = self.guarded_check([&param], *b, eff, ty)?;
                Term::Let(param, Box::new(a_tm), Box::new(body))
            }
            Update(_, v, a, b) => {
                let a_ty = self.gamma.get(&v).unwrap().clone();
                let a = self.check(*a, eff, &a_ty)?;
                let b = self.check(*b, eff, ty)?;
                Term::Update(v, Box::new(a), Box::new(b))
            }
            While(_, p, b, r) => {
                let p = self.check(*p, eff, &Term::Boolean)?;
                let b = self.check(*b, eff, &Term::Unit)?;
                let r = self.check(*r, eff, ty)?;
                Term::While(Box::new(p), Box::new(b), Box::new(r))
            }
            Fori(_, b, r) => {
                let b = self.check(*b, eff, &Term::Unit)?;
                let r = self.check(*r, eff, ty)?;
                Term::Fori(Box::new(b), Box::new(r))
            }
            Guard(_, p, b, e, r) => {
                let p = self.check(*p, eff, &Term::Boolean)?;
                let b = self.check(*b, eff, &Term::Unit)?;
                let e = if let Some(e) = e {
                    Some(Box::new(self.check(*e, eff, &Term::Unit)?))
                } else {
                    None
                };
                let r = self.check(*r, eff, ty)?;
                Term::Guard(Box::new(p), Box::new(b), e, Box::new(r))
            }
            Lam(loc, var, body) => match self.nf(loc).term(ty.clone())? {
                Term::Pi {
                    param: ty_param,
                    eff: ty_eff,
                    body: ty_body,
                } => {
                    self.unifier(loc).unify(eff, &ty_eff)?;

                    let p = Param {
                        var: var.clone(),
                        info: Explicit,
                        typ: ty_param.typ.clone(),
                    };
                    let b_ty = self
                        .nf(loc)
                        .with([(&ty_param.var, &Term::Ref(var))], *ty_body)?;
                    let b = self.guarded_check([&p], *body, eff, &b_ty)?;
                    Term::Lam(p, Box::new(b))
                }
                ty => return Err(ExpectedPi(ty, loc)),
            },
            Tuple(loc, a, b) => match self.nf(loc).term(ty.clone())? {
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
                        Term::Tuple(Box::new(self.check(args, eff, t)?), Box::new(Term::TT))
                    }
                    _ => {
                        let a = self.check(*a, eff, &p.typ)?;
                        let body = self.nf(loc).with([(&p.var, &a)], *body)?;
                        Term::Tuple(Box::new(a), Box::new(self.check(*b, eff, &body)?))
                    }
                },
                Term::AnonVarargs(ty) => {
                    let ret = self.infer(Tuple(loc, a, b))?;
                    self.unifier(loc).unify(eff, &ret.eff)?;
                    self.unifier(loc).unify(&ty, &ret.ty)?;
                    ret.tm
                }
                ty => return Err(ExpectedSigma(ty, loc)),
            },
            TupleBind(_, x, y, a, b) => {
                let a_loc = a.loc();
                let InferResult {
                    tm: a,
                    eff: a_eff,
                    ty: a_ty,
                } = self.infer(*a)?;

                self.unifier(a_loc).unify(eff, &a_eff)?;

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
                        let b = self.guarded_check([&x, &y], *b, eff, ty)?;
                        Term::TupleBind(x, y, Box::new(a), Box::new(b))
                    }
                    ty => return Err(ExpectedSigma(ty, a_loc)),
                }
            }
            UnitBind(_, a, b) => Term::UnitBind(
                Box::new(self.check(*a, eff, &Term::Unit)?),
                Box::new(self.check(*b, eff, ty)?),
            ),
            If(_, p, t, e) => Term::If(
                Box::new(self.check(*p, eff, &Term::Boolean)?),
                Box::new(self.check(*t, eff, ty)?),
                Box::new(self.check(*e, eff, ty)?),
            ),
            Downcast(loc, a) => {
                let InferResult {
                    tm: a,
                    eff: a_eff,
                    ty: a_ty,
                } = self.infer(*a)?;

                self.unifier(loc).unify(eff, &a_eff)?;

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
                let InferResult {
                    tm: a,
                    eff: a_eff,
                    ty: a_ty,
                } = self.infer(*a)?;

                self.unifier(loc).unify(eff, &a_eff)?;

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

                let InferResult {
                    tm: mut inferred_tm,
                    eff: inferred_eff,
                    ty: inferred_ty,
                } = self.infer(e)?;
                let mut inferred_eff = self.nf(loc).term(inferred_eff)?;
                let mut inferred = self.nf(loc).term(inferred_ty)?;
                let expected = self.nf(loc).term(ty.clone())?;

                if Self::is_hole_insertable(&expected) {
                    if let Some(f_e) = Self::app_insert_holes(f_e, UnnamedExplicit, &inferred)? {
                        let InferResult {
                            tm: new_tm,
                            eff: new_eff,
                            ty: new_ty,
                        } = self.infer(f_e)?;
                        inferred_tm = new_tm;
                        inferred_eff = new_eff;
                        inferred = new_ty;
                    }
                }

                self.unifier(loc).unify(eff, &inferred_eff)?;
                self.unifier(loc).unify(&expected, &inferred)?;

                inferred_tm
            }
        })
    }

    fn infer(&mut self, e: Expr) -> Result<InferResult, Error> {
        maybe_grow(move || {
            self.infer_impl(e).map(|InferResult { tm, eff, ty }| {
                debug!(target: "elab", "expression inferred successfully: tm={tm}, eff={eff}, ty={ty}");
                let (tm,ty)=Term::unwrap_solved_implicit_lambda(tm, ty);
                InferResult{ tm, eff, ty }
            })
        })
    }

    fn infer_impl(&mut self, e: Expr) -> Result<InferResult, Error> {
        use Expr::*;
        use MetaKind::*;
        trace!(target: "elab", "inferring expression: e={e}");
        Ok(match e {
            Resolved(loc, v) => {
                let local = self.gamma.get(&v);
                if local.is_none() {
                    let d = self.sigma.get(&v).unwrap();
                    let mut tm = d.to_term(v);
                    let eff = d.to_eff();
                    let mut ty = d.to_type();
                    if matches!(d.body, Body::Associated(..)) {
                        (tm, ty) = self.try_sugar_type_args(loc, tm, ty)?;
                    }
                    return Ok(InferResult { tm, eff, ty });
                }
                let ty = *local.unwrap().clone();
                return Ok(InferResult {
                    tm: Term::Ref(v),
                    eff: self.insert_meta(loc, InsertedMeta).0,
                    ty,
                });
            }
            Imported(_, v) => {
                let d = self.sigma.get(&v).unwrap();
                let tm = Term::Ref(v);
                let eff = d.to_eff();
                let ty = d.to_type();
                InferResult { tm, eff, ty }
            }
            Qualified(_, m, v) => {
                let d = self.sigma.get(&v).unwrap();
                let tm = Term::Qualified(m, v);
                let eff = d.to_eff();
                let ty = d.to_type();
                InferResult { tm, eff, ty }
            }
            Hole(loc) => {
                let (tm, ty) = self.insert_meta(loc, UserMeta);
                InferResult::pure(tm, ty)
            }
            InsertedHole(loc) => {
                let (tm, ty) = self.insert_meta(loc, InsertedMeta);
                InferResult::pure(tm, ty)
            }
            Return(_, a) => {
                let a = self.check(
                    *a,
                    &self.checking_eff.clone().unwrap(),
                    &self.checking_ret.clone().unwrap(),
                )?;
                InferResult::pure(Term::Return(Box::new(a)), Term::Unit)
            }
            Continue(_) => InferResult::pure(Term::Continue, Term::Unit),
            Break(_) => InferResult::pure(Term::Break, Term::Unit),
            Pi(loc, p, b) => {
                let param_ty = self.infer(*p.typ)?.tm;
                let param = Param {
                    var: p.var,
                    info: p.info,
                    typ: Box::new(param_ty),
                };
                let InferResult {
                    tm: b, ty: b_ty, ..
                } = self.guarded_infer([&param], *b)?;
                let eff = self.insert_meta(loc, InsertedMeta).0;
                InferResult {
                    tm: Term::Pi {
                        param,
                        eff: Box::new(eff.clone()),
                        body: Box::new(b),
                    },
                    eff,
                    ty: b_ty,
                }
            }
            Lam(loc, var, b) => {
                let mut typ = Box::new(Term::Unit);

                // Our lambda parameters are mostly tupled, hence we could cheat here by forming the tupled parameters
                // and inserting metas, and unification won't get stuck.
                let mut body = b.as_ref();
                while let TupleBind(_, x, y, _, b) = body {
                    let rhs = y.as_str();
                    if !rhs.starts_with(UNTUPLED_RHS_PREFIX) {
                        break;
                    }

                    typ = Box::new(Term::Sigma(
                        Param {
                            var: x.clone(),
                            info: Explicit,
                            typ: Box::new(self.insert_meta(loc, InsertedMeta).0),
                        },
                        typ,
                    ));
                    body = b.as_ref();

                    // Do not count in the multi-binders `const (a, b, c) = expr` here.
                    if rhs == UNTUPLED_ENDS {
                        break;
                    }
                }

                let param = Param {
                    var,
                    info: Explicit,
                    typ,
                };
                let InferResult {
                    tm: b, ty: b_ty, ..
                } = self.guarded_infer([&param], *b)?;
                let eff = self.insert_meta(loc, InsertedMeta).0;
                InferResult {
                    tm: Term::Lam(param.clone(), Box::new(b)),
                    eff: eff.clone(),
                    ty: Term::Pi {
                        param,
                        eff: Box::new(eff),
                        body: Box::new(b_ty),
                    },
                }
            }
            App(_, f, ai, x) => {
                let f_loc = f.loc();
                let f_e = f.clone();
                let InferResult {
                    tm: f, ty: f_ty, ..
                } = self.infer(*f)?;

                if let Some(f_e) = Self::app_insert_holes(*f_e, ai.clone(), &f_ty)? {
                    return self.infer(App(f_loc, Box::new(f_e), ai, x));
                }

                match f_ty {
                    Term::Pi {
                        param: p,
                        eff: b_eff,
                        body: b,
                    } => {
                        let x = self.guarded_check(
                            [&Param {
                                var: p.var.clone(),
                                info: p.info,
                                typ: p.typ.clone(),
                            }],
                            *x,
                            &b_eff,
                            &p.typ,
                        )?;
                        let applied_eff = self.nf(f_loc).with([(&p.var, &x)], *b_eff)?;
                        let applied_ty = self.nf(f_loc).with([(&p.var, &x)], *b)?;
                        let applied = self.nf(f_loc).apply(f, p.info.into(), &[x])?;
                        InferResult {
                            tm: applied,
                            eff: applied_eff,
                            ty: applied_ty,
                        }
                    }
                    ty => return Err(ExpectedPi(ty, f_loc)),
                }
            }
            RevApp(loc, f, type_args, x) => {
                if let Term::Sigma(p, _) = self.infer(*x.clone())?.ty {
                    if let Some(PartialClass { methods, .. }) = p.typ.class_methods(&self.sigma) {
                        let (f_loc, f_var, globally_found) = match *f {
                            Resolved(f_loc, v) => (f_loc, v, true),
                            Unresolved(f_loc, _, v) => (f_loc, v, false),
                            _ => unreachable!(),
                        };

                        let mut f = match methods.get(f_var.as_str()) {
                            Some(v) => Resolved(f_loc, v.clone()),
                            None if globally_found => Resolved(f_loc, f_var),
                            _ => return Err(UnresolvedVar(f_loc)),
                        };

                        f = type_args.into_iter().fold(f, |e, ty| {
                            App(loc, Box::new(e), UnnamedImplicit, Box::new(ty))
                        });

                        return self.infer(App(loc, Box::new(f), UnnamedExplicit, x));
                    }
                }
                if let Unresolved(f_loc, ..) = *f {
                    return Err(UnresolvedVar(f_loc));
                }
                self.infer(App(loc, f, UnnamedExplicit, x))?
            }
            Sigma(_, p, b) => {
                let param_ty = self.infer(*p.typ)?.tm;
                let param = Param {
                    var: p.var,
                    info: p.info,
                    typ: Box::new(param_ty),
                };
                let InferResult {
                    tm: b,
                    eff,
                    ty: b_ty,
                } = self.guarded_infer([&param], *b)?;
                InferResult {
                    tm: Term::Sigma(param, Box::new(b)),
                    eff,
                    ty: b_ty,
                }
            }
            Tuple(loc, a, b) => {
                let InferResult {
                    tm: a,
                    eff: a_eff,
                    ty: a_ty,
                } = self.infer(*a)?;
                let InferResult {
                    tm: b,
                    eff: b_eff,
                    ty: b_ty,
                } = self.infer(*b)?;

                self.unifier(loc).unify(&a_eff, &b_eff)?;

                InferResult {
                    tm: Term::Tuple(Box::new(a), Box::new(b)),
                    eff: a_eff,
                    ty: Term::Sigma(
                        Param {
                            var: Var::unbound(),
                            info: Explicit,
                            typ: Box::new(a_ty),
                        },
                        Box::new(b_ty),
                    ),
                }
            }
            TupleBind(_, x, y, a, b) => {
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

                let InferResult {
                    tm: b,
                    eff,
                    ty: b_ty,
                } = self.guarded_infer([&x, &y], *b)?;
                let a = self.check(*a, &eff, &Term::Sigma(x.clone(), Box::new(y_ty)))?;

                InferResult {
                    tm: Term::TupleBind(x, y, Box::new(a), Box::new(b)),
                    eff,
                    ty: b_ty,
                }
            }
            UnitBind(_, a, b) => {
                let InferResult { tm: b, eff, ty } = self.infer(*b)?;
                let a = self.check(*a, &eff, &Term::Unit)?;
                InferResult {
                    tm: Term::UnitBind(Box::new(a), Box::new(b)),
                    eff,
                    ty,
                }
            }
            Arr(loc, xs) => {
                let mut v_ty = None;
                let mut v_eff = None;
                let mut checked = Vec::default();
                for (i, x) in xs.into_iter().enumerate() {
                    if i > 0 {
                        checked.push(self.check(
                            x,
                            v_eff.as_ref().unwrap(),
                            v_ty.as_ref().unwrap(),
                        )?);
                        continue;
                    }
                    let InferResult {
                        tm: x_tm,
                        eff,
                        ty: x_ty,
                    } = self.infer(x)?;
                    v_ty = Some(x_ty);
                    v_eff = Some(eff);
                    checked.push(x_tm);
                }
                if checked.is_empty() {
                    InferResult {
                        tm: Term::Arr(Default::default()),
                        eff: self.insert_meta(loc, InsertedMeta).0,
                        ty: self.insert_meta(loc, InsertedMeta).0,
                    }
                } else {
                    InferResult {
                        tm: Term::Arr(checked),
                        eff: v_eff.unwrap(),
                        ty: Term::Array(Box::new(v_ty.unwrap())),
                    }
                }
            }
            Kv(loc, xs) => {
                let mut k_ty = None;
                let mut v_ty = None;
                let mut k_eff = None;
                let mut checked = Vec::default();
                for (i, (k, v)) in xs.into_iter().enumerate() {
                    if i > 0 {
                        checked.push((
                            self.check(k, k_eff.as_ref().unwrap(), k_ty.as_ref().unwrap())?,
                            self.check(v, k_eff.as_ref().unwrap(), v_ty.as_ref().unwrap())?,
                        ));
                        continue;
                    }

                    let InferResult {
                        tm: key,
                        eff: key_eff,
                        ty: key_ty,
                    } = self.infer(k)?;
                    let InferResult {
                        tm: val,
                        eff: val_eff,
                        ty: val_ty,
                    } = self.infer(v)?;

                    if i == 0 {
                        self.unifier(loc).unify(&key_eff, &val_eff)?;
                    }

                    k_ty = Some(key_ty);
                    v_ty = Some(val_ty);
                    k_eff = Some(key_eff);
                    checked.push((key, val));
                }
                if checked.is_empty() {
                    InferResult {
                        tm: Term::Kv(Default::default()),
                        eff: self.insert_meta(loc, InsertedMeta).0,
                        ty: self.insert_meta(loc, InsertedMeta).0,
                    }
                } else {
                    InferResult {
                        tm: Term::Kv(checked),
                        eff: k_eff.unwrap(),
                        ty: Term::Map(Box::new(k_ty.unwrap()), Box::new(v_ty.unwrap())),
                    }
                }
            }
            Associate(loc, a, n) => InferResult::pure(
                Term::Associate(Box::new(self.check(*a, &Term::Pure, &Term::Univ)?), n),
                self.insert_meta(loc, InsertedMeta).0,
            ),
            Fields(_, fields) => {
                let mut inferred = FieldMap::default();
                for (f, e) in fields {
                    inferred.insert(f, self.infer(e)?.tm);
                }
                InferResult::pure(Term::Fields(inferred), Term::Row)
            }
            Combine(_, a, b) => {
                let a = self.check(*a, &Term::Pure, &Term::Row)?;
                let b = self.check(*b, &Term::Pure, &Term::Row)?;
                InferResult::pure(Term::Combine(false, Box::new(a), Box::new(b)), Term::Row)
            }
            RowOrd(_, a, b) => {
                let a = self.check(*a, &Term::Pure, &Term::Row)?;
                let b = self.check(*b, &Term::Pure, &Term::Row)?;
                InferResult::pure(Term::RowOrd(Box::new(a), Box::new(b)), Term::Univ)
            }
            RowEq(_, a, b) => {
                let a = self.check(*a, &Term::Pure, &Term::Row)?;
                let b = self.check(*b, &Term::Pure, &Term::Row)?;
                InferResult::pure(Term::RowEq(Box::new(a), Box::new(b)), Term::Univ)
            }
            Object(_, r) => {
                let r = self.check(*r, &Term::Pure, &Term::Row)?;
                InferResult::pure(Term::Object(Box::new(r)), Term::Univ)
            }
            Obj(_, r) => match *r {
                Fields(loc, fields) => {
                    let mut tm_fields = FieldMap::default();
                    let mut ty_fields = FieldMap::default();
                    let mut o_eff = None;
                    for (n, e) in fields {
                        let InferResult { tm, eff, ty } = self.infer(e)?;
                        if o_eff.is_none() {
                            o_eff = Some(eff);
                        } else {
                            self.unifier(loc).unify(o_eff.as_ref().unwrap(), &eff)?;
                        }
                        tm_fields.insert(n.clone(), tm);
                        ty_fields.insert(n, ty);
                    }
                    InferResult {
                        tm: Term::Obj(Box::new(Term::Fields(tm_fields))),
                        eff: o_eff.unwrap(),
                        ty: Term::Object(Box::new(Term::Fields(ty_fields))),
                    }
                }
                _ => unreachable!(),
            },
            Concat(loc, a, b) => {
                let x_loc = a.loc();
                let y_loc = b.loc();

                let InferResult {
                    tm: x,
                    eff: x_eff,
                    ty: x_ty,
                } = self.infer(*a)?;
                let InferResult {
                    tm: y,
                    eff: y_eff,
                    ty: y_ty,
                } = self.infer(*b)?;

                self.unifier(loc).unify(&x_eff, &y_eff)?;

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
                InferResult {
                    tm: Term::Concat(Box::new(x), Box::new(y)),
                    eff: x_eff,
                    ty,
                }
            }
            Access(_, n) => {
                let t = Var::new("T");
                let a = Var::new("'A");
                let e = Var::new("^E");
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
                        var: e.clone(),
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
                InferResult::pure(
                    *rename(Box::new(Term::lam(
                        &tele,
                        Term::Access(Box::new(Term::Ref(o)), n),
                    ))),
                    *rename(Box::new(Term::pi(&tele, Term::Pure, Term::Ref(t)))),
                )
            }
            Downcast(loc, a) => {
                let InferResult { tm: a, eff, ty } = self.infer(*a)?;
                let m = self.insert_meta(loc, InsertedMeta).0;
                match ty {
                    Term::Object(r) => InferResult {
                        tm: Term::Down(Box::new(a), Box::new(m.clone())),
                        eff,
                        ty: Term::Downcast(Box::new(Term::Object(r)), Box::new(m)),
                    },
                    ty => return Err(ExpectedObject(ty, loc)),
                }
            }
            Enum(_, r) => InferResult::pure(
                Term::Enum(Box::new(self.check(*r, &Term::Pure, &Term::Row)?)),
                Term::Univ,
            ),
            Variant(_, n, a) => {
                let InferResult {
                    tm: a,
                    eff,
                    ty: a_ty,
                } = self.infer(*a)?;
                let tm = Term::Fields(FieldMap::from([(n.clone(), a)]));
                let ty = Term::Fields(FieldMap::from([(n, a_ty)]));
                InferResult {
                    tm: Term::Variant(Box::new(tm)),
                    eff,
                    ty: Term::Upcast(Box::new(Term::Enum(Box::new(ty)))),
                }
            }
            Upcast(loc, a) => {
                let InferResult { tm: a, eff, ty } = self.infer(*a)?;
                match ty {
                    Term::Enum(r) => InferResult {
                        tm: a,
                        eff,
                        ty: Term::Upcast(Box::new(Term::Enum(r))),
                    },
                    Term::Upcast(r) => InferResult {
                        tm: a,
                        eff,
                        ty: Term::Upcast(r),
                    },
                    ty => return Err(ExpectedEnum(ty, loc)),
                }
            }
            Switch(loc, a, cs, d) => {
                let mut ret_ty = None;
                let a_loc = a.loc();
                let InferResult {
                    tm: a,
                    eff: a_eff,
                    ty: a_ty,
                } = self.infer(*a)?;
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
                            let InferResult { tm, eff, ty } = self.guarded_infer([&pat], e)?;
                            self.unifier(loc).unify(&a_eff, &eff)?;
                            ret_ty = Some(ty);
                            tm
                        }
                        Some(ret) => self.guarded_check([&pat], e, &a_eff, ret)?,
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
                            Box::new(self.guarded_check(
                                [&p],
                                *e,
                                &a_eff,
                                ret_ty.as_ref().unwrap(),
                            )?),
                        ))
                    }
                    None => None,
                };
                InferResult {
                    tm: Term::Switch(Box::new(a), m, d),
                    eff: a_eff,
                    ty: ret_ty.unwrap(),
                }
            }
            Instanceof(loc, a) => {
                let InferResult { tm, eff, ty } = self.infer(*a)?;
                match tm {
                    Term::Instanceof(a, i) => InferResult {
                        tm: Term::Instanceof(a, i),
                        eff,
                        ty,
                    },
                    tm => return Err(ExpectedInstanceof(tm, loc)),
                }
            }
            Varargs(loc, t) => {
                let t = self.check(*t, &Term::Pure, &Term::Univ)?;
                if !self.is_variadic(&t) {
                    return Err(NonVariadicType(t, loc));
                }
                InferResult::pure(Term::Varargs(Box::new(t)), Term::Univ)
            }
            AnonVarargs(_, t) => InferResult::pure(
                Term::AnonVarargs(Box::new(self.check(*t, &Term::Pure, &Term::Univ)?)),
                Term::Univ,
            ),
            Spread(loc, a) => {
                let InferResult { tm: a, eff, ty } = self.infer(*a)?;
                if !self.is_variadic(&ty) {
                    return Err(NonVariadicType(ty, loc));
                }
                InferResult {
                    tm: Term::Spread(Box::new(a)),
                    eff,
                    ty,
                }
            }
            Pure(_) => InferResult::pure(Term::Pure, Term::Row),
            Effect(_, a) => InferResult::pure(
                Term::Effect(FieldSet::from_iter(a.into_iter().map(Expr::resolved))),
                Term::Row,
            ),
            EmitAsync(_, a) => {
                let InferResult { tm, ty, .. } = self.infer(*a)?;
                InferResult {
                    tm: Term::EmitAsync(Box::new(tm)),
                    eff: Term::async_effect(self.ubiquitous.get(ASYNC).unwrap().1.clone()),
                    ty,
                }
            }

            Univ(_) => InferResult::pure(Term::Univ, Term::Univ),
            Unit(_) => InferResult::pure(Term::Unit, Term::Univ),
            TT(_) => InferResult::pure(Term::TT, Term::Unit),
            Boolean(_) => InferResult::pure(Term::Boolean, Term::Univ),
            False(_) => InferResult::pure(Term::False, Term::Boolean),
            True(_) => InferResult::pure(Term::True, Term::Boolean),
            String(_) => InferResult::pure(Term::String, Term::Univ),
            Str(_, v) => InferResult::pure(Term::Str(v), Term::String),
            Number(_) => InferResult::pure(Term::Number, Term::Univ),
            Num(_, r) => InferResult::pure(Term::Num(r.parse().unwrap()), Term::Number),
            BigInt(_) => InferResult::pure(Term::BigInt, Term::Univ),
            Big(_, v) => InferResult::pure(Term::Big(v), Term::BigInt),
            Row(_) => InferResult::pure(Term::Row, Term::Univ),

            _ => unreachable!(),
        })
    }

    fn guarded_check<const N: usize>(
        &mut self,
        ps: [&Param<Term>; N],
        e: Expr,
        eff: &Term,
        ty: &Term,
    ) -> Result<Term, Error> {
        for p in ps {
            self.gamma.insert(p.var.clone(), p.typ.clone());
        }
        let ret = self.check(e, eff, ty)?;
        for p in ps {
            self.gamma.remove(&p.var);
        }
        Ok(ret)
    }

    fn guarded_infer<const N: usize>(
        &mut self,
        ps: [&Param<Term>; N],
        e: Expr,
    ) -> Result<InferResult, Error> {
        for p in ps {
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
                eff: Box::new(Term::Pure),
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
                eff: Box::new(Term::Pure),
                ret: Box::new(ty.clone()),
                body: Meta(k.clone(), None),
            },
        );
        (Term::MetaRef(k, tm_meta_var, spine), ty)
    }

    fn is_hole_insertable(expected: &Term) -> bool {
        match expected {
            Term::Pi { param, .. } => param.info != Implicit,
            _ => true,
        }
    }

    fn app_insert_holes(f_e: Expr, i: ArgInfo, f_ty: &Term) -> Result<Option<Expr>, Error> {
        fn holes_to_insert(loc: Loc, name: String, mut ty: &Term) -> Result<usize, Error> {
            let mut ret = Default::default();
            loop {
                match ty {
                    Term::Pi {
                        param: p, body: b, ..
                    } => {
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
            Term::Pi { param, .. } if param.info == Implicit => match i {
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

    fn verify(
        &mut self,
        loc: Loc,
        target: Expr,
        expected_eff: Term,
        expected_ty: Term,
    ) -> Result<Term, Error> {
        let InferResult { tm, eff, ty } = self.infer(target)?;
        #[cfg(not(test))]
        {
            let _ = loc;
            let _ = expected_eff;
            let _ = expected_ty;
            let _ = eff;
            let _ = ty;
        }
        #[cfg(test)]
        {
            let actual_eff = self.nf(loc).term(eff)?;
            let expected_eff = self.nf(loc).term(expected_eff)?;
            self.unifier(loc).unify(&expected_eff, &actual_eff)?;

            let actual_ty = self.nf(loc).term(ty)?;
            let expected_ty = self.nf(loc).term(expected_ty)?;
            self.unifier(loc).unify(&expected_ty, &actual_ty)?;
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
            checking_eff: Default::default(),
            checking_ret: Default::default(),
            checking_class_type_args: Default::default(),
        }
    }
}

struct InferResult {
    tm: Term,
    eff: Term,
    ty: Term,
}

impl InferResult {
    fn pure(tm: Term, ty: Term) -> Self {
        Self {
            tm,
            eff: Term::Pure,
            ty,
        }
    }
}
