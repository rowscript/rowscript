use std::collections::HashMap;

use log::{debug, info, trace};

use crate::theory::abs::builtin::Builtins;
use crate::theory::abs::data::{CaseMap, FieldMap, FieldSet, MetaKind, PartialClass, Term};
use crate::theory::abs::def::{gamma_to_tele, tele_to_refs, Body, ClassMembers, InstanceBody};
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
use crate::Error::{
    CatchAsyncEffect, DuplicateEffect, ExpectedCapability, ExpectedEnum, ExpectedInstanceof,
    ExpectedInterface, ExpectedObject, ExpectedPi, ExpectedSigma, NonCatchableExpr, NonExhaustive,
    NonVariadicType, NotCheckedYet, UnresolvedEffect, UnresolvedField, UnresolvedImplicitParam,
    UnresolvedVar,
};
use crate::{maybe_grow, File};
use crate::{print_err, Error};

#[derive(Debug)]
pub struct Elaborator {
    pub ubiquitous: NameMap,
    pub sigma: Sigma,
    gamma: Gamma,

    vg: VarGen,

    checking_eff: Option<Term>,
    checking_ret: Option<Term>,
    checking_class_type_args: Option<Box<[Term]>>,

    delayed: HashMap<Var, (Loc, Var, Body<Expr>)>,
}

impl Elaborator {
    pub fn files(&mut self, files: Vec<File<Expr>>) -> Result<Vec<File<Term>>, Error> {
        files
            .into_iter()
            .map(|f| {
                let p = f.path.clone();
                self.file(f).map_err(|e| print_err(e, &p))
            })
            .collect()
    }

    fn file(&mut self, file: File<Expr>) -> Result<File<Term>, Error> {
        let File {
            path,
            imports,
            defs,
        } = file;

        let defs = defs
            .into_iter()
            .map(|d| {
                let def = self.def(d)?;
                if let Some((.., v, body)) = self.delayed.remove(&def.name) {
                    self.fn_body(v, body)?;
                }
                Ok::<_, Error>(def)
            })
            .collect::<Result<_, _>>()?;

        if let Some((v, (loc, ..))) = self.delayed.iter().next() {
            return Err(NotCheckedYet(v.clone(), *loc));
        }

        Ok(File {
            path,
            imports,
            defs,
        })
    }

    fn def(&mut self, d: Def<Expr>) -> Result<Def<Term>, Error> {
        use Body::*;

        info!(target: "elab", "checking definition: {}", d.name);

        let Def {
            loc,
            name,
            tele,
            eff,
            ret,
            body,
        } = d;

        // Help to sugar the associated type argument insertion, see `self.try_sugar_type_args`.
        if let Method { class, .. } = &body {
            self.checking_class_type_args =
                Some(tele_to_refs(&self.sigma.get(class).unwrap().tele));
        }

        let tele = self.params(tele)?;

        // Help to sugar the associated type argument insertion, see `self.try_sugar_type_args`.
        if matches!(body, Class { .. }) {
            self.checking_class_type_args = Some(tele_to_refs(&tele));
        }

        let mut eff = Box::new(self.check(*eff, &Term::Pure, &Term::Row)?);
        let mut ret = Box::new(self.check(*ret, &Term::Pure, &Term::Univ)?);
        self.checking_eff = Some(*eff.clone());
        self.checking_ret = Some(*ret.clone());
        let mut inferred_eff = None;
        let mut inferred_ret = None;

        if matches!(body, Fn(..) | Alias { .. }) {
            // Self-referencing definitions.
            self.sigma.insert(
                name.clone(),
                Def {
                    loc,
                    name: name.clone(),
                    tele: tele.clone(),
                    eff: eff.clone(),
                    ret: ret.clone(),
                    body: Undefined,
                },
            );
        }

        let body = match body {
            Fn(f) => {
                let f_copied = f.clone();
                let b = self.check(*f, &eff, &ret);
                match b {
                    Ok(f) => Fn(Box::new(f)),
                    Err(e) => match e {
                        NotCheckedYet(yet, loc) => {
                            self.delayed.insert(yet, (loc, name.clone(), Fn(f_copied)));
                            Undefined
                        }
                        e => return Err(e),
                    },
                }
            }
            Postulate => Postulate,
            Alias { ty, implements } => {
                let ty = self.check(*ty, &eff, &ret)?;
                Alias {
                    ty: Box::new(ty.clone()),
                    implements: implements
                        .map(|i| self.insert_implements(*i, name.clone(), ty))
                        .transpose()?,
                }
            }
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
            Verify(a) => Verify(Box::new(self.verify(
                d.loc,
                *a,
                *eff.clone(),
                *rename(Box::new(Term::pi(&tele, *eff.clone(), *ret.clone()))),
            )?)),
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
            Instance(body) => Instance(self.check_instance_body(&name, *body, false)?),
            InstanceFn(f) => InstanceFn(Box::new(self.check(*f, &eff, &ret)?)),
            ImplementsFn { name, f } => ImplementsFn {
                name,
                f: Box::new(self.check(*f, &eff, &ret)?),
            },
            Class {
                ctor,
                associated,
                members,
                methods,
            } => {
                let members = match members {
                    ClassMembers::Wrapper(ty) => ClassMembers::Wrapper(Box::new(self.check(
                        *ty,
                        &Term::Pure,
                        &Term::Univ,
                    )?)),
                    ClassMembers::Members(m) => {
                        let mut checked_members = Vec::default();
                        for (loc, id, typ) in m {
                            checked_members.push((loc, id, self.check(typ, &eff, &ret)?));
                        }
                        ClassMembers::Members(checked_members)
                    }
                };
                Class {
                    ctor,
                    associated,
                    members,
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
            _ => unreachable!(),
        };

        if let Some(e) = inferred_eff {
            eff = e;
        }
        if let Some(r) = inferred_ret {
            ret = r;
        }
        let def = Def {
            loc,
            name,
            tele,
            eff,
            ret,
            body,
        };

        self.sigma.insert(def.name.clone(), def.clone());

        self.gamma.clear();
        self.checking_eff = None;
        self.checking_ret = None;
        self.checking_class_type_args = None;

        debug!(target: "elab", "definition checked successfully: {def}");
        Ok(def)
    }

    fn fn_body(&mut self, v: Var, b: Body<Expr>) -> Result<(), Error> {
        let Def { tele, eff, ret, .. } = self.sigma.get(&v).unwrap().clone();

        tele.into_iter().for_each(|p| {
            self.gamma.insert(p.var, p.typ);
        });

        self.checking_eff = Some(*eff.clone());
        self.checking_ret = Some(*ret.clone());

        let r = match b.clone() {
            Body::Fn(f) => self.check(*f, &eff, &ret),
            _ => unreachable!(),
        };
        match r {
            Ok(f) => {
                self.sigma.get_mut(&v).unwrap().body = Body::Fn(Box::new(f));
            }
            Err(e) => match e {
                NotCheckedYet(yet, loc) => {
                    self.delayed.insert(yet, (loc, v, b));
                }
                e => return Err(e),
            },
        };

        self.gamma.clear();
        self.checking_eff = None;
        self.checking_ret = None;

        Ok(())
    }

    fn instance_fn_def(&mut self, d: Def<Expr>) -> Result<Def<Term>, Error> {
        let mut checked = Vec::default();
        let mut tele = Tele::default();
        for p in &d.tele {
            let typ = self.check(*p.typ.clone(), &Term::Pure, &Term::Univ)?;
            self.gamma.insert(p.var.clone(), Box::new(typ.clone()));
            checked.push(p.var.clone());
            tele.push(Param {
                var: p.var.clone(),
                info: p.info,
                typ: Box::new(typ),
            })
        }

        let eff = Box::new(self.check(*d.eff.clone(), &Term::Pure, &Term::Row)?);
        let ret = Box::new(self.check(*d.ret.clone(), &Term::Pure, &Term::Univ)?);

        let body = match d.body {
            Body::InstanceFn(f) => Body::InstanceFn(Box::new(self.check(*f, &eff, &ret)?)),
            _ => unreachable!(),
        };

        for v in checked {
            self.gamma.remove(&v);
        }

        Ok(Def {
            loc: d.loc,
            name: d.name.clone(),
            tele,
            eff,
            ret,
            body,
        })
    }

    fn params(&mut self, tele: Tele<Expr>) -> Result<Tele<Term>, Error> {
        tele.into_iter()
            .map(|Param { var, info, typ }| {
                let typ = Box::new(self.check(*typ, &Term::Pure, &Term::Univ)?);
                self.gamma.insert(var.clone(), typ.clone());
                Ok(Param { var, info, typ })
            })
            .collect()
    }

    fn unifier(&mut self, loc: Loc) -> Unifier {
        Unifier::new(&self.ubiquitous, &mut self.sigma, loc)
    }

    fn nf(&mut self, loc: Loc) -> Normalizer {
        Normalizer::new(&self.ubiquitous, &mut self.sigma, loc)
    }

    fn insert_implements(&mut self, i: Expr, name: Var, ty: Term) -> Result<Box<Term>, Error> {
        use Body::*;
        use Expr::*;

        let (loc, i) = match i {
            Resolved(loc, i) => (loc, i),
            _ => unreachable!(),
        };
        let inst = Resolved(loc, name.clone());
        let inst_tm = Box::new(Term::Ref(name));
        let implements = match &self.sigma.get(&i).unwrap().body {
            Interface { implements, .. } => implements.clone(),
            _ => unreachable!(),
        };

        let mut fns = HashMap::default();
        for f in implements {
            let mut d = self.sigma.get(&f).unwrap().clone();
            let ty_var = d.tele.remove(0).var;
            d.tele = d
                .tele
                .into_iter()
                .map(|p| {
                    Ok::<_, Error>(Param {
                        var: p.var,
                        info: p.info,
                        typ: Box::new(self.nf(d.loc).with([(&ty_var, &ty)], *p.typ)?),
                    })
                })
                .collect::<Result<Tele<_>, _>>()?;
            d.ret = Box::new(self.nf(d.loc).with([(&ty_var, &ty)], *d.ret)?);
            let (f_name, f) = match d.body {
                ImplementsFn { name, f } => (name, f),
                _ => unreachable!(),
            };
            d.body = InstanceFn(Box::new(self.nf(d.loc).with([(&ty_var, &ty)], *f)?));
            d.name = f_name.instance_fn(&i, &inst);

            fns.insert(f_name, d.name.clone());
            self.sigma.insert(d.name.clone(), d);
        }

        let inst_def = Def {
            loc,
            name: i.instance(&inst),
            tele: Default::default(),
            eff: Box::new(Term::Pure),
            ret: Box::new(Term::Univ),
            body: Instance(Box::new(InstanceBody {
                i: i.clone(),
                inst: inst_tm,
                fns,
            })),
        };
        match &mut self.sigma.get_mut(&i).unwrap().body {
            Interface { instances, .. } => instances.push(inst_def.name.clone()),
            _ => unreachable!(),
        };
        self.sigma.insert(inst_def.name.clone(), inst_def);

        Ok(Box::new(Term::Ref(i)))
    }

    fn check_instance_body(
        &mut self,
        d: &Var,
        body: InstanceBody<Expr>,
        can_be_capability: bool,
    ) -> Result<Box<InstanceBody<Term>>, Error> {
        use Body::*;
        use Expr::*;

        let ret = Box::new(InstanceBody {
            i: body.i,
            inst: Box::new(self.infer(*body.inst)?.tm),
            fns: body.fns,
        });
        let inst_tm = ret.instance_type(&self.sigma)?;

        let i_def = self.sigma.get_mut(&ret.i).unwrap();
        let i_def_loc = i_def.loc;
        match &mut i_def.body {
            Interface {
                is_capability,
                fns,
                instances,
                ..
            } => {
                if !can_be_capability && *is_capability {
                    return Err(ExpectedInterface(Term::Ref(ret.i.clone()), i_def_loc));
                }
                instances.push(d.clone());
                for f in fns {
                    if ret.fns.contains_key(f) {
                        continue;
                    }
                    return Err(NonExhaustive(inst_tm, i_def_loc));
                }
            }
            _ => return Err(ExpectedInterface(Term::Ref(ret.i.clone()), i_def_loc)),
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
                trace!(target: "elab", "expression checked successfully: tm={tm}, eff={eff}, ty={ty}");
            })
        })
    }

    fn check_impl(&mut self, e: Expr, eff: &Term, ty: &Term) -> Result<Term, Error> {
        use Expr::*;
        debug!(target: "elab", "checking expression: e={e}, ty={ty}");
        Ok(match e {
            Const(_, var, maybe_typ, a, b) => {
                let a_loc = a.loc();
                let InferResult {
                    tm: a_tm,
                    eff: a_eff,
                    ty: a_ty,
                } = self.check_anno(*a, eff, maybe_typ)?;

                self.unifier(a_loc).unify_eff(eff, &a_eff)?;

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

                self.unifier(a_loc).unify_eff(eff, &a_eff)?;

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
            Lam(loc, var, body) => match ty {
                Term::Pi {
                    param: ty_param,
                    eff: ty_eff,
                    body: ty_body,
                } => {
                    self.unifier(loc).unify_eff(eff, ty_eff)?;

                    let p = Param {
                        var: var.clone(),
                        info: Explicit,
                        typ: ty_param.typ.clone(),
                    };
                    let b_ty = self
                        .nf(loc)
                        .with([(&ty_param.var, &Term::Ref(var))], *ty_body.clone())?;
                    let b = self.guarded_check([&p], *body, eff, &b_ty)?;
                    Term::Lam(p, Box::new(b))
                }
                ty => return Err(ExpectedPi(ty.clone(), loc)),
            },
            Tuple(loc, a, b) => match ty {
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
                        let body = self.nf(loc).with([(&p.var, &a)], *body.clone())?;
                        Term::Tuple(Box::new(a), Box::new(self.check(*b, eff, &body)?))
                    }
                },
                Term::AnonVarargs(ty) => {
                    let ret = self.infer(Tuple(loc, a, b))?;
                    self.unifier(loc).unify_eff(eff, &ret.eff)?;
                    self.unifier(loc).unify(ty, &ret.ty)?;
                    ret.tm
                }
                ty => return Err(ExpectedSigma(ty.clone(), loc)),
            },
            TupleBind(_, x, y, a, b) => {
                let a_loc = a.loc();
                let InferResult {
                    tm: a,
                    eff: a_eff,
                    ty: a_ty,
                } = self.infer(*a)?;

                self.unifier(a_loc).unify_eff(eff, &a_eff)?;

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

                self.unifier(loc).unify_eff(eff, &a_eff)?;

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

                self.unifier(loc).unify_eff(eff, &a_eff)?;

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

                self.unifier(loc).unify_eff(eff, &inferred_eff)?;
                self.unifier(loc).unify(&expected, &inferred)?;

                inferred_tm
            }
        })
    }

    fn infer(&mut self, e: Expr) -> Result<InferResult, Error> {
        maybe_grow(move || {
            self.infer_impl(e).map(|InferResult { tm, eff, ty }| {
                let (tm, ty) = Term::unwrap_solved_implicit_lambda(tm, ty);
                trace!(target: "elab", "expression inferred successfully: tm={tm}, eff={eff}, ty={ty}");
                InferResult { tm, eff, ty }
            })
        })
    }

    fn infer_impl(&mut self, e: Expr) -> Result<InferResult, Error> {
        use Expr::*;
        use MetaKind::*;
        debug!(target: "elab", "inferring expression: e={e}");
        Ok(match e {
            Resolved(loc, v) => match self.gamma.get(&v) {
                Some(ty) => {
                    let ty = *ty.clone();
                    InferResult {
                        tm: Term::Ref(v),
                        eff: self.insert_meta(loc, InsertedMeta).0,
                        ty,
                    }
                }
                None => match self.sigma.get(&v) {
                    Some(d) => {
                        let mut tm = d.to_term(v);
                        let eff = d.to_eff();
                        let mut ty = d.to_type();
                        if matches!(d.body, Body::Associated(..)) {
                            (tm, ty) = self.try_sugar_type_args(loc, tm, ty)?;
                        }
                        InferResult { tm, eff, ty }
                    }
                    None => return Err(NotCheckedYet(v, loc)),
                },
            },
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

                match self.nf(f_loc).term(f_ty)? {
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
                            tm: Self::auto_unionify(applied, &p.typ),
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

                self.unifier(loc).unify_eff(&a_eff, &b_eff)?;

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
                        self.unifier(loc).unify_eff(&key_eff, &val_eff)?;
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
            At(_, a, k) => {
                let a_loc = a.loc();
                let k = self.check(*k, &Term::Pure, &Term::Rowkey)?;
                let InferResult { tm, eff, mut ty } = self.infer(*a)?;
                self.unifier(a_loc).unify_eff(&Term::Pure, &eff)?;
                ty = match ty {
                    Term::Downcast(ty, ..) | Term::Upcast(ty) => *ty,
                    ty => ty,
                };
                InferResult {
                    tm: Term::At(Box::new(tm), Box::new(k.clone())),
                    eff,
                    ty: Term::AtResult {
                        ty: Box::new(ty),
                        key: Box::new(k),
                    },
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
                            self.unifier(loc).unify_eff(o_eff.as_ref().unwrap(), &eff)?;
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
            Concat(_, a, b) => {
                let a = self.check(*a, &Term::Pure, &Term::Univ)?;
                let b = self.check(*b, &Term::Pure, &Term::Univ)?;
                match (a, b) {
                    (Term::Object(a), Term::Object(b)) => InferResult::pure(
                        Term::Object(Box::new(Term::Combine(false, a, b))),
                        Term::Univ,
                    ),
                    (a, b) => InferResult::pure(Term::Concat(Box::new(a), Box::new(b)), Term::Univ),
                }
            }
            Cat(loc, a, b) => {
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

                self.unifier(loc).unify_eff(&x_eff, &y_eff)?;

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
                    tm: Term::Cat(Box::new(x), Box::new(y)),
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
                let a_loc = a.loc();
                let InferResult {
                    tm: a,
                    eff: a_eff,
                    ty: a_ty,
                } = self.infer(*a)?;
                let en = self.nf(loc).with_expand_mu(a_ty)?;
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
                let mut ret_ty = None;
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
                            self.unifier(loc).unify_eff(&a_eff, &eff)?;
                            ret_ty = Some(ty);
                            tm
                        }
                        Some(ret) => match ret {
                            // If every branch's inferred type is upcast, we try to create a disjoint union of each.
                            Term::Upcast(a_ty) => {
                                let InferResult { tm, eff, ty } = self.guarded_infer([&pat], e)?;
                                match ty {
                                    Term::Upcast(b_ty) => {
                                        ret_ty = Some(self.nf(loc).term(Term::Upcast(Box::new(
                                            Term::Disjoint(a_ty.clone(), b_ty),
                                        )))?)
                                    }
                                    ty => {
                                        self.unifier(loc).unify_eff(&a_eff, &eff)?;
                                        self.unifier(loc).unify(ret, &ty)?;
                                    }
                                }
                                tm
                            }
                            ret => self.guarded_check([&pat], e, &a_eff, ret)?,
                        },
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
            Typeof(_, a) => {
                let InferResult { ty, .. } = self.infer(*a)?;
                let type_of = self.ubiquitous.get("Typeof").unwrap().1.clone();
                let type_of = self.sigma.get(&type_of).unwrap().to_term(type_of);
                InferResult::pure(Term::Typeof(Box::new(ty)), type_of)
            }
            Keyof(loc, a) => {
                let InferResult { tm, .. } = self.infer(*a)?;
                let list_ty = self.ubiquitous.get("List").unwrap().1.clone();
                let list_ty = self.sigma.get(&list_ty).unwrap().to_term(list_ty);
                let label_list_ty = self.nf(loc).term(Term::App(
                    Box::new(list_ty),
                    UnnamedImplicit,
                    Box::new(Term::Rowkey),
                ))?;
                InferResult::pure(Term::Keyof(Box::new(tm)), label_list_ty)
            }
            Pure(_) => InferResult::pure(Term::Pure, Term::Row),
            Effect(loc, a) => {
                let mut effs = FieldSet::new();
                for e in a {
                    let eff = e.resolved();
                    if effs.contains(&eff) {
                        return Err(DuplicateEffect(eff, loc));
                    }

                    // Check if it's async effect.
                    if let Some(rv) = self.ubiquitous.get(eff.as_str()) {
                        if rv.1.as_str() == ASYNC {
                            effs.insert(eff);
                            continue;
                        }
                    }

                    // Check if it's capability effect.
                    match &self.sigma.get(&eff).unwrap().body {
                        Body::Interface { is_capability, .. } if *is_capability => {
                            effs.insert(eff);
                        }
                        _ => return Err(ExpectedCapability(eff, loc)),
                    }
                }
                InferResult::pure(Term::Effect(effs), Term::Row)
            }
            EmitAsync(_, a) => {
                let InferResult { tm, ty, .. } = self.infer(*a)?;
                InferResult {
                    tm: Term::EmitAsync(Box::new(tm)),
                    eff: Term::async_effect(self.ubiquitous.get(ASYNC).unwrap().1.clone()),
                    ty,
                }
            }
            TryCatch(_, body, catches) => {
                let body_loc = body.loc();
                let InferResult { mut tm, eff, ty } = self.infer(*body)?;
                let effs = match eff {
                    Term::Effect(effs) => effs,
                    _ => return Err(NonCatchableExpr(tm, body_loc)),
                };
                if effs.contains(&self.ubiquitous.get(ASYNC).unwrap().1) {
                    return Err(CatchAsyncEffect(tm, body_loc));
                }

                let mut remaining_effs = effs.clone();
                let mut instances = HashMap::new();

                for catch in catches {
                    let i_loc = catch.i.loc();
                    let eff = catch.i.resolved();
                    if !effs.contains(&eff) {
                        return Err(UnresolvedEffect(eff, Term::Effect(effs), i_loc));
                    }
                    remaining_effs.remove(&eff);

                    let interface_fns = match &self.sigma.get(&eff).unwrap().body {
                        Body::Interface { fns, .. } => fns
                            .iter()
                            .map(|f| (f.to_string(), f.clone()))
                            .collect::<HashMap<_, _>>(),
                        _ => unreachable!(),
                    };
                    let mut fns = HashMap::default();
                    let mut instance_fns = Vec::default();
                    for (name, def) in catch.inst_fns {
                        if let Some(v) = interface_fns.get(&name) {
                            fns.insert(v.clone(), def.name.clone());
                        }
                        instance_fns.push(def);
                    }
                    for d in instance_fns {
                        let inst_fn = self.instance_fn_def(d)?;
                        self.sigma.insert(inst_fn.name.clone(), inst_fn);
                    }

                    let inst_name = self.vg.fresh().catch();
                    let checked_instance_body = self.check_instance_body(
                        &inst_name,
                        InstanceBody {
                            i: eff.clone(),
                            inst: Box::new(catch.inst_ty),
                            fns,
                        },
                        true,
                    )?;

                    instances.insert(eff, *checked_instance_body.inst.clone());
                    self.sigma.insert(
                        inst_name.clone(),
                        Def {
                            loc: i_loc,
                            name: inst_name,
                            tele: Default::default(),
                            eff: Box::new(Term::Pure),
                            ret: Box::new(Term::Univ),
                            body: Body::Instance(checked_instance_body),
                        },
                    );
                }

                tm = self.nf(body_loc).with_instances(instances, tm)?;

                let mut eff = Term::Pure;
                if !remaining_effs.is_empty() {
                    eff = Term::Effect(remaining_effs);
                }
                InferResult { tm, eff, ty }
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
            BigInt(_) => InferResult::pure(Term::Bigint, Term::Univ),
            Big(_, v) => InferResult::pure(Term::Big(v), Term::Bigint),
            Row(_) => InferResult::pure(Term::Row, Term::Univ),
            Rowkey(_) => InferResult::pure(Term::Rowkey, Term::Univ),

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
            self.unifier(loc).unify_eff(&expected_eff, &actual_eff)?;

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

    fn auto_unionify(fx: Term, x_ty: &Term) -> Term {
        match fx {
            Term::App(f, i, x) => match *f {
                Term::Extern(ffi) => {
                    let f = Box::new(Term::Extern(ffi));
                    let mut arg = *x;
                    let mut arg_ty = x_ty;
                    let mut args = Vec::default();
                    loop {
                        match (arg, arg_ty) {
                            (Term::Tuple(a, b), Term::Sigma(a_p, b_ty)) => {
                                args.push(if matches!(a_p.typ.as_ref(), Term::Enum(..)) {
                                    Box::new(Term::Unionify(a))
                                } else {
                                    a
                                });
                                arg = *b;
                                arg_ty = b_ty.as_ref();
                            }
                            (Term::TT, Term::Unit) => {
                                return Term::App(
                                    f,
                                    i,
                                    Box::new(
                                        args.into_iter()
                                            .rfold(Term::TT, |b, a| Term::Tuple(a, Box::new(b))),
                                    ),
                                )
                            }
                            _ if !args.is_empty() => unreachable!(),
                            (arg, _) => return Term::App(f, i, Box::new(arg)),
                        }
                    }
                }
                _ => Term::App(f, i, x),
            },
            _ => fx,
        }
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
            delayed: Default::default(),
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
