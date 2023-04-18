use std::collections::HashMap;

use crate::theory::abs::data::Dir::Le;
use crate::theory::abs::data::{CaseMap, FieldMap, MetaKind, Term};
use crate::theory::abs::def::{gamma_to_tele, Body};
use crate::theory::abs::def::{Def, Gamma, Sigma};
use crate::theory::abs::normalize::Normalizer;
use crate::theory::abs::rename::rename;
use crate::theory::abs::unify::Unifier;
use crate::theory::conc::data::ArgInfo::{NamedImplicit, UnnamedExplicit};
use crate::theory::conc::data::{ArgInfo, Expr};
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::{Loc, Param, Tele, Var, VarGen, VPTR};
use crate::Error;
use crate::Error::{
    ExpectedAlias, ExpectedClass, ExpectedEnum, ExpectedImplementsOf, ExpectedInterface,
    ExpectedObject, ExpectedPi, ExpectedSigma, FieldsUnknown, NonExhaustive, UnresolvedField,
    UnresolvedImplicitParam,
};

#[derive(Debug, Default)]
pub struct Elaborator {
    pub sigma: Sigma,
    gamma: Gamma,
    vg: VarGen,
}

impl Elaborator {
    pub fn defs(&mut self, defs: Vec<Def<Expr>>) -> Result<Vec<Def<Term>>, Error> {
        let mut ret = Vec::default();
        for d in defs {
            ret.push(self.def(d)?);
        }
        Ok(ret)
    }

    fn def(&mut self, d: Def<Expr>) -> Result<Def<Term>, Error> {
        use Body::*;

        let mut checked = Vec::default();
        let mut tele = Tele::default();
        for p in d.tele {
            let gamma_var = p.var.clone();
            let checked_var = p.var.clone();
            let var = p.var.clone();

            let gamma_typ = self.check(p.typ, &Box::new(Term::Univ))?;
            let typ = gamma_typ.clone();

            self.gamma.insert(gamma_var, gamma_typ);
            checked.push(checked_var);
            tele.push(Param {
                var,
                info: p.info,
                typ,
            })
        }

        let ret = self.check(d.ret, &Box::new(Term::Univ))?;
        self.sigma.insert(
            d.name.clone(),
            Def {
                loc: d.loc,
                name: d.name.clone(),
                tele,
                ret: ret.clone(),
                body: Undefined,
            },
        );

        let body = match d.body {
            Fn(f) => Fn(*self.check(Box::from(f), &ret)?),
            Postulate => Postulate,
            Alias(t) => Alias(*self.check(Box::from(t), &ret)?),

            Class {
                object,
                methods,
                ctor,
                vptr,
                vptr_ctor,
                vtbl,
                vtbl_lookup,
            } => Class {
                object: *self.check(Box::from(object), &ret)?,
                methods,
                ctor,
                vptr,
                vptr_ctor,
                vtbl,
                vtbl_lookup,
            },
            Ctor(f) => Ctor(*self.check(Box::from(f), &ret)?),
            Method(f) => Method(*self.check(Box::from(f), &ret)?),
            VptrType(t) => VptrType(*self.check(Box::from(t), &ret)?),
            VptrCtor(t) => VptrCtor(t),
            VtblType(t) => VtblType(*self.check(Box::from(t), &ret)?),
            VtblLookup => VtblLookup,

            Interface { fns, ims } => Interface { fns, ims },
            Implements { i, fns } => {
                self.push_implements(&d.name, &i, &fns)?;
                Implements { i, fns }
            }
            ImplementsFn(f) => ImplementsFn(*self.check(Box::from(f), &ret)?),
            Findable(i) => Findable(i),

            Undefined => unreachable!(),
            Meta(_, _) => unreachable!(),
        };

        for n in checked {
            self.gamma.remove(&n);
        }

        let mut checked = self.sigma.get_mut(&d.name).unwrap();
        checked.body = body;

        Ok(checked.clone())
    }

    fn push_implements(
        &mut self,
        d: &Var,
        i: &(Var, Var),
        im_fns: &HashMap<Var, Var>,
    ) -> Result<(), Error> {
        use Body::*;
        use Expr::*;

        let (i, im) = i;

        let im_def = self.sigma.get(im).unwrap();
        let im_def_loc = im_def.loc;
        let im_tm = im_def.to_term(im.clone());
        match im_def.body {
            Alias(_) => {}
            _ => return Err(ExpectedAlias(Term::Ref(im.clone()), im_def_loc)),
        }

        let i_def = self.sigma.get_mut(i).unwrap();
        let i_def_loc = i_def.loc;
        match &mut i_def.body {
            Interface { fns, ims, .. } => {
                ims.push(d.clone());
                for f in fns {
                    if im_fns.contains_key(f) {
                        continue;
                    }
                    return Err(NonExhaustive(Term::Ref(im.clone()), i_def_loc));
                }
            }
            _ => return Err(ExpectedInterface(Term::Ref(i.clone()), i_def_loc)),
        };

        for (i_fn, im_fn) in im_fns {
            let i_fn_def = self.sigma.get(i_fn).unwrap();

            let i_loc = i_fn_def.loc;
            let im_loc = self.sigma.get(im_fn).unwrap().loc;

            let (i_fn_ty_p, i_fn_ty_b) = match *i_fn_def.to_type() {
                Term::Pi(p, b) => (p, b),
                _ => unreachable!(),
            };
            let i_fn_ty_applied = Normalizer::new(&mut self.sigma, i_loc)
                .with(&[(&i_fn_ty_p.var, &im_tm)], *i_fn_ty_b)?;
            let (_, im_fn_ty) = self.infer(Box::new(Resolved(im_loc, im_fn.clone())), None)?;

            Unifier::new(&mut self.sigma, im_loc).unify(&i_fn_ty_applied, &im_fn_ty)?;
        }

        Ok(())
    }

    fn check(&mut self, e: Box<Expr>, ty: &Box<Term>) -> Result<Box<Term>, Error> {
        use Expr::*;

        Ok(match *e {
            Let(_, var, maybe_typ, a, b) => {
                let (tm, typ) = if let Some(t) = maybe_typ {
                    let checked_ty = self.check(t, &Box::new(Term::Univ))?;
                    (self.check(a, &checked_ty)?, checked_ty)
                } else {
                    self.infer(a, Some(ty))?
                };
                let param = Param {
                    var,
                    info: Explicit,
                    typ,
                };
                let body = self.guarded_check(&[&param], *b, ty)?;
                Box::new(Term::Let(param, tm, Box::from(body)))
            }
            Lam(loc, var, body) => {
                let pi = Box::new(Normalizer::new(&mut self.sigma, loc).term(*ty.clone())?);
                match &*pi {
                    Term::Pi(ty_param, ty_body) => {
                        let param = Param {
                            var: var.clone(),
                            info: Explicit,
                            typ: ty_param.typ.clone(),
                        };
                        let body_type = Normalizer::new(&mut self.sigma, loc)
                            .with(&[(&ty_param.var, &Term::Ref(var))], *ty_body.clone())?;
                        let checked_body =
                            self.guarded_check(&[&param], *body, &Box::new(body_type))?;
                        Box::new(Term::Lam(param.clone(), Box::from(checked_body)))
                    }
                    _ => return Err(ExpectedPi(*pi, loc)),
                }
            }
            Tuple(loc, a, b) => {
                let sig = Box::new(Normalizer::new(&mut self.sigma, loc).term(*ty.clone())?);
                match &*sig {
                    Term::Sigma(ty_param, ty_body) => {
                        let a = *self.check(a, &ty_param.typ)?;
                        let body_type = Normalizer::new(&mut self.sigma, loc)
                            .with(&[(&ty_param.var, &a)], *ty_body.clone())?;
                        let b = *self.check(b, &Box::new(body_type))?;
                        Box::new(Term::Tuple(Box::from(a), Box::from(b)))
                    }
                    _ => return Err(ExpectedSigma(*sig, loc)),
                }
            }
            TupleLet(_, x, y, a, b) => {
                let a_loc = a.loc();
                let (a, a_ty) = self.infer(a, Some(ty))?;
                let sig = Box::new(Normalizer::new(&mut self.sigma, a_loc).term(*a_ty)?);
                match &*sig {
                    Term::Sigma(ty_param, ty_body) => {
                        let x = Param {
                            var: x,
                            info: Explicit,
                            typ: ty_param.typ.clone(),
                        };
                        let y = Param {
                            var: y,
                            info: Explicit,
                            typ: ty_body.clone(),
                        };
                        let b = self.guarded_check(&[&x, &y], *b, ty)?;
                        Box::new(Term::TupleLet(x, y, a, Box::from(b)))
                    }
                    _ => return Err(ExpectedSigma(*sig, a_loc)),
                }
            }
            UnitLet(_, a, b) => Box::new(Term::UnitLet(
                self.check(a, &Box::new(Term::Unit))?,
                self.check(b, ty)?,
            )),
            If(_, p, t, e) => Box::new(Term::If(
                self.check(p, &Box::new(Term::Boolean))?,
                self.check(t, ty)?,
                self.check(e, ty)?,
            )),
            _ => {
                let loc = e.loc();
                let f_e = e.clone();

                let (mut inferred_tm, inferred_ty) = self.infer(e, Some(ty))?;
                let mut inferred =
                    Box::new(Normalizer::new(&mut self.sigma, loc).term(*inferred_ty)?);
                let expected = Box::new(Normalizer::new(&mut self.sigma, loc).term(*ty.clone())?);

                if Self::is_hole_insertable(&expected) {
                    if let Some(f_e) = Self::app_insert_holes(*f_e, UnnamedExplicit, &inferred)? {
                        let (new_tm, new_ty) = self.infer(Box::from(f_e), Some(ty))?;
                        inferred_tm = new_tm;
                        inferred = new_ty;
                    }
                }

                Unifier::new(&mut self.sigma, loc).unify(&expected, &inferred)?;

                inferred_tm
            }
        })
    }

    fn infer(
        &mut self,
        e: Box<Expr>,
        hint: Option<&Box<Term>>,
    ) -> Result<(Box<Term>, Box<Term>), Error> {
        use Expr::*;
        use MetaKind::*;

        Ok(match *e {
            Resolved(_, v) => match self.gamma.get(&v) {
                Some(ty) => (Box::new(Term::Ref(v)), ty.clone()),
                None => {
                    let d = self.sigma.get(&v).unwrap();
                    (d.to_term(v), d.to_type())
                }
            },
            Hole(loc) => self.insert_meta(loc, UserMeta),
            InsertedHole(loc) => self.insert_meta(loc, InsertedMeta),
            Pi(_, p, b) => {
                let (param_ty, _) = self.infer(p.typ, hint)?;
                let param = Param {
                    var: p.var,
                    info: p.info,
                    typ: param_ty,
                };
                let (b, b_ty) = self.guarded_infer(&[&param], b, hint)?;
                (Box::new(Term::Pi(param, Box::from(b))), Box::from(b_ty))
            }
            AnnoLam(_, p, b) => {
                let (p_ty, _) = self.infer(p.typ, hint)?;
                let param = Param {
                    var: p.var,
                    info: p.info,
                    typ: p_ty,
                };
                let (b, b_ty) = self.guarded_infer(&[&param], b, hint)?;
                (
                    Box::new(Term::Lam(param.clone(), Box::from(b))),
                    Box::new(Term::Pi(param, Box::from(b_ty))),
                )
            }
            App(_, f, ai, x) => {
                let f_loc = f.loc();
                let f_e = f.clone();
                let (f, f_ty) = self.infer(f, hint)?;

                if let Some(f_e) = Self::app_insert_holes(*f_e, ai.clone(), &f_ty)? {
                    return self.infer(Box::new(App(f_loc, Box::from(f_e), ai, x)), hint);
                }

                match *f_ty {
                    Term::Pi(p, b) => {
                        let x = self.guarded_check(
                            &[&Param {
                                var: p.var.clone(),
                                info: p.info,
                                typ: p.typ.clone(),
                            }],
                            *x,
                            &p.typ,
                        )?;
                        let applied_ty =
                            Normalizer::new(&mut self.sigma, f_loc).with(&[(&p.var, &x)], *b)?;
                        let applied = Normalizer::new(&mut self.sigma, f_loc).apply(
                            *f,
                            p.info.into(),
                            &[x],
                        )?;
                        (Box::from(applied), Box::from(applied_ty))
                    }
                    ty => return Err(ExpectedPi(*Box::new(ty), f_loc)),
                }
            }
            Sigma(_, p, b) => {
                let (param_ty, _) = self.infer(p.typ, hint)?;
                let param = Param {
                    var: p.var,
                    info: p.info,
                    typ: param_ty,
                };
                let (b, b_ty) = self.guarded_infer(&[&param], b, hint)?;
                (Box::new(Term::Sigma(param, Box::from(b))), Box::from(b_ty))
            }
            Tuple(_, a, b) => {
                let (a, a_ty) = self.infer(a, hint)?;
                let (b, b_ty) = self.infer(b, hint)?;
                (
                    Box::new(Term::Tuple(a, b)),
                    Box::new(Term::Sigma(
                        Param {
                            var: Var::unbound(),
                            info: Explicit,
                            typ: a_ty,
                        },
                        b_ty,
                    )),
                )
            }
            AnnoTupleLet(_, p, q, a, b) => {
                let p_ty = self.check(p.typ, &Box::new(Term::Univ))?;
                let p = Param {
                    var: p.var,
                    info: p.info,
                    typ: p_ty,
                };
                let q_ty = self.guarded_check(&[&p], *q.typ, &Box::new(Term::Univ))?;
                let q = Param {
                    var: q.var,
                    info: q.info,
                    typ: Box::from(q_ty),
                };
                let (b, b_ty) = self.guarded_infer(&[&p, &q], b, hint)?;
                let a = self.check(a, &Box::new(Term::Sigma(p.clone(), q.typ.clone())))?;
                (
                    Box::new(Term::TupleLet(p, q, a, Box::from(b))),
                    Box::from(b_ty),
                )
            }
            Fields(_, fields) => {
                let mut inferred = FieldMap::default();
                for (f, e) in fields {
                    let (tm, _) = self.infer(Box::new(e), hint)?;
                    inferred.insert(f, *tm);
                }
                (Box::new(Term::Fields(inferred)), Box::new(Term::Row))
            }
            Combine(_, a, b) => {
                let a = self.check(a, &Box::new(Term::Row))?;
                let b = self.check(b, &Box::new(Term::Row))?;
                (Box::new(Term::Combine(a, b)), Box::new(Term::Row))
            }
            RowOrd(_, a, d, b) => {
                let a = self.check(a, &Box::new(Term::Row))?;
                let b = self.check(b, &Box::new(Term::Row))?;
                (Box::new(Term::RowOrd(a, d, b)), Box::new(Term::Univ))
            }
            RowEq(_, a, b) => {
                let a = self.check(a, &Box::new(Term::Row))?;
                let b = self.check(b, &Box::new(Term::Row))?;
                (Box::new(Term::RowEq(a, b)), Box::new(Term::Univ))
            }
            Object(_, r) => {
                let r = self.check(r, &Box::new(Term::Row))?;
                (Box::new(Term::Object(r)), Box::new(Term::Univ))
            }
            Obj(_, r) => match *r {
                Fields(_, fields) => {
                    let mut tm_fields = FieldMap::default();
                    let mut ty_fields = FieldMap::default();
                    for (n, e) in fields {
                        let (tm, ty) = self.infer(Box::new(e), hint)?;
                        tm_fields.insert(n.clone(), *tm);
                        ty_fields.insert(n, *ty);
                    }
                    (
                        Box::new(Term::Obj(Box::new(Term::Fields(tm_fields)))),
                        Box::new(Term::Object(Box::new(Term::Fields(ty_fields)))),
                    )
                }
                _ => unreachable!(),
            },
            Concat(_, a, b) => {
                let x_loc = a.loc();
                let y_loc = b.loc();
                let (x, x_ty) = self.infer(a, hint)?;
                let (y, y_ty) = self.infer(b, hint)?;
                let ty = match (*x_ty, *y_ty) {
                    (Term::Object(rx), Term::Object(ry)) => {
                        Box::new(Term::Object(Box::new(Term::Combine(rx, ry))))
                    }
                    (Term::Object(_), y_ty) => return Err(ExpectedObject(*Box::new(y_ty), y_loc)),
                    (x_ty, _) => return Err(ExpectedObject(*Box::new(x_ty), x_loc)),
                };
                (Box::new(Term::Concat(x, y)), ty)
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
                            Le,
                            Box::new(Term::Ref(a)),
                        )),
                    },
                ];
                (
                    Box::new(rename(Term::lam(
                        &tele,
                        Term::Access(Box::new(Term::Ref(o)), n),
                    ))),
                    Box::new(rename(Term::pi(&tele, Term::Ref(t)))),
                )
            }
            Downcast(loc, a) => {
                let b_ty =
                    Box::new(Normalizer::new(&mut self.sigma, loc).term(*hint.unwrap().clone())?);
                let (a, a_ty) = self.infer(a, hint)?;
                match (&*a_ty, &*b_ty) {
                    (Term::Object(from), Term::Object(to)) => {
                        let tele = vec![Param {
                            var: Var::unbound(),
                            info: Implicit,
                            typ: Box::new(Term::RowOrd(to.clone(), Le, from.clone())),
                        }];
                        (
                            Box::new(rename(Term::lam(&tele, Term::Downcast(a, to.clone())))),
                            Box::new(rename(Term::pi(&tele, Term::Object(to.clone())))),
                        )
                    }
                    (Term::Object(_), _) => return Err(ExpectedObject(*b_ty, loc)),
                    _ => return Err(ExpectedObject(*a_ty, loc)),
                }
            }
            Enum(_, r) => {
                let r = self.check(r, &Box::new(Term::Row))?;
                (Box::new(Term::Enum(r)), Box::new(Term::Univ))
            }
            Variant(loc, n, a) => {
                let b_ty =
                    Box::new(Normalizer::new(&mut self.sigma, loc).term(*hint.unwrap().clone())?);
                let (a, a_ty) = self.infer(a, hint)?;
                match &*b_ty {
                    Term::Enum(to) => {
                        let ty_fields = FieldMap::from([(n.clone(), *a_ty)]);
                        let tm_fields = FieldMap::from([(n, *a)]);
                        let from = Box::new(Term::Fields(ty_fields));
                        let tele = vec![Param {
                            var: Var::unbound(),
                            info: Implicit,
                            typ: Box::new(Term::RowOrd(from, Le, to.clone())),
                        }];
                        (
                            Box::new(rename(Term::lam(
                                &tele,
                                Term::Variant(Box::new(Term::Fields(tm_fields))),
                            ))),
                            Box::new(rename(Term::pi(&tele, Term::Enum(to.clone())))),
                        )
                    }
                    _ => return Err(ExpectedEnum(*b_ty, loc)),
                }
            }
            Upcast(loc, a) => {
                let b_ty =
                    Box::new(Normalizer::new(&mut self.sigma, loc).term(*hint.unwrap().clone())?);
                let (a, a_ty) = self.infer(a, hint)?;
                match (&*a_ty, &*b_ty) {
                    (Term::Enum(from), Term::Enum(to)) => {
                        let tele = vec![Param {
                            var: Var::unbound(),
                            info: Implicit,
                            typ: Box::new(Term::RowOrd(from.clone(), Le, to.clone())),
                        }];
                        (
                            Box::new(rename(Term::lam(&tele, Term::Upcast(a, to.clone())))),
                            Box::new(rename(Term::pi(&tele, Term::Enum(to.clone())))),
                        )
                    }
                    (Term::Enum(_), _) => return Err(ExpectedEnum(*b_ty, loc)),
                    _ => return Err(ExpectedEnum(*a_ty, loc)),
                }
            }
            Switch(loc, a, cs) => {
                let ret_ty = hint.unwrap();
                let a_loc = a.loc();
                let (a, a_ty) = self.infer(a, hint)?;
                let en = Box::new(Normalizer::new(&mut self.sigma, loc).term(*a_ty)?);
                match *en {
                    Term::Enum(y) => match *y {
                        Term::Fields(f) => {
                            if f.len() != cs.len() {
                                return Err(NonExhaustive(*Box::new(Term::Fields(f)), loc));
                            }
                            let mut m = CaseMap::default();
                            for (n, v, e) in cs {
                                let ty = f.get(&n).ok_or(UnresolvedField(
                                    n.clone(),
                                    *Box::new(Term::Fields(f.clone())),
                                    loc,
                                ))?;
                                let p = Param {
                                    var: v.clone(),
                                    info: Explicit,
                                    typ: Box::new(ty.clone()),
                                };
                                let tm = self.guarded_check(&[&p], *Box::new(e), ret_ty)?;
                                m.insert(n, (v, tm));
                            }
                            (Box::new(Term::Switch(a, m)), ret_ty.clone())
                        }
                        y => return Err(FieldsUnknown(*Box::new(y), loc)),
                    },
                    en => return Err(ExpectedEnum(*Box::new(en), a_loc)),
                }
            }
            Lookup(loc, o, n, arg) => {
                let o_loc = o.loc();
                match *self.infer(o.clone(), hint)?.1 {
                    Term::Object(f) => match *f {
                        Term::Fields(f) => match f.get(VPTR) {
                            Some(vp) => match vp {
                                Term::Vptr(v, _) => {
                                    let desugared = Box::new(App(
                                        loc,
                                        Box::new(App(
                                            loc,
                                            Box::new(Access(loc, n)),
                                            UnnamedExplicit,
                                            Box::new(App(
                                                loc,
                                                Box::new(Resolved(loc, v.clone())),
                                                UnnamedExplicit,
                                                Box::new(App(
                                                    loc,
                                                    Box::new(Access(loc, VPTR.to_string())),
                                                    UnnamedExplicit,
                                                    o.clone(),
                                                )),
                                            )),
                                        )),
                                        UnnamedExplicit,
                                        Box::new(Tuple(arg.loc(), o, arg)),
                                    ));
                                    self.infer(desugared, hint)?
                                }
                                _ => unreachable!(),
                            },
                            None => {
                                return Err(ExpectedClass(
                                    *Box::new(Term::Object(Box::new(Term::Fields(f)))),
                                    o_loc,
                                ));
                            }
                        },
                        tm => return Err(FieldsUnknown(*Box::new(tm), o_loc)),
                    },
                    tm => return Err(ExpectedClass(*Box::new(tm), o_loc)),
                }
            }
            Vptr(_, r, ts) => {
                let mut types = Vec::default();
                for t in ts {
                    types.push(*self.infer(Box::new(t), hint)?.0);
                }
                (Box::new(Term::Vptr(r, types)), Box::new(Term::Univ))
            }
            Find(_, _, f) => {
                let ty = self.sigma.get(&f).unwrap().to_type();
                (Box::new(Term::Ref(f)), ty)
            }
            ImplementsOf(loc, a) => {
                let (tm, ty) = self.infer(a, hint)?;
                match *tm {
                    Term::ImplementsOf(a, i) => (Box::new(Term::ImplementsOf(a, i)), ty),
                    tm => return Err(ExpectedImplementsOf(*Box::new(tm), loc)),
                }
            }

            Univ(_) => (Box::new(Term::Univ), Box::new(Term::Univ)),
            Unit(_) => (Box::new(Term::Unit), Box::new(Term::Univ)),
            TT(_) => (Box::new(Term::TT), Box::new(Term::Unit)),
            Boolean(_) => (Box::new(Term::Boolean), Box::new(Term::Univ)),
            False(_) => (Box::new(Term::False), Box::new(Term::Boolean)),
            True(_) => (Box::new(Term::True), Box::new(Term::Boolean)),
            String(_) => (Box::new(Term::String), Box::new(Term::Univ)),
            Str(_, v) => (Box::new(Term::Str(v)), Box::new(Term::String)),
            Number(_) => (Box::new(Term::Number), Box::new(Term::Univ)),
            Num(_, r) => {
                let v = r.parse().unwrap();
                (Box::new(Term::Num(r, v)), Box::new(Term::Number))
            }
            BigInt(_) => (Box::new(Term::BigInt), Box::new(Term::Univ)),
            Big(_, v) => (Box::new(Term::Big(v)), Box::new(Term::BigInt)),
            Row(_) => (Box::new(Term::Row), Box::new(Term::Univ)),

            _ => unreachable!(),
        })
    }

    fn guarded_check(&mut self, ps: &[&Param<Term>], e: Expr, ty: &Term) -> Result<Term, Error> {
        for &p in ps {
            self.gamma.insert(p.var.clone(), p.typ.clone());
        }
        let ret = self.check(Box::from(e), &Box::new(ty.clone()))?;
        for p in ps {
            self.gamma.remove(&p.var);
        }
        Ok(*ret)
    }

    fn guarded_infer(
        &mut self,
        ps: &[&Param<Term>],
        e: Box<Expr>,
        hint: Option<&Box<Term>>,
    ) -> Result<(Box<Term>, Box<Term>), Error> {
        for &p in ps {
            self.gamma.insert(p.var.clone(), p.typ.clone());
        }
        let ret = self.infer(e, hint)?;
        for p in ps {
            self.gamma.remove(&p.var);
        }
        Ok(ret)
    }

    fn insert_meta(&mut self, loc: Loc, k: MetaKind) -> (Box<Term>, Box<Term>) {
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
        let ty = Box::new(Term::MetaRef(k.clone(), ty_meta_var, Default::default()));

        let tm_meta_var = self.vg.fresh();
        let tele = gamma_to_tele(&self.gamma);
        let spine = Term::tele_to_spine(&tele);
        self.sigma.insert(
            tm_meta_var.clone(),
            Def {
                loc,
                name: tm_meta_var.clone(),
                tele,
                ret: ty.clone(),
                body: Meta(k.clone(), None),
            },
        );
        (Box::new(Term::MetaRef(k, tm_meta_var, spine)), ty)
    }

    fn is_hole_insertable(expected: &Term) -> bool {
        match expected {
            Term::Pi(p, _) => p.info != Implicit,
            _ => true,
        }
    }

    fn app_insert_holes(f_e: Expr, i: ArgInfo, f_ty: &Term) -> Result<Option<Expr>, Error> {
        fn holes_to_insert(loc: Loc, name: String, mut ty: &Term) -> Result<usize, Error> {
            let mut ret = Default::default();
            loop {
                match ty {
                    Term::Pi(p, b) => {
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
            Term::Pi(p, _) if p.info == Implicit => match i {
                UnnamedExplicit => Some(Expr::holed_app(f_e)),
                NamedImplicit(name) => match holes_to_insert(f_e.loc(), name, f_ty)? {
                    0 => None,
                    n => Some((0..n).fold(f_e, |e, _| Expr::holed_app(e))),
                },
                _ => None,
            },
            _ => None,
        })
    }
}
