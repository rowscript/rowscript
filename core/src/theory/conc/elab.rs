use crate::theory::abs::data::Dir::Le;
use crate::theory::abs::data::{CaseMap, FieldMap, Term};
use crate::theory::abs::def::{gamma_to_tele, Body, VtblLookups};
use crate::theory::abs::def::{Def, Gamma, Sigma};
use crate::theory::abs::normalize::Normalizer;
use crate::theory::abs::unify::Unifier;
use crate::theory::conc::data::ArgInfo::{NamedImplicit, UnnamedExplicit};
use crate::theory::conc::data::{ArgInfo, Expr};
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::{Loc, Param, Tele, Var, VarGen, VPTR};
use crate::Error;
use crate::Error::{
    ExpectedClass, ExpectedEnum, ExpectedObject, ExpectedPi, ExpectedSigma, FieldsUnknown,
    NonExhaustive, UnresolvedField, UnresolvedImplicitParam,
};

#[derive(Debug)]
pub struct Elaborator {
    sigma: Sigma,
    gamma: Gamma,

    ug: VarGen,
    ig: VarGen,

    vtbl_lookups: VtblLookups,
}

impl Elaborator {
    pub fn defs(&mut self, defs: Vec<Def<Expr>>, vtbl_lookups: VtblLookups) -> Result<(), Error> {
        self.vtbl_lookups = vtbl_lookups;
        for d in defs {
            self.def(d)?;
        }
        for (_, d) in &self.sigma {
            println!("{}", d);
        }
        Ok(())
    }

    fn def(&mut self, d: Def<Expr>) -> Result<(), Error> {
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
            Fun(f) => Fun(self.check(f, &ret)?),
            Postulate => Postulate,
            Alias(t) => Alias(self.check(t, &ret)?),
            Class {
                object,
                methods,
                ctor,
                vptr,
                vptr_ctor,
                vtbl,
                vtbl_lookup,
            } => Class {
                object: self.check(object, &ret)?,
                methods,
                ctor,
                vptr,
                vptr_ctor,
                vtbl,
                vtbl_lookup,
            },
            _ => unreachable!(),
        };

        for n in checked {
            self.gamma.remove(&n);
        }

        self.sigma.get_mut(&d.name).unwrap().body = body;

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
                let body = self.guarded_check(&[&param], b, ty)?;
                Box::new(Term::Let(param, tm, body))
            }
            Lam(loc, var, body) => {
                let pi = Normalizer::new(&mut self.sigma, loc).term(ty.clone())?;
                match &*pi {
                    Term::Pi(ty_param, ty_body) => {
                        let param = Param {
                            var: var.clone(),
                            info: Explicit,
                            typ: ty_param.typ.clone(),
                        };
                        let body_type = Normalizer::new(&mut self.sigma, loc).with(
                            &[(&ty_param.var, &Box::new(Term::Ref(var)))],
                            ty_body.clone(),
                        )?;
                        let checked_body = self.guarded_check(&[&param], body, &body_type)?;
                        Box::new(Term::Lam(param.clone(), checked_body))
                    }
                    _ => return Err(ExpectedPi(pi, loc)),
                }
            }
            Tuple(loc, a, b) => {
                let sig = Normalizer::new(&mut self.sigma, loc).term(ty.clone())?;
                match &*sig {
                    Term::Sigma(ty_param, ty_body) => {
                        let a = self.check(a, &ty_param.typ)?;
                        let body_type = Normalizer::new(&mut self.sigma, loc)
                            .with(&[(&ty_param.var, &a)], ty_body.clone())?;
                        let b = self.check(b, &body_type)?;
                        Box::new(Term::Tuple(a, b))
                    }
                    _ => return Err(ExpectedSigma(sig, loc)),
                }
            }
            TupleLet(_, x, y, a, b) => {
                let a_loc = a.loc();
                let (a, a_ty) = self.infer(a, Some(ty))?;
                let sig = Normalizer::new(&mut self.sigma, a_loc).term(a_ty)?;
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
                        let b = self.guarded_check(&[&x, &y], b, ty)?;
                        Box::new(Term::TupleLet(x, y, a, b))
                    }
                    _ => return Err(ExpectedSigma(sig, a_loc)),
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
                let (mut inferred_tm, mut inferred_ty) = self.infer(e, Some(ty))?;
                if let Some(f_e) = Self::app_insert_holes(f_e, UnnamedExplicit, &*inferred_ty)? {
                    let (new_tm, new_ty) = self.infer(f_e, Some(ty))?;
                    inferred_tm = new_tm;
                    inferred_ty = new_ty;
                }
                let inferred = Normalizer::new(&mut self.sigma, loc).term(inferred_ty)?;
                let expected = Normalizer::new(&mut self.sigma, loc).term(ty.clone())?;
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
        Ok(match *e {
            Resolved(_, v) => {
                if let Some(ty) = self.gamma.get(&v) {
                    (Box::new(Term::Ref(v)), ty.clone())
                } else {
                    let d = self.sigma.get(&v).unwrap();
                    (d.to_term(v), d.to_type())
                }
            }
            Hole(loc) => self.insert_meta(loc, true),
            InsertedHole(loc) => self.insert_meta(loc, false),
            Pi(_, p, b) => {
                let (param_ty, _) = self.infer(p.typ, hint)?;
                let param = Param {
                    var: p.var,
                    info: p.info,
                    typ: param_ty,
                };
                let (b, b_ty) = self.guarded_infer(&[&param], b, hint)?;
                (Box::new(Term::Pi(param, b)), b_ty)
            }
            App(_, f, i, x) => {
                let loc = f.loc();
                let f_e = f.clone();
                let (f, f_ty) = self.infer(f, hint)?;
                if let Some(f_e) = Self::app_insert_holes(f_e, i.clone(), &*f_ty)? {
                    return self.infer(Box::new(App(loc, f_e, i, x)), hint);
                }
                match *f_ty {
                    Term::Pi(p, b) => {
                        let x = self.guarded_check(
                            &[&Param {
                                var: p.var.clone(),
                                info: p.info,
                                typ: p.typ.clone(),
                            }],
                            x,
                            &p.typ,
                        )?;
                        let applied = Normalizer::new(&mut self.sigma, loc).apply(f, &[&x])?;
                        let applied_ty =
                            Normalizer::new(&mut self.sigma, loc).with(&[(&p.var, &x)], b)?;
                        (applied, applied_ty)
                    }
                    _ => return Err(ExpectedPi(f, loc)),
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
                (Box::new(Term::Sigma(param, b)), b_ty)
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
                    (Term::Object(_), y_ty) => return Err(ExpectedObject(Box::new(y_ty), y_loc)),
                    (x_ty, _) => return Err(ExpectedObject(Box::new(x_ty), x_loc)),
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
                    Term::lam(&tele, Box::new(Term::Access(Box::new(Term::Ref(o)), n))),
                    Term::pi(&tele, Box::new(Term::Ref(t))),
                )
            }
            Downcast(loc, a) => {
                let b_ty = Normalizer::new(&mut self.sigma, loc).term(hint.unwrap().clone())?;
                let (a, a_ty) = self.infer(a, hint)?;
                match (&*a_ty, &*b_ty) {
                    (Term::Object(from), Term::Object(to)) => {
                        let tele = vec![Param {
                            var: Var::unbound(),
                            info: Implicit,
                            typ: Box::new(Term::RowOrd(to.clone(), Le, from.clone())),
                        }];
                        (
                            Term::lam(&tele, Box::new(Term::Downcast(a, to.clone()))),
                            Term::pi(&tele, Box::new(Term::Object(to.clone()))),
                        )
                    }
                    (Term::Object(_), _) => return Err(ExpectedObject(b_ty, loc)),
                    _ => return Err(ExpectedObject(a_ty, loc)),
                }
            }
            Enum(_, r) => {
                let r = self.check(r, &Box::new(Term::Row))?;
                (Box::new(Term::Enum(r)), Box::new(Term::Univ))
            }
            Variant(loc, n, a) => {
                let b_ty = Normalizer::new(&mut self.sigma, loc).term(hint.unwrap().clone())?;
                let (a, a_ty) = self.infer(a, hint)?;
                match &*b_ty {
                    Term::Enum(to) => {
                        let ty_fields = FieldMap::from([(n.clone(), *a_ty)]);
                        let tm_fields = FieldMap::from([(n, *a)]);
                        let from = Box::new(Term::Fields(ty_fields));
                        let tele = vec![Param {
                            var: Var::unbound(),
                            info: Implicit,
                            typ: Box::new(Term::RowOrd(from.clone(), Le, to.clone())),
                        }];
                        (
                            Term::lam(
                                &tele,
                                Box::new(Term::Variant(Box::new(Term::Fields(tm_fields)))),
                            ),
                            Term::pi(&tele, Box::new(Term::Enum(to.clone()))),
                        )
                    }
                    _ => return Err(ExpectedEnum(b_ty, loc)),
                }
            }
            Upcast(loc, a) => {
                let b_ty = Normalizer::new(&mut self.sigma, loc).term(hint.unwrap().clone())?;
                let (a, a_ty) = self.infer(a, hint)?;
                match (&*a_ty, &*b_ty) {
                    (Term::Enum(from), Term::Enum(to)) => {
                        let tele = vec![Param {
                            var: Var::unbound(),
                            info: Implicit,
                            typ: Box::new(Term::RowOrd(from.clone(), Le, to.clone())),
                        }];
                        (
                            Term::lam(&tele, Box::new(Term::Upcast(a, to.clone()))),
                            Term::pi(&tele, Box::new(Term::Enum(to.clone()))),
                        )
                    }
                    (Term::Enum(_), _) => return Err(ExpectedEnum(b_ty, loc)),
                    _ => return Err(ExpectedEnum(a_ty, loc)),
                }
            }
            Switch(loc, a, cs) => {
                let ret_ty = hint.unwrap();
                let a_loc = a.loc();
                let (a, a_ty) = self.infer(a, hint)?;
                let en = Normalizer::new(&mut self.sigma, loc).term(a_ty)?;
                match *en {
                    Term::Enum(y) => match *y {
                        Term::Fields(f) => {
                            if f.len() != cs.len() {
                                return Err(NonExhaustive(Box::new(Term::Fields(f.clone())), loc));
                            }
                            let mut m = CaseMap::default();
                            for (n, v, e) in cs {
                                let ty = f.get(&n).ok_or(UnresolvedField(
                                    n.clone(),
                                    Box::new(Term::Fields(f.clone())),
                                    loc,
                                ))?;
                                let p = Param {
                                    var: v.clone(),
                                    info: Explicit,
                                    typ: Box::new(ty.clone()),
                                };
                                let tm = *self.guarded_check(&[&p], Box::new(e), ret_ty)?;
                                m.insert(n, (v, tm));
                            }
                            (Box::new(Term::Switch(a, m)), ret_ty.clone())
                        }
                        y => return Err(FieldsUnknown(Box::new(y), loc)),
                    },
                    en => return Err(ExpectedEnum(Box::new(en), a_loc)),
                }
            }
            Lookup(loc, o, n, arg) => {
                let o_loc = o.loc();
                match *self.infer(o.clone(), hint)?.1 {
                    Term::Object(f) => match *f {
                        Term::Fields(f) => match f.get(VPTR) {
                            Some(vp) => match vp {
                                Term::Ref(v) => {
                                    let lookup = self.vtbl_lookups.get(v);
                                    let desugared = Box::new(App(
                                        loc,
                                        Box::new(App(
                                            loc,
                                            Box::new(Access(loc, n)),
                                            UnnamedExplicit,
                                            Box::new(App(
                                                loc,
                                                Box::new(Resolved(loc, lookup)),
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
                                    Box::new(Term::Object(Box::new(Term::Fields(f)))),
                                    o_loc,
                                ))
                            }
                        },
                        tm => return Err(FieldsUnknown(Box::new(tm), o_loc)),
                    },
                    tm => return Err(ExpectedClass(Box::new(tm), o_loc)),
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

    fn guarded_check(
        &mut self,
        ps: &[&Param<Term>],
        e: Box<Expr>,
        ty: &Box<Term>,
    ) -> Result<Box<Term>, Error> {
        for &p in ps {
            self.gamma.insert(p.var.clone(), p.typ.clone());
        }
        let ret = self.check(e, ty)?;
        for p in ps {
            self.gamma.remove(&p.var);
        }
        Ok(ret)
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

    fn insert_meta(&mut self, loc: Loc, is_user: bool) -> (Box<Term>, Box<Term>) {
        use Body::*;

        let ty_meta_var = self.ig.fresh();
        self.sigma.insert(
            ty_meta_var.clone(),
            Def::new_constant_constraint(loc, ty_meta_var.clone(), Box::new(Term::Univ)),
        );
        let ty = Box::new(Term::MetaRef(ty_meta_var, Default::default()));

        let tm_meta_var = if is_user {
            self.ug.fresh()
        } else {
            self.ig.fresh()
        };
        let tele = gamma_to_tele(&self.gamma);
        let spine = Term::tele_to_spine(&tele);
        self.sigma.insert(
            tm_meta_var.clone(),
            Def {
                loc,
                name: tm_meta_var.clone(),
                tele,
                ret: ty.clone(),
                body: Meta(None),
            },
        );
        (Box::new(Term::MetaRef(tm_meta_var, spine)), ty)
    }

    fn app_insert_holes(f: Box<Expr>, i: ArgInfo, f_ty: &Term) -> Result<Option<Box<Expr>>, Error> {
        fn n_to_insert(n: usize, loc: Loc, name: String, ty: &Term) -> Result<usize, Error> {
            match ty {
                Term::Pi(p, b) => {
                    if p.info == Implicit {
                        if *p.var.name == name {
                            Ok(n)
                        } else {
                            n_to_insert(n + 1, loc, name, &*b)
                        }
                    } else {
                        Err(UnresolvedImplicitParam(name, loc))
                    }
                }
                _ => unreachable!(),
            }
        }

        Ok(match f_ty {
            Term::Pi(p, _) if p.info == Implicit => match i {
                UnnamedExplicit => Some(Expr::holed_app(f)),
                NamedImplicit(name) => {
                    let n = n_to_insert(0, f.loc(), name, f_ty)?;
                    if n == 0 {
                        None
                    } else {
                        let mut ret = Expr::holed_app(f);
                        for _ in 1..n {
                            ret = Expr::holed_app(ret);
                        }
                        Some(ret)
                    }
                }
                _ => None,
            },
            _ => None,
        })
    }
}

impl Default for Elaborator {
    fn default() -> Self {
        Self {
            sigma: Default::default(),
            gamma: Default::default(),
            ug: VarGen::user_meta(),
            ig: VarGen::inserted_meta(),
            vtbl_lookups: Default::default(),
        }
    }
}
