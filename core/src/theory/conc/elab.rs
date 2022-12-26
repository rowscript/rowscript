use crate::theory::abs::data::Dir::Le;
use crate::theory::abs::data::{FieldMap, Term};
use crate::theory::abs::def::{gamma_to_tele, Body};
use crate::theory::abs::def::{Def, Gamma, Sigma};
use crate::theory::abs::normalize::Normalizer;
use crate::theory::abs::rename::rename;
use crate::theory::abs::unify::Unifier;
use crate::theory::conc::data::ArgInfo::{NamedImplicit, UnnamedExplicit};
use crate::theory::conc::data::{ArgInfo, Expr};
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::{Loc, Param, Tele, Var, VarGen};
use crate::Error;
use crate::Error::{ExpectedObject, ExpectedPi, ExpectedSigma, UnresolvedImplicitParam};

#[derive(Debug)]
pub struct Elaborator {
    sigma: Sigma,
    gamma: Gamma,
    ug: VarGen,
    ig: VarGen,
}

impl Elaborator {
    pub fn defs(&mut self, defs: Vec<Def<Expr>>) -> Result<(), Error> {
        for d in defs {
            let name = d.name.clone();
            let checked = self.def(d)?;
            self.sigma.insert(name, checked);
        }
        for (_, d) in &self.sigma {
            println!("{}", d);
        }
        Ok(())
    }

    fn def(&mut self, d: Def<Expr>) -> Result<Def<Term>, Error> {
        use Body::*;

        let mut checked: Vec<Var> = Default::default();
        let mut tele: Tele<Term> = Default::default();
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
        let body = match d.body {
            Fun(f) => Fun(self.check(f, &ret)?),
            Postulate => Postulate,
            _ => unreachable!(),
        };

        let d = Def {
            loc: d.loc,
            name: d.name,
            tele,
            ret,
            body,
        };

        for n in checked {
            self.gamma.remove(&n);
        }

        Ok(d)
    }

    fn check(&mut self, e: Box<Expr>, ty: &Box<Term>) -> Result<Box<Term>, Error> {
        use Expr::*;

        Ok(match *e {
            Let(_, var, maybe_typ, a, b) => {
                let (tm, typ) = if let Some(t) = maybe_typ {
                    let checked_ty = self.check(t, &Box::new(Term::Univ))?;
                    (self.check(a, &checked_ty)?, checked_ty)
                } else {
                    self.infer(a)?
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
                match *pi {
                    Term::Pi(ty_param, ty_body) => {
                        let param = Param {
                            var: var.clone(),
                            info: Explicit,
                            typ: ty_param.typ,
                        };
                        let body_type = Normalizer::new(&mut self.sigma, loc)
                            .with(&[(&ty_param.var, &Box::new(Term::Ref(var)))], ty_body)?;
                        let checked_body = self.guarded_check(&[&param], body, &body_type)?;
                        Box::new(Term::Lam(param.clone(), checked_body))
                    }
                    _ => return Err(ExpectedPi(ty.clone(), loc)),
                }
            }
            Tuple(loc, a, b) => {
                let sig = Normalizer::new(&mut self.sigma, loc).term(ty.clone())?;
                match *sig {
                    Term::Sigma(ty_param, ty_body) => {
                        let a = self.check(a, &ty_param.typ)?;
                        let body_type = Normalizer::new(&mut self.sigma, loc)
                            .with(&[(&ty_param.var, &a)], ty_body)?;
                        let b = self.check(b, &body_type)?;
                        Box::new(Term::Tuple(a, b))
                    }
                    _ => return Err(ExpectedSigma(ty.clone(), loc)),
                }
            }
            TupleLet(loc, x, y, a, b) => {
                let (a, a_ty) = self.infer(a)?;
                let sig = Normalizer::new(&mut self.sigma, loc).term(a_ty)?;
                match *sig {
                    Term::Sigma(ty_param, ty_body) => {
                        let x = Param {
                            var: x,
                            info: Explicit,
                            typ: ty_param.typ,
                        };
                        let y = Param {
                            var: y,
                            info: Explicit,
                            typ: ty_body,
                        };
                        let b = self.guarded_check(&[&x, &y], b, ty)?;
                        Box::new(Term::TupleLet(x, y, a, b))
                    }
                    _ => return Err(ExpectedSigma(ty.clone(), loc)),
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
            Cast(loc, a) => {
                let b_ty = Normalizer::new(&mut self.sigma, loc).term(ty.clone())?;
                let (a, a_ty) = self.infer(a)?;
                match (&*a_ty, &*b_ty) {
                    (Term::Object(from), Term::Object(to)) => {
                        let o = Var::new("o");
                        let tele = vec![
                            Param {
                                var: o.clone(),
                                info: Explicit,
                                typ: Box::new(Term::Object(from.clone())),
                            },
                            Param {
                                var: Var::unbound(),
                                info: Implicit,
                                typ: Box::new(Term::RowOrd(to.clone(), Le, from.clone())),
                            },
                        ];
                        let f = Term::lam(
                            &tele,
                            Box::new(Term::Cast(Box::new(Term::Ref(o)), to.clone())),
                        );
                        Box::new(Term::App(f, a))
                    }
                    (Term::Object(_), _) => return Err(ExpectedObject(b_ty, loc)),
                    _ => return Err(ExpectedObject(a_ty, loc)),
                }
            }
            _ => {
                let loc = e.loc();
                let f_e = e.clone();
                let (mut inferred_tm, mut inferred_ty) = self.infer(e)?;
                if let Some(f_e) = Self::app_insert_holes(f_e, UnnamedExplicit, &*inferred_ty)? {
                    let (new_tm, new_ty) = self.infer(f_e)?;
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

    fn infer(&mut self, e: Box<Expr>) -> Result<(Box<Term>, Box<Term>), Error> {
        use Body::*;
        use Expr::*;
        Ok(match *e {
            Resolved(_, v) => {
                if let Some(ty) = self.gamma.get(&v) {
                    (Box::new(Term::Ref(v)), ty.clone())
                } else {
                    let d = self.sigma.get(&v).unwrap();
                    match &d.body {
                        Fun(f) => (
                            rename(Term::lam(&d.tele, f.clone())),
                            Term::pi(&d.tele, d.ret.clone()),
                        ),
                        Postulate => (Box::new(Term::Ref(v)), Term::pi(&d.tele, d.ret.clone())),
                        _ => unreachable!(),
                    }
                }
            }
            Hole(loc) => self.insert_meta(loc, true),
            InsertedHole(loc) => self.insert_meta(loc, false),
            Pi(_, p, b) => {
                let (param_ty, _) = self.infer(p.typ)?;
                let param = Param {
                    var: p.var,
                    info: p.info,
                    typ: param_ty,
                };
                let (b, b_ty) = self.guarded_infer(&[&param], b)?;
                (Box::new(Term::Pi(param, b)), b_ty)
            }
            App(_, f, i, x) => {
                let loc = f.loc();
                let f_e = f.clone();
                let (f, f_ty) = self.infer(f)?;
                if let Some(f_e) = Self::app_insert_holes(f_e, i.clone(), &*f_ty)? {
                    return self.infer(Box::new(App(loc, f_e, i, x)));
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
                let (param_ty, _) = self.infer(p.typ)?;
                let param = Param {
                    var: p.var,
                    info: p.info,
                    typ: param_ty,
                };
                let (b, b_ty) = self.guarded_infer(&[&param], b)?;
                (Box::new(Term::Sigma(param, b)), b_ty)
            }
            Tuple(_, a, b) => {
                let (a, a_ty) = self.infer(a)?;
                let (b, b_ty) = self.infer(b)?;
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
                    let (tm, _) = self.infer(Box::new(e))?;
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
                        let (tm, ty) = self.infer(Box::new(e))?;
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
                let (x, x_ty) = self.infer(a)?;
                let (y, y_ty) = self.infer(b)?;
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
    ) -> Result<(Box<Term>, Box<Term>), Error> {
        for &p in ps {
            self.gamma.insert(p.var.clone(), p.typ.clone());
        }
        let ret = self.infer(e)?;
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
        }
    }
}
