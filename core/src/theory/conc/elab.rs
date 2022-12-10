use std::collections::HashMap;

use crate::Error;
use crate::Error::{ExpectedObject, ExpectedPi, ExpectedSigma, NonUnifiable};
use crate::theory::{LocalVar, Param, Tele, VarGen};
use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Body, gamma_to_tele};
use crate::theory::abs::def::{Def, Gamma, Sigma};
use crate::theory::abs::normalize::Normalizer;
use crate::theory::abs::rename::rename;
use crate::theory::abs::unify::Unifier;
use crate::theory::conc::data::Expr;
use crate::theory::ParamInfo::Explicit;

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
        let mut checked: Vec<LocalVar> = Default::default();
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
            Meta(_) => todo!(),
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
                let pi = Normalizer::new(&mut self.sigma).term(ty.clone());
                match *pi {
                    Term::Pi(ty_param, ty_body) => {
                        let param = Param {
                            var: var.clone(),
                            info: Explicit,
                            typ: ty_param.typ,
                        };
                        let body_type = Normalizer::new(&mut self.sigma)
                            .with(&[(&ty_param.var, &Box::new(Term::Ref(var)))], ty_body);
                        let checked_body = self.guarded_check(&[&param], body, &body_type)?;
                        Box::new(Term::Lam(param.clone(), checked_body))
                    }
                    _ => return Err(ExpectedPi(ty.clone(), loc)),
                }
            }
            Tuple(loc, a, b) => {
                let sig = Normalizer::new(&mut self.sigma).term(ty.clone());
                match *sig {
                    Term::Sigma(ty_param, ty_body) => {
                        let a = self.check(a, &ty_param.typ)?;
                        let body_type =
                            Normalizer::new(&mut self.sigma).with(&[(&ty_param.var, &a)], ty_body);
                        let b = self.check(b, &body_type)?;
                        Box::new(Term::Tuple(a, b))
                    }
                    _ => return Err(ExpectedSigma(ty.clone(), loc)),
                }
            }
            TupleLet(loc, x, y, a, b) => {
                let (a, a_ty) = self.infer(a)?;
                let sig = Normalizer::new(&mut self.sigma).term(a_ty);
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
            Obj(loc, fields) => {
                let object = Normalizer::new(&mut self.sigma).term(ty.clone());
                match *object {
                    Term::Object(row) => {
                        todo!()
                    }
                    _ => return Err(ExpectedObject(ty.clone(), loc))
                }
            }
            _ => {
                let loc = e.loc();
                let (inferred_tm, inferred_ty) = self.infer(e)?;
                let inferred = Normalizer::new(&mut self.sigma).term(inferred_ty);
                let expected = Normalizer::new(&mut self.sigma).term(ty.clone());
                let mut u = Unifier::new(&mut self.sigma);
                if !u.unify(&expected, &inferred) {
                    return Err(NonUnifiable(expected, inferred, loc));
                }
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
            Hole(loc) => {
                let ty_meta_var = self.ig.fresh();
                self.sigma.insert(
                    ty_meta_var.clone(),
                    Def {
                        loc,
                        name: ty_meta_var.clone(),
                        tele: Default::default(),
                        ret: Box::new(Term::Univ),
                        body: Meta(None),
                    },
                );
                let ty = Box::new(Term::MetaRef(ty_meta_var, Default::default()));

                let tm_meta_var = self.ug.fresh();
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
            App(_, f, x) => {
                let f_loc = f.loc();
                let (f, f_ty) = self.infer(f)?;
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
                        let applied = Normalizer::new(&mut self.sigma).apply(f, &[&x]);
                        let applied_ty = Normalizer::new(&mut self.sigma).with(&[(&p.var, &x)], b);
                        (applied, applied_ty)
                    }
                    _ => return Err(ExpectedPi(f, f_loc)),
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
                            var: LocalVar::unbound(),
                            info: Explicit,
                            typ: a_ty,
                        },
                        b_ty,
                    )),
                )
            }
            Fields(_, fields) => {
                let mut inferred = HashMap::default();
                for (f, e) in fields {
                    let typ = self.check(Box::new(e), &Box::new(Term::Univ))?;
                    inferred.insert(f, *typ);
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

            e => {
                dbg!(&e);
                unreachable!()
            }
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
