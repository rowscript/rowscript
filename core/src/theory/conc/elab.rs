use crate::theory::abs::data::Term;
use crate::theory::abs::def::Body::Fun;
use crate::theory::abs::def::{Def, Gamma, Sigma};
use crate::theory::abs::normalize::Normalizer;
use crate::theory::abs::rename::rename;
use crate::theory::conc::data::Expr;
use crate::theory::conc::data::Expr::{
    Big, BigInt, Boolean, False, If, Lam, Let, Num, Number, Resolved, Str, String, True, Unit,
    Univ, TT,
};
use crate::theory::{LocalVar, Param};
use crate::Error;
use crate::Error::ExpectedPi;

pub struct Elaborator {
    pub sigma: Sigma,
    gamma: Gamma,
}

impl Elaborator {
    pub fn def(&mut self, d: Def<Expr>) -> Result<Def<Term>, Error> {
        let mut checked: Vec<LocalVar> = Default::default();
        let mut tele: Vec<Param<Term>> = Default::default();
        for p in d.tele {
            let gamma_var = p.var.to_owned();
            let checked_var = p.var.to_owned();
            let var = p.var.to_owned();

            let gamma_typ = self.check(p.typ, &Box::new(Term::Univ))?;
            let typ = gamma_typ.to_owned();

            self.gamma.insert(gamma_var, gamma_typ);
            checked.push(checked_var);
            tele.push(Param { var, typ })
        }

        let ret = self.check(d.ret, &Box::new(Term::Univ))?;
        let body = match d.body {
            Fun(f) => Fun(self.check(f, &ret)?),
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
        Ok(match *e {
            Let(_, var, maybe_typ, a, b) => {
                let (tm, typ) = if let Some(t) = maybe_typ {
                    let checked_ty = self.check(t, &Box::new(Term::Univ))?;
                    (self.check(a, &checked_ty)?, checked_ty)
                } else {
                    self.infer(a)?
                };
                let param = Param { var, typ };
                let body = self.guarded_check(&[&param], b, ty)?;
                Box::new(Term::Let(param, tm, body))
            }
            Lam(loc, var, body) => {
                let pi = Normalizer::from(self as &_).term(ty);
                match *pi {
                    Term::Pi(ty_param, ty_body) => {
                        let param = Param {
                            var: var.clone(),
                            typ: ty_param.typ,
                        };
                        let body_type = Normalizer::from(self as &_).with(
                            &ty_body,
                            &[(ty_param.var, Box::new(Term::Ref(var.clone())))],
                        );
                        let checked_body = self.guarded_check(&[&param], body, &body_type)?;
                        Box::new(Term::Lam(param, checked_body))
                    }
                    _ => return Err(ExpectedPi(loc, ty.clone())),
                }
            }
            If(_, p, t, e) => Box::new(Term::If(
                self.check(p, &Box::new(Term::Boolean))?,
                self.check(t, ty)?,
                self.check(e, ty)?,
            )),
            _ => {
                let (tm, inferred_ty) = self.infer(e)?;
                // TODO: Unification.
                tm
            }
        })
    }

    fn infer(&mut self, e: Box<Expr>) -> Result<(Box<Term>, Box<Term>), Error> {
        Ok(match *e {
            Resolved(_, v) => {
                if let Some(ty) = self.gamma.get(&v) {
                    (Box::new(Term::Ref(v)), ty.to_owned())
                } else {
                    let d = self.sigma.get(&v).unwrap();
                    match &d.body {
                        Fun(f) => (
                            rename(Term::new_lam(&d.tele, f.to_owned())),
                            Term::new_pi(&d.tele, d.ret.to_owned()),
                        ),
                    }
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
            Num(_, v) => (Box::new(Term::Num(v)), Box::new(Term::Number)),
            BigInt(_) => (Box::new(Term::BigInt), Box::new(Term::Univ)),
            Big(_, v) => (Box::new(Term::Big(v)), Box::new(Term::BigInt)),

            _ => unreachable!(),
        })
    }

    fn guarded_check(
        &mut self,
        ps: &[&Param<Term>],
        e: Box<Expr>,
        ty: &Box<Term>,
    ) -> Result<Box<Term>, Error> {
        for p in ps {
            let var = p.var.to_owned();
            let typ = p.typ.to_owned();
            self.gamma.insert(var, typ);
        }
        let checked = self.check(e, ty)?;
        for p in ps {
            self.gamma.remove(&p.var);
        }
        Ok(checked)
    }
}

impl Default for Elaborator {
    fn default() -> Self {
        Self {
            sigma: Default::default(),
            gamma: Default::default(),
        }
    }
}
