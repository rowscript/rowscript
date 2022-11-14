use std::collections::HashMap;

use crate::theory::abs::data::{Term, U};
use crate::theory::abs::def::Body::Fun;
use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::theory::conc::data::Expr::{
    Big, BigInt, Boolean, False, If, Num, Number, Str, String, True, Unit, Univ, TT,
};
use crate::theory::{LocalVar, Param};
use crate::Error;

type Sigma = HashMap<LocalVar, Def<Term>>;
type Gamma = HashMap<LocalVar, Box<Term>>;
type Rho = HashMap<LocalVar, Box<Term>>;

pub struct Elaborator {
    sigma: Sigma,
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

            let gamma_typ = self.check(p.typ, Box::new(Term::Univ))?;
            let typ = gamma_typ.to_owned();

            self.gamma.insert(gamma_var, gamma_typ);
            checked.push(checked_var);
            tele.push(Param { var, typ })
        }

        let ret = self.check(d.ret, Box::new(Term::Univ))?;
        let body = match d.body {
            Fun(f) => Fun(self.check(f, ret.to_owned())?),
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

    fn check(&mut self, e: Box<Expr>, ty: Box<Term>) -> Result<Box<Term>, Error> {
        Ok(match *e {
            If(_, p, t, e) => {
                let else_ty = ty.to_owned();
                Box::new(Term::If(
                    self.check(p, Box::new(Term::Boolean))?,
                    self.check(t, ty)?,
                    self.check(e, else_ty)?,
                ))
            }
            _ => {
                let (tm, inferred_ty) = self.infer(e)?;
                // TODO: Unification.
                tm
            }
        })
    }

    fn infer(&mut self, e: Box<Expr>) -> Result<(Box<Term>, Box<Term>), Error> {
        Ok(match *e {
            Univ(_) => (Box::new(U), Box::new(Term::Univ)),
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
}
