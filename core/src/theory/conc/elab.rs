use std::collections::HashMap;

use crate::theory::abs::data::{Term, U};
use crate::theory::abs::def::Body::Fun;
use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
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

            let gamma_typ = self.check(p.typ, Box::new(U))?;
            let typ = gamma_typ.to_owned();

            self.gamma.insert(gamma_var, gamma_typ);
            checked.push(checked_var);
            tele.push(Param { var, typ })
        }

        let ret = self.check(d.ret, Box::new(U))?;
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
        todo!()
    }
}
