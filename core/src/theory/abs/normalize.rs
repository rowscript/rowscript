use crate::theory::abs::data::Term;
use crate::theory::abs::data::Term::{
    Big, BigInt, Boolean, False, Let, Num, Number, Ref, Str, String, True, Unit, Univ, TT,
};
use crate::theory::abs::def::{Rho, Sigma};
use crate::theory::abs::rename::Renamer;
use crate::theory::conc::elab::Elaborator;
use crate::theory::LocalVar;

pub struct Normalizer<'a> {
    sigma: &'a Sigma,
    rho: Rho,
}

impl<'a> Normalizer<'a> {
    pub fn term(&mut self, tm: Box<Term>) -> Box<Term> {
        match *tm {
            Ref(ref x) => {
                if let Some(y) = self.rho.get(&x) {
                    self.term(Renamer::default().term(y.clone()))
                } else {
                    tm.clone()
                }
            }
            Let(p, a, b) => {
                let a = self.term(a);
                self.with(b, &[(p.var, a)])
            }

            Univ => Box::new(Univ),
            Unit => Box::new(Unit),
            TT => Box::new(TT),
            Boolean => Box::new(Boolean),
            False => Box::new(False),
            True => Box::new(True),
            String => Box::new(String),
            Str(v) => Box::new(Str(v)),
            Number => Box::new(Number),
            Num(v) => Box::new(Num(v)),
            BigInt => Box::new(BigInt),
            Big(v) => Box::new(Big(v)),

            _ => unreachable!(),
        }
    }

    pub fn with(&mut self, tm: Box<Term>, rho: &[(LocalVar, Box<Term>)]) -> Box<Term> {
        for (x, v) in rho {
            self.rho.insert(x.clone(), v.clone());
        }
        self.term(tm)
    }
}

impl<'a> From<&'a Elaborator> for Normalizer<'a> {
    fn from(e: &'a Elaborator) -> Self {
        Self {
            sigma: &e.sigma,
            rho: Default::default(),
        }
    }
}
