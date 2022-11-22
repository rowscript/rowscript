use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Rho, Sigma};
use crate::theory::conc::elab::Elaborator;
use crate::theory::LocalVar;

pub struct Normalizer<'a> {
    sigma: &'a Sigma,
    rho: Rho,
}

impl<'a> Normalizer<'a> {
    pub fn term(&mut self, tm: &Box<Term>) -> Box<Term> {
        todo!()
    }

    pub fn with(&mut self, tm: &Box<Term>, rho: &[(LocalVar, Box<Term>)]) -> Box<Term> {
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
