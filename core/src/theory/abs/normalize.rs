use crate::theory::abs::data::Term;
use crate::theory::abs::data::Term::{
    App, Big, BigInt, Boolean, False, If, Lam, Let, Num, Number, Pi, Ref, Sigma, Str, String, True,
    Tuple, TupleLet, Unit, UnitLet, Univ, TT,
};
use crate::theory::abs::def::{Rho, Sigma as Sig};
use crate::theory::abs::rename::Renamer;
use crate::theory::conc::elab::Elaborator;
use crate::theory::{LocalVar, Param};

pub struct Normalizer<'a> {
    sigma: &'a Sig,
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
            Pi(p, b) => Box::new(Pi(self.param(p), self.term(b))),
            Lam(p, b) => Box::new(Lam(self.param(p), self.term(b))),
            App(f, x) => {
                let f = self.term(f);
                let x = self.term(x);
                if let Lam(p, b) = *f {
                    self.rho.insert(p.var, x);
                    self.term(b)
                } else {
                    Box::new(App(f, x))
                }
            }
            Sigma(p, b) => Box::new(Sigma(self.param(p), self.term(b))),
            Tuple(a, b) => Box::new(Tuple(self.term(a), self.term(b))),
            TupleLet(p, q, a, b) => {
                let a = self.term(a);
                if let Tuple(x, y) = *a {
                    self.rho.insert(p.var, x);
                    self.rho.insert(q.var, y);
                    self.term(b)
                } else {
                    Box::new(TupleLet(p, q, a, b))
                }
            }
            UnitLet(a, b) => {
                let a = self.term(a);
                if let TT = *a {
                    self.term(b)
                } else {
                    Box::new(UnitLet(a, b))
                }
            }
            If(p, t, e) => {
                let p = self.term(p);
                match *p {
                    True => self.term(t),
                    False => self.term(e),
                    _ => unreachable!(),
                }
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

    fn param(&mut self, p: Param<Term>) -> Param<Term> {
        Param {
            var: p.var,
            typ: self.term(p.typ),
        }
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
