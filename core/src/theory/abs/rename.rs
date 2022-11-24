use std::collections::HashMap;

use crate::theory::abs::data::Term;
use crate::theory::{LocalVar, Param};

pub struct Renamer(HashMap<LocalVar, LocalVar>);

impl Default for Renamer {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl Renamer {
    pub fn term(&mut self, tm: Box<Term>) -> Box<Term> {
        use Term::*;
        Box::new(match *tm {
            Ref(x) => self.0.get(&x).map_or(Ref(x), |y| Ref(y.to_owned())),
            Let(p, a, b) => {
                let a = self.term(a); // not guarded by `p`, rename it first
                Let(self.param(p), a, self.term(b))
            }
            Pi(p, c) => Pi(self.param(p), self.term(c)),
            Lam(p, b) => Lam(self.param(p), self.term(b)),
            App(f, x) => App(self.term(f), self.term(x)),
            Sigma(p, c) => Sigma(self.param(p), self.term(c)),
            Tuple(a, b) => Tuple(self.term(a), self.term(b)),
            TupleLet(x, y, a, b) => {
                TupleLet(self.param(x), self.param(y), self.term(a), self.term(b))
            }
            UnitLet(a, b) => UnitLet(self.term(a), self.term(b)),
            If(p, t, e) => If(self.term(p), self.term(t), self.term(e)),

            Univ => Univ,
            Unit => Unit,
            TT => TT,
            Boolean => Boolean,
            False => False,
            True => True,
            String => String,
            Str(v) => Str(v),
            Number => Number,
            Num(r, v) => Num(r, v),
            BigInt => BigInt,
            Big(v) => Big(v),

            _ => unreachable!(),
        })
    }

    fn param(&mut self, p: Param<Term>) -> Param<Term> {
        let var = LocalVar::new(p.var.name.as_str());
        self.0.insert(p.var, var.to_owned());
        Param {
            var,
            typ: self.term(p.typ),
        }
    }
}

pub fn rename(tm: Box<Term>) -> Box<Term> {
    Renamer::default().term(tm)
}
