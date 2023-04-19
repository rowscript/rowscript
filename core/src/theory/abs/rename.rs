use std::collections::HashMap;

use crate::theory::abs::data::{CaseMap, FieldMap, Term};
use crate::theory::{Param, Var};

#[derive(Default)]
pub struct Renamer(HashMap<Var, Var>);

impl Renamer {
    pub fn term(&mut self, tm: Term) -> Term {
        use Term::*;
        match tm {
            Ref(x) => self.0.get(&x).map_or(Ref(x), |y| Ref(y.clone())),
            MetaRef(k, r, sp) => MetaRef(
                k,
                r,
                sp.into_iter().map(|(i, tm)| (i, self.term(tm))).collect(),
            ),
            Let(p, a, b) => {
                let a = self.term(*a); // not guarded by `p`, rename it first
                Let(self.param(p), Box::new(a), Box::new(self.term(*b)))
            }
            Pi(p, c) => Pi(self.param(p), Box::new(self.term(*c))),
            Lam(p, b) => Lam(self.param(p), Box::new(self.term(*b))),
            App(f, i, x) => App(Box::new(self.term(*f)), i, Box::new(self.term(*x))),
            Sigma(p, c) => Sigma(self.param(p), Box::new(self.term(*c))),
            Tuple(a, b) => Tuple(Box::new(self.term(*a)), Box::new(self.term(*b))),
            TupleLet(x, y, a, b) => TupleLet(
                self.param(x),
                self.param(y),
                Box::new(self.term(*a)),
                Box::new(self.term(*b)),
            ),
            UnitLet(a, b) => UnitLet(Box::new(self.term(*a)), Box::new(self.term(*b))),
            If(p, t, e) => If(
                Box::new(self.term(*p)),
                Box::new(self.term(*t)),
                Box::new(self.term(*e)),
            ),
            Fields(fields) => {
                let mut m = FieldMap::default();
                for (f, tm) in fields {
                    m.insert(f, self.term(tm));
                }
                Fields(m)
            }
            Combine(a, b) => Combine(Box::new(self.term(*a)), Box::new(self.term(*b))),
            RowOrd(a, d, b) => RowOrd(Box::new(self.term(*a)), d, Box::new(self.term(*b))),
            RowEq(a, b) => RowEq(Box::new(self.term(*a)), Box::new(self.term(*b))),
            Object(f) => Object(Box::new(self.term(*f))),
            Obj(f) => Obj(Box::new(self.term(*f))),
            Concat(a, b) => Concat(Box::new(self.term(*a)), Box::new(self.term(*b))),
            Access(a, n) => Access(Box::new(self.term(*a)), n),
            Downcast(a, f) => Downcast(Box::new(self.term(*a)), Box::new(self.term(*f))),
            Enum(f) => Enum(Box::new(self.term(*f))),
            Variant(f) => Variant(Box::new(self.term(*f))),
            Upcast(a, f) => Upcast(Box::new(self.term(*a)), Box::new(self.term(*f))),
            Switch(a, cs) => {
                let a = self.term(*a);
                let mut m = CaseMap::default();
                for (n, (v, tm)) in cs {
                    m.insert(n, (v, self.term(tm)));
                }
                Switch(Box::new(a), m)
            }
            Vptr(r, ts) => Vptr(r, ts.into_iter().map(|t| self.term(t)).collect()),
            Vp(r, ts) => Vp(r, ts.into_iter().map(|t| self.term(t)).collect()),
            Lookup(a) => Lookup(Box::new(self.term(*a))),
            Find(ty, i, f) => Find(Box::new(self.term(*ty)), i, f),
            ImplementsOf(a, i) => ImplementsOf(Box::new(self.term(*a)), i),

            tm => tm,
        }
    }

    fn param(&mut self, p: Param<Term>) -> Param<Term> {
        let var = Var::new(p.var.name.as_str());
        self.0.insert(p.var, var.clone());
        Param {
            var,
            info: p.info,
            typ: Box::new(self.term(*p.typ)),
        }
    }
}

pub fn rename(tm: Term) -> Term {
    Renamer::default().term(tm)
}
