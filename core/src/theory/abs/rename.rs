use std::collections::HashMap;

use crate::theory::abs::data::{CaseMap, FieldMap, Term};
use crate::theory::{Param, Var};

#[derive(Default)]
pub struct Renamer(HashMap<Var, Var>);

impl Renamer {
    pub fn term(&mut self, tm: Box<Term>) -> Box<Term> {
        use Term::*;
        Box::new(match *tm {
            Ref(x) => self.0.get(&x).map_or(Ref(x), |y| Ref(y.clone())),
            MetaRef(r, sp) => MetaRef(
                r,
                sp.into_iter()
                    .map(|(i, tm)| (i, *self.term(Box::new(tm))))
                    .collect(),
            ),
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
            Fields(fields) => {
                let mut m = FieldMap::default();
                for (f, tm) in fields {
                    m.insert(f, *self.term(Box::new(tm)));
                }
                Fields(m)
            }
            Combine(a, b) => Combine(self.term(a), self.term(b)),
            RowOrd(a, d, b) => RowOrd(self.term(a), d, self.term(b)),
            RowEq(a, b) => RowEq(self.term(a), self.term(b)),
            Object(f) => Object(self.term(f)),
            Obj(f) => Obj(self.term(f)),
            Concat(a, b) => Concat(self.term(a), self.term(b)),
            Access(a, n) => Access(self.term(a), n),
            Downcast(a, f) => Downcast(self.term(a), self.term(f)),
            Enum(f) => Enum(self.term(f)),
            Variant(f) => Variant(self.term(f)),
            Upcast(a, f) => Upcast(self.term(a), self.term(f)),
            Switch(a, cs) => {
                let a = self.term(a);
                let mut m = CaseMap::default();
                for (n, (v, tm)) in cs {
                    m.insert(n, (v, *self.term(Box::new(tm))));
                }
                Switch(a, m)
            }

            Undef(x) => Undef(x),
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
            Row => Row,
            RowSat => RowSat,
            RowRefl => RowRefl,
            Vptr(r) => Vptr(r),
            InterfaceRef(r) => InterfaceRef(r),
        })
    }

    fn param(&mut self, p: Param<Term>) -> Param<Term> {
        let var = Var::new(p.var.name.as_str());
        self.0.insert(p.var, var.clone());
        Param {
            var,
            info: p.info,
            typ: self.term(p.typ),
        }
    }
}

pub fn rename(tm: Box<Term>) -> Box<Term> {
    Renamer::default().term(tm)
}
