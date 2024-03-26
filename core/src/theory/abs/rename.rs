use std::collections::HashMap;

use crate::maybe_grow;
use crate::theory::abs::data::{CaseMap, FieldMap, Term};
use crate::theory::{Param, Var};

#[derive(Default)]
struct Renamer(HashMap<Var, Var>);

impl Renamer {
    pub fn term(&mut self, tm: Term) -> Term {
        maybe_grow(move || self.term_impl(tm))
    }

    fn term_impl(&mut self, tm: Term) -> Term {
        use Term::*;
        match tm {
            Ref(x) => self.0.get(&x).map_or(Ref(x), |y| Ref(y.clone())),
            MetaRef(k, r, sp) => MetaRef(
                k,
                r,
                sp.into_iter().map(|(i, tm)| (i, self.term(tm))).collect(),
            ),
            Local(p, a, b) => {
                let a = self.term(*a); // not guarded by `p`, rename it first
                Local(self.param(p), Box::new(a), Box::new(self.term(*b)))
            }
            LocalSet(p, a, b) => {
                let a = self.term(*a);
                LocalSet(self.param(p), Box::new(a), Box::new(self.term(*b)))
            }
            LocalUpdate(v, a, b) => {
                LocalUpdate(v, Box::new(self.term(*a)), Box::new(self.term(*b)))
            }
            While(p, b, r) => While(
                Box::new(self.term(*p)),
                Box::new(self.term(*b)),
                Box::new(self.term(*r)),
            ),
            Fori(b, r) => Fori(Box::new(self.term(*b)), Box::new(self.term(*r))),
            Guard(p, b, r) => Guard(
                Box::new(self.term(*p)),
                Box::new(self.term(*b)),
                Box::new(self.term(*r)),
            ),
            Return(a) => Return(Box::new(self.term(*a))),
            Pi(p, c) => Pi(self.param(p), Box::new(self.term(*c))),
            Lam(p, b) => Lam(self.param(p), Box::new(self.term(*b))),
            App(f, i, x) => App(Box::new(self.term(*f)), i, Box::new(self.term(*x))),
            Sigma(p, c) => Sigma(self.param(p), Box::new(self.term(*c))),
            Tuple(a, b) => Tuple(Box::new(self.term(*a)), Box::new(self.term(*b))),
            TupleLocal(x, y, a, b) => TupleLocal(
                self.param(x),
                self.param(y),
                Box::new(self.term(*a)),
                Box::new(self.term(*b)),
            ),
            UnitLocal(a, b) => UnitLocal(Box::new(self.term(*a)), Box::new(self.term(*b))),
            If(p, t, e) => If(
                Box::new(self.term(*p)),
                Box::new(self.term(*t)),
                Box::new(self.term(*e)),
            ),
            BoolOr(a, b) => BoolOr(Box::new(self.term(*a)), Box::new(self.term(*b))),
            BoolAnd(a, b) => BoolAnd(Box::new(self.term(*a)), Box::new(self.term(*b))),
            BoolNot(a) => BoolNot(Box::new(self.term(*a))),
            BoolEq(a, b) => BoolEq(Box::new(self.term(*a)), Box::new(self.term(*b))),
            BoolNeq(a, b) => BoolNeq(Box::new(self.term(*a)), Box::new(self.term(*b))),
            StrAdd(a, b) => StrAdd(Box::new(self.term(*a)), Box::new(self.term(*b))),
            StrEq(a, b) => StrEq(Box::new(self.term(*a)), Box::new(self.term(*b))),
            StrNeq(a, b) => StrNeq(Box::new(self.term(*a)), Box::new(self.term(*b))),
            NumAdd(a, b) => NumAdd(Box::new(self.term(*a)), Box::new(self.term(*b))),
            NumSub(a, b) => NumSub(Box::new(self.term(*a)), Box::new(self.term(*b))),
            NumMul(a, b) => NumMul(Box::new(self.term(*a)), Box::new(self.term(*b))),
            NumDiv(a, b) => NumDiv(Box::new(self.term(*a)), Box::new(self.term(*b))),
            NumMod(a, b) => NumMod(Box::new(self.term(*a)), Box::new(self.term(*b))),
            NumEq(a, b) => NumEq(Box::new(self.term(*a)), Box::new(self.term(*b))),
            NumNeq(a, b) => NumNeq(Box::new(self.term(*a)), Box::new(self.term(*b))),
            NumLe(a, b) => NumLe(Box::new(self.term(*a)), Box::new(self.term(*b))),
            NumGe(a, b) => NumGe(Box::new(self.term(*a)), Box::new(self.term(*b))),
            NumLt(a, b) => NumLt(Box::new(self.term(*a)), Box::new(self.term(*b))),
            NumGt(a, b) => NumGt(Box::new(self.term(*a)), Box::new(self.term(*b))),
            NumNeg(a) => NumNeg(Box::new(self.term(*a))),
            ArrayIterator(t) => ArrayIterator(Box::new(self.term(*t))),
            ArrIterNext(it) => ArrIterNext(Box::new(self.term(*it))),
            Array(t) => Array(Box::new(self.term(*t))),
            Arr(xs) => Arr(xs.into_iter().map(|x| self.term(x)).collect()),
            ArrLength(a) => ArrLength(Box::new(self.term(*a))),
            ArrPush(a, v) => ArrPush(Box::new(self.term(*a)), Box::new(self.term(*v))),
            ArrForeach(a, f) => ArrForeach(Box::new(self.term(*a)), Box::new(self.term(*f))),
            ArrAt(a, i) => ArrAt(Box::new(self.term(*a)), Box::new(self.term(*i))),
            ArrInsert(a, i, v) => ArrInsert(
                Box::new(self.term(*a)),
                Box::new(self.term(*i)),
                Box::new(self.term(*v)),
            ),
            ArrIter(a) => ArrIter(Box::new(self.term(*a))),
            MapIterator(t) => MapIterator(Box::new(self.term(*t))),
            MapIterNext(it) => MapIterNext(Box::new(self.term(*it))),
            Map(k, v) => Map(Box::new(self.term(*k)), Box::new(self.term(*v))),
            Kv(xs) => Kv(xs
                .into_iter()
                .map(|(k, v)| (self.term(k), self.term(v)))
                .collect()),
            MapHas(m, k) => MapHas(Box::new(self.term(*m)), Box::new(self.term(*k))),
            MapGet(m, k) => MapGet(Box::new(self.term(*m)), Box::new(self.term(*k))),
            MapSet(m, k, v) => MapSet(
                Box::new(self.term(*m)),
                Box::new(self.term(*k)),
                Box::new(self.term(*v)),
            ),
            MapDelete(m, k) => MapDelete(Box::new(self.term(*m)), Box::new(self.term(*k))),
            MapClear(m) => MapClear(Box::new(self.term(*m))),
            MapIter(a) => MapIter(Box::new(self.term(*a))),
            Fields(fields) => {
                let mut m = FieldMap::default();
                for (f, tm) in fields {
                    m.insert(f, self.term(tm));
                }
                Fields(m)
            }
            Associate(a, n) => Associate(Box::new(self.term(*a)), n),
            Combine(i, a, b) => Combine(i, Box::new(self.term(*a)), Box::new(self.term(*b))),
            RowOrd(a, b) => RowOrd(Box::new(self.term(*a)), Box::new(self.term(*b))),
            RowEq(a, b) => RowEq(Box::new(self.term(*a)), Box::new(self.term(*b))),
            Object(f) => Object(Box::new(self.term(*f))),
            Obj(f) => Obj(Box::new(self.term(*f))),
            Concat(a, b) => Concat(Box::new(self.term(*a)), Box::new(self.term(*b))),
            Access(a, n) => Access(Box::new(self.term(*a)), n),
            Downcast(a, m) => Downcast(Box::new(self.term(*a)), Box::new(self.term(*m))),
            Down(r, to) => Down(Box::new(self.term(*r)), Box::new(self.term(*to))),
            Enum(f) => Enum(Box::new(self.term(*f))),
            Variant(f) => Variant(Box::new(self.term(*f))),
            Upcast(a) => Upcast(Box::new(self.term(*a))),
            Up(r, from, to) => Up(
                Box::new(self.term(*r)),
                Box::new(self.term(*from)),
                Box::new(self.term(*to)),
            ),
            Switch(a, cs, d) => {
                let a = self.term(*a);
                let mut m = CaseMap::default();
                for (n, (v, tm)) in cs {
                    m.insert(n, (v, self.term(tm)));
                }
                Switch(
                    Box::new(a),
                    m,
                    d.map(|(v, tm)| (v, Box::new(self.term(*tm)))),
                )
            }
            Unionify(a) => Unionify(Box::new(self.term(*a))),
            Find(ty, i, f) => Find(Box::new(self.term(*ty)), i, f),
            ImplementsOf(a, i) => ImplementsOf(Box::new(self.term(*a)), i),
            Reflected(a) => Reflected(Box::new(self.term(*a))),
            Cls {
                class,
                type_args: t,
                associated: a,
                object,
            } => Cls {
                class,
                type_args: t.into_iter().map(|ty| self.term(ty)).collect(),
                associated: a.into_iter().map(|(n, ty)| (n, self.term(ty))).collect(),
                object: Box::new(self.term(*object)),
            },
            ErrorThrow(a) => ErrorThrow(Box::new(self.term(*a))),
            ConsoleLog(m) => ConsoleLog(Box::new(self.term(*m))),
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
