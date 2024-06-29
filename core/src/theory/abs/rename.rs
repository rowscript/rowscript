use std::collections::HashMap;

use crate::theory::abs::data::{CaseMap, FieldMap, Term};
use crate::theory::{Param, Var};

#[derive(Default)]
struct Renamer(HashMap<Var, Var>);

impl Renamer {
    fn term(&mut self, #[allow(clippy::boxed_local)] tm: Box<Term>) -> Box<Term> {
        use Term::*;
        Box::new(match *tm {
            Ref(x) => self.0.get(&x).map_or(Ref(x), |y| Ref(y.clone())),
            MetaRef(k, r, sp) => MetaRef(
                k,
                r,
                sp.into_iter()
                    .map(|(i, tm)| (i, *self.term(Box::new(tm))))
                    .collect(),
            ),
            Const(p, a, b) => {
                let a = self.term(a); // not guarded by `p`, rename it first
                Const(self.param(p), a, self.term(b))
            }
            Let(p, a, b) => {
                let a = self.term(a);
                Let(self.param(p), a, self.term(b))
            }
            Update(v, a, b) => Update(v, self.term(a), self.term(b)),
            While(p, b, r) => While(self.term(p), self.term(b), self.term(r)),
            Fori(b, r) => Fori(self.term(b), self.term(r)),
            Guard(p, b, e, r) => Guard(
                self.term(p),
                self.term(b),
                e.map(|e| self.term(e)),
                self.term(r),
            ),
            Return(a) => Return(self.term(a)),
            Pi { param, eff, body } => Pi {
                param: self.param(param),
                eff: self.term(eff),
                body: self.term(body),
            },
            Lam(p, b) => Lam(self.param(p), self.term(b)),
            App(f, i, x) => App(self.term(f), i, self.term(x)),
            Sigma(p, c) => Sigma(self.param(p), self.term(c)),
            Tuple(a, b) => Tuple(self.term(a), self.term(b)),
            TupleBind(x, y, a, b) => {
                let a = self.term(a);
                TupleBind(self.param(x), self.param(y), a, self.term(b))
            }
            UnitBind(a, b) => UnitBind(self.term(a), self.term(b)),
            If(p, t, e) => If(self.term(p), self.term(t), self.term(e)),
            BoolOr(a, b) => BoolOr(self.term(a), self.term(b)),
            BoolAnd(a, b) => BoolAnd(self.term(a), self.term(b)),
            BoolNot(a) => BoolNot(self.term(a)),
            BoolEq(a, b) => BoolEq(self.term(a), self.term(b)),
            BoolNeq(a, b) => BoolNeq(self.term(a), self.term(b)),
            StrAdd(a, b) => StrAdd(self.term(a), self.term(b)),
            StrEq(a, b) => StrEq(self.term(a), self.term(b)),
            StrNeq(a, b) => StrNeq(self.term(a), self.term(b)),
            NumAdd(a, b) => NumAdd(self.term(a), self.term(b)),
            NumSub(a, b) => NumSub(self.term(a), self.term(b)),
            NumMul(a, b) => NumMul(self.term(a), self.term(b)),
            NumDiv(a, b) => NumDiv(self.term(a), self.term(b)),
            NumMod(a, b) => NumMod(self.term(a), self.term(b)),
            NumEq(a, b) => NumEq(self.term(a), self.term(b)),
            NumNeq(a, b) => NumNeq(self.term(a), self.term(b)),
            NumLe(a, b) => NumLe(self.term(a), self.term(b)),
            NumGe(a, b) => NumGe(self.term(a), self.term(b)),
            NumLt(a, b) => NumLt(self.term(a), self.term(b)),
            NumGt(a, b) => NumGt(self.term(a), self.term(b)),
            NumNeg(a) => NumNeg(self.term(a)),
            NumToStr(a) => NumToStr(self.term(a)),
            BigintToStr(a) => BigintToStr(self.term(a)),
            ArrayIterator(t) => ArrayIterator(self.term(t)),
            ArrIterNext(it) => ArrIterNext(self.term(it)),
            Array(t) => Array(self.term(t)),
            Arr(xs) => Arr(xs.into_iter().map(|x| *self.term(Box::new(x))).collect()),
            ArrLength(a) => ArrLength(self.term(a)),
            ArrPush(a, v) => ArrPush(self.term(a), self.term(v)),
            ArrForeach(a, f) => ArrForeach(self.term(a), self.term(f)),
            ArrAt(a, i) => ArrAt(self.term(a), self.term(i)),
            ArrInsert(a, i, v) => ArrInsert(self.term(a), self.term(i), self.term(v)),
            ArrIter(a) => ArrIter(self.term(a)),
            MapIterator(t) => MapIterator(self.term(t)),
            MapIterNext(it) => MapIterNext(self.term(it)),
            Map(k, v) => Map(self.term(k), self.term(v)),
            Kv(xs) => Kv(xs
                .into_iter()
                .map(|(k, v)| (*self.term(Box::new(k)), *self.term(Box::new(v))))
                .collect()),
            MapHas(m, k) => MapHas(self.term(m), self.term(k)),
            MapGet(m, k) => MapGet(self.term(m), self.term(k)),
            MapSet(m, k, v) => MapSet(self.term(m), self.term(k), self.term(v)),
            MapDelete(m, k) => MapDelete(self.term(m), self.term(k)),
            MapClear(m) => MapClear(self.term(m)),
            MapIter(a) => MapIter(self.term(a)),
            Fields(fields) => {
                let mut m = FieldMap::default();
                for (f, tm) in fields {
                    m.insert(f, *self.term(Box::new(tm)));
                }
                Fields(m)
            }
            Associate(a, n) => Associate(self.term(a), n),
            Combine(i, a, b) => Combine(i, self.term(a), self.term(b)),
            RowOrd(a, b) => RowOrd(self.term(a), self.term(b)),
            RowEq(a, b) => RowEq(self.term(a), self.term(b)),
            Object(f) => Object(self.term(f)),
            Obj(f) => Obj(self.term(f)),
            Concat(a, b) => Concat(self.term(a), self.term(b)),
            Access(a, n) => Access(self.term(a), n),
            Downcast(a, m) => Downcast(self.term(a), self.term(m)),
            Down(r, to) => Down(self.term(r), self.term(to)),
            Enum(f) => Enum(self.term(f)),
            Variant(f) => Variant(self.term(f)),
            Upcast(a) => Upcast(self.term(a)),
            Disjoint(a, b) => Disjoint(self.term(a), self.term(b)),
            Up(r, from, to) => Up(self.term(r), self.term(from), self.term(to)),
            Switch(a, cs, d) => {
                let a = self.term(a);
                let mut cm = CaseMap::default();
                for (n, (v, tm)) in cs {
                    cm.insert(n, (self.param_var(v), *self.term(Box::new(tm))));
                }
                let dc = d.map(|(v, tm)| (self.param_var(v), self.term(tm)));
                Switch(a, cm, dc)
            }
            Unionify(a) => Unionify(self.term(a)),
            Find {
                instance_ty: ty,
                interface,
                interface_fn,
            } => Find {
                instance_ty: self.term(ty),
                interface,
                interface_fn,
            },
            Instanceof(a, i) => Instanceof(self.term(a), i),
            Varargs(t) => Varargs(self.term(t)),
            AnonVarargs(t) => AnonVarargs(self.term(t)),
            Spread(a) => Spread(self.term(a)),
            Typeof(ty) => Typeof(self.term(ty)),
            Keyof(ty) => Keyof(self.term(ty)),
            Cls {
                class,
                type_args: t,
                associated: a,
                object,
            } => Cls {
                class,
                type_args: t.into_iter().map(|ty| *self.term(Box::new(ty))).collect(),
                associated: a
                    .into_iter()
                    .map(|(n, ty)| (n, *self.term(Box::new(ty))))
                    .collect(),
                object: self.term(object),
            },
            Panic(a) => Panic(self.term(a)),
            ConsoleLog(m) => ConsoleLog(self.term(m)),
            SetTimeout(f, d, x) => SetTimeout(self.term(f), self.term(d), self.term(x)),
            JSONStringify(a) => JSONStringify(self.term(a)),
            EmitAsync(a) => EmitAsync(self.term(a)),
            tm => tm,
        })
    }

    fn param(&mut self, p: Param<Term>) -> Param<Term> {
        let typ = self.term(p.typ);
        let var = self.param_var(p.var);
        Param {
            var,
            info: p.info,
            typ,
        }
    }

    fn param_var(&mut self, old: Var) -> Var {
        let new = Var::new(old.name.as_str());
        self.0.insert(old, new.clone());
        new
    }
}

pub fn rename(#[allow(clippy::boxed_local)] tm: Box<Term>) -> Box<Term> {
    Renamer::default().term(tm)
}
