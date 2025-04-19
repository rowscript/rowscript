use ustr::Ustr;

use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::abs::data::Term;
use crate::theory::abs::data::Term::{
    AnonVarargs, App, ArrAt, ArrForeach, ArrInsert, ArrIter, ArrIterNext, ArrLength, ArrPush,
    Array, ArrayIterator, Bigint, BigintToStr, BoolAnd, BoolEq, BoolNeq, BoolNot, BoolOr, Boolean,
    ConsoleLog, Discriminants, DocumentGetElementById, EmitAsync, Enum, Fields, Find,
    HtmlElementAddEventListener, Interface, JSONStringify, Map, MapClear, MapDelete, MapGet,
    MapHas, MapIter, MapIterNext, MapIterator, MapSet, NumAdd, NumDiv, NumEq, NumGe, NumGt, NumLe,
    NumLt, NumMod, NumMul, NumNeg, NumNeq, NumSub, NumToStr, Number, Object, Panic, Pi, Pure, Ref,
    RkToStr, Row, Rowkey, SetTimeout, StrAdd, StrEq, StrNeq, StrToLowerCase, String, TupleBind,
    Undef, Unit, Univ,
};
use crate::theory::abs::def::{Body, Def, Sigma};
use crate::theory::conc::data::ArgInfo;
use crate::theory::{ASYNC, AWAIT_ANY, NameMap, Param, ResolvedVar, Var};
use crate::theory::{Tele, VarKind};

fn implicit(var: Var, typ: Term) -> Param<Term> {
    Param {
        var,
        info: Implicit,
        typ: Box::new(typ),
    }
}

fn type_param(var: Var) -> Param<Term> {
    implicit(var, Univ)
}

fn row_param(var: Var) -> Param<Term> {
    implicit(var, Row)
}

fn explicit(var: Var, typ: Term) -> Param<Term> {
    Param {
        var,
        info: Explicit,
        typ: Box::new(typ),
    }
}

fn explicit_pi(p: (Var, Term), b: Term) -> Term {
    Pi {
        param: explicit(p.0, p.1),
        eff: Box::new(Pure),
        body: Box::new(b),
    }
}

fn unbound_explicit_pi(a: Term, b: Term) -> Term {
    explicit_pi((Var::unbound(), a), b)
}

fn explicit_sigma_rfold<const N: usize>(ts: [Term; N], init: Term) -> Term {
    ts.into_iter().rfold(init, |acc, t| {
        Term::Sigma(explicit(Var::unbound(), t), Box::new(acc))
    })
}

fn explicit_sigma<const N: usize>(ts: [Term; N]) -> Term {
    explicit_sigma_rfold(ts, Unit)
}

fn explicit_tuple_bind(p: (Var, Term), q: (Var, Term), a: Term, b: Term) -> Term {
    TupleBind(
        explicit(p.0, p.1),
        explicit(q.0, q.1),
        Box::new(a),
        Box::new(b),
    )
}

fn explicit_tuple_bind1(p: Var, ty: Term, a: Term, b: Term) -> Term {
    explicit_tuple_bind((p, ty), (Var::unbound(), Unit), a, b)
}

fn tuple_param<const N: usize>(var: Var, tele: [(Var, Term); N]) -> Param<Term> {
    let mut ty = Unit;
    for (var, typ) in tele.into_iter().rev() {
        ty = Term::Sigma(explicit(var, typ), Box::new(ty));
    }
    Param {
        var,
        info: Explicit,
        typ: Box::new(ty),
    }
}

fn option_type(t: Term) -> Term {
    Enum(Box::new(Fields(
        [("Ok".into(), t), ("None".into(), Unit)]
            .into_iter()
            .collect(),
    )))
}

fn entry_type(k: Term, v: Term) -> Term {
    Object(Box::new(Fields(
        [("key".into(), k), ("value".into(), v)]
            .into_iter()
            .collect(),
    )))
}

fn parameters<const T: usize, const V: usize>(
    types: [Var; T],
    params: [(Var, Term); V],
) -> (Term, Tele<Term>) {
    let tupled = Var::tupled();
    let mut tele: Tele<_> = types.into_iter().map(type_param).collect();
    tele.push(tuple_param(tupled.clone(), params));
    (Ref(tupled), tele)
}

macro_rules! un_op {
    ($name:ident, $builtin_name:literal, $typ:ident, $ret:ident, $op:ident) => {
        fn $name(self) -> Self {
            let a = Var::new("a");
            let (tupled, tele) = parameters([], [(a.clone(), $typ)]);
            self.func(
                $builtin_name,
                tele,
                $ret,
                explicit_tuple_bind1(a.clone(), $typ, tupled, $op(Box::new(Ref(a)))),
            )
        }
    };
}

macro_rules! bin_op {
    ($name:ident, $builtin_name:literal, $typ:ident, $ret:ident, $op:ident) => {
        fn $name(self) -> Self {
            let a = Var::new("a");
            let a_rhs = a.untupled_rhs();
            let b = Var::new("b");
            let (tupled, tele) = parameters([], [(a.clone(), $typ), (b.clone(), $typ)]);
            self.func(
                $builtin_name,
                tele,
                $ret,
                explicit_tuple_bind(
                    (a.clone(), $typ),
                    (a_rhs.clone(), explicit_sigma([$typ])),
                    tupled,
                    explicit_tuple_bind1(
                        b.clone(),
                        $typ,
                        Ref(a_rhs),
                        $op(Box::new(Ref(a)), Box::new(Ref(b))),
                    ),
                ),
            )
        }
    };
}

#[derive(Default)]
pub struct Builtins {
    pub ubiquitous: NameMap,
    pub sigma: Sigma,
}

impl Builtins {
    pub fn new() -> Self {
        Self::default()
            .reserved([
                Var::r#typeof(),
                Var::list(),
                Var::async_effect(),
                Var::await_one(),
                Var::await_mul(),
                Var::await_all(),
                Var::await_any(),
            ])
            .panic()
            .console_log()
            .set_timeout()
            .boolean_or()
            .boolean_and()
            .boolean_not()
            .boolean_eq()
            .boolean_neq()
            .string_add()
            .string_eq()
            .string_neq()
            .string_to_lower_case()
            .number_add()
            .number_sub()
            .number_mul()
            .number_div()
            .number_mod()
            .number_eq()
            .number_neq()
            .number_le()
            .number_ge()
            .number_lt()
            .number_gt()
            .number_neg()
            .number_to_string()
            .bigint_to_string()
            .rowkey_to_string()
            .reflect_discriminants()
            .array_iterator_type()
            .array_iterator_next()
            .array_type()
            .array_length()
            .array_push()
            .array_foreach()
            .array_at()
            .array_set()
            .array_iter()
            .map_iterator_type()
            .map_iterator_next()
            .map_type()
            .map_has()
            .map_get()
            .map_set()
            .map_delete()
            .map_clear()
            .map_iter()
            .await_all()
            .await_any()
            .json_stringify()
            .html_element_add_event_listener()
            .document_get_element_by_id()
    }

    fn func(self, name: &str, tele: Tele<Term>, ret: Term, f: Term) -> Self {
        self.impure_func(name, tele, Pure, ret, f)
    }

    fn impure_func(self, name: &str, tele: Tele<Term>, eff: Term, ret: Term, f: Term) -> Self {
        self.define(Def {
            is_public: false,
            loc: Default::default(),
            name: Var::new(name),
            tele,
            eff: Box::new(eff),
            ret: Box::new(ret),
            body: Body::Fn(Box::new(f)),
        })
    }

    fn define(mut self, def: Def<Term>) -> Self {
        self.ubiquitous.insert(
            *def.name.as_str(),
            ResolvedVar(VarKind::Inside, def.name.clone()),
        );
        self.sigma.insert(def.name.clone(), def);
        self
    }

    fn defined(&self, name: &str) -> Term {
        Undef(self.ubiquitous.get(&Ustr::from(name)).unwrap().1.clone())
    }

    fn reserved<const N: usize>(mut self, vars: [Var; N]) -> Self {
        for v in vars {
            self.ubiquitous
                .insert(*v.as_str(), ResolvedVar(VarKind::Reserved, v));
        }
        self
    }

    fn panic(self) -> Self {
        let t = Var::new("T");
        let tupled = Var::tupled();
        let m = Var::new("m");
        let m_ty = String;
        self.func(
            "panic",
            vec![
                type_param(t.clone()),
                tuple_param(tupled.clone(), [(m.clone(), m_ty.clone())]),
            ],
            Ref(t),
            explicit_tuple_bind1(m.clone(), m_ty, Ref(tupled), Panic(Box::new(Ref(m)))),
        )
    }

    fn console_log(self) -> Self {
        let varargs = Var::new("Args");
        let tupled = Var::tupled();
        self.func(
            "console#log",
            vec![
                type_param(varargs.clone()),
                explicit(tupled.clone(), AnonVarargs(Box::new(Ref(varargs)))),
            ],
            Unit,
            ConsoleLog(Box::new(Ref(tupled))),
        )
    }

    fn set_timeout(self) -> Self {
        let varargs = Var::new("Args");
        let t = Var::new("T");
        let tupled = Var::tupled();
        let f = Var::new("f");
        let f_rhs = f.untupled_rhs();
        let d = Var::new("d");
        let ends = Var::untupled_ends();
        self.func(
            "setTimeout",
            vec![
                type_param(varargs.clone()),
                type_param(t.clone()),
                explicit(
                    tupled.clone(),
                    explicit_sigma_rfold(
                        [
                            unbound_explicit_pi(
                                AnonVarargs(Box::new(Ref(varargs.clone()))),
                                Ref(t.clone()),
                            ),
                            Number,
                        ],
                        Ref(varargs.clone()),
                    ),
                ),
            ],
            Unit,
            explicit_tuple_bind(
                (
                    f.clone(),
                    unbound_explicit_pi(AnonVarargs(Box::new(Ref(varargs.clone()))), Ref(t)),
                ),
                (
                    f_rhs.clone(),
                    explicit_sigma([Number, Ref(varargs.clone())]),
                ),
                Ref(tupled),
                explicit_tuple_bind(
                    (d.clone(), Number),
                    (ends.clone(), Ref(varargs)),
                    Ref(f_rhs),
                    SetTimeout(Box::new(Ref(f)), Box::new(Ref(d)), Box::new(Ref(ends))),
                ),
            ),
        )
    }

    bin_op!(boolean_or, "boolean#__or__", Boolean, Boolean, BoolOr);
    bin_op!(boolean_and, "boolean#__and__", Boolean, Boolean, BoolAnd);
    bin_op!(boolean_eq, "boolean#__eq__", Boolean, Boolean, BoolEq);
    bin_op!(boolean_neq, "boolean#__neq__", Boolean, Boolean, BoolNeq);
    un_op!(boolean_not, "boolean#__not__", Boolean, Boolean, BoolNot);

    bin_op!(string_add, "string#__add__", String, String, StrAdd);
    bin_op!(string_eq, "string#__eq__", String, Boolean, StrEq);
    bin_op!(string_neq, "string#__neq__", String, Boolean, StrNeq);
    un_op!(
        string_to_lower_case,
        "string#toLowerCase",
        String,
        String,
        StrToLowerCase
    );

    bin_op!(number_add, "number#__add__", Number, Number, NumAdd);
    bin_op!(number_sub, "number#__sub__", Number, Number, NumSub);
    bin_op!(number_mul, "number#__mul__", Number, Number, NumMul);
    bin_op!(number_div, "number#__div__", Number, Number, NumDiv);
    bin_op!(number_mod, "number#__mod__", Number, Number, NumMod);
    bin_op!(number_eq, "number#__eq__", Number, Boolean, NumEq);
    bin_op!(number_neq, "number#__neq__", Number, Boolean, NumNeq);
    bin_op!(number_le, "number#__le__", Number, Boolean, NumLe);
    bin_op!(number_ge, "number#__ge__", Number, Boolean, NumGe);
    bin_op!(number_lt, "number#__lt__", Number, Boolean, NumLt);
    bin_op!(number_gt, "number#__gt__", Number, Boolean, NumGt);
    un_op!(number_neg, "number#__neg__", Number, Number, NumNeg);
    un_op!(
        number_to_string,
        "number#toString",
        Number,
        String,
        NumToStr
    );

    un_op!(
        bigint_to_string,
        "bigint#toString",
        Bigint,
        String,
        BigintToStr
    );

    un_op!(rowkey_to_string, "rowkey#toString", Rowkey, String, RkToStr);

    fn reflect_discriminants(self) -> Self {
        let r = Var::new("'a");
        let a = Var::new("a");
        let tupled = Var::tupled();
        let list_ty = self.defined("List");
        self.func(
            "reflect#discriminants",
            vec![
                row_param(r.clone()),
                tuple_param(
                    tupled.clone(),
                    [(a.clone(), Enum(Box::new(Ref(r.clone()))))],
                ),
            ],
            App(
                Box::new(list_ty),
                ArgInfo::UnnamedImplicit,
                Box::new(Rowkey),
            ),
            explicit_tuple_bind1(
                a,
                Enum(Box::new(Ref(r.clone()))),
                Ref(tupled),
                Discriminants(Box::new(Ref(r))),
            ),
        )
    }

    fn array_iterator_type(self) -> Self {
        let t = Var::new("T");
        self.func(
            "NativeArrayIterator",
            vec![type_param(t.clone())],
            Univ,
            ArrayIterator(Box::new(Ref(t))),
        )
    }

    fn array_iterator_next(self) -> Self {
        let t = Var::new("T");
        let a = Var::new("a");
        let a_ty = ArrayIterator(Box::new(Ref(t.clone())));
        let (tupled, tele) = parameters([t.clone()], [(a.clone(), a_ty.clone())]);
        self.func(
            "arrayIter#next",
            tele,
            option_type(Ref(t)),
            explicit_tuple_bind1(
                a.clone(),
                a_ty.clone(),
                tupled,
                ArrIterNext(Box::new(Ref(a))),
            ),
        )
    }

    fn array_type(self) -> Self {
        let t = Var::new("T");
        self.func(
            "NativeArray",
            vec![type_param(t.clone())],
            Univ,
            Array(Box::new(Ref(t))),
        )
    }

    fn array_length(self) -> Self {
        let t = Var::new("T");
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_ty = Array(Box::new(Ref(t.clone())));
        self.func(
            "array#length",
            vec![
                type_param(t),
                tuple_param(tupled.clone(), [(a.clone(), a_ty.clone())]),
            ],
            Number,
            explicit_tuple_bind1(
                a.clone(),
                a_ty.clone(),
                Ref(tupled),
                ArrLength(Box::new(Ref(a))),
            ),
        )
    }

    fn array_push(self) -> Self {
        let t = Var::new("T");
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_ty = Array(Box::new(Ref(t.clone())));
        let a_rhs = a.untupled_rhs();
        let v = Var::new("v");
        let v_ty = Ref(t.clone());
        self.func(
            "array#push",
            vec![
                type_param(t),
                tuple_param(
                    tupled.clone(),
                    [(a.clone(), a_ty.clone()), (v.clone(), v_ty.clone())],
                ),
            ],
            Number,
            explicit_tuple_bind(
                (a.clone(), a_ty),
                (a_rhs.clone(), explicit_sigma([v_ty.clone()])),
                Ref(tupled),
                explicit_tuple_bind1(
                    v.clone(),
                    v_ty,
                    Ref(a_rhs),
                    ArrPush(Box::new(Ref(a)), Box::new(Ref(v))),
                ),
            ),
        )
    }

    fn array_foreach(self) -> Self {
        let t = Var::new("T");
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_ty = Array(Box::new(Ref(t.clone())));
        let a_rhs = a.untupled_rhs();
        let f = Var::new("f");
        let f_ty = Pi {
            param: tuple_param(Var::unbound(), [(Var::new("v"), Ref(t.clone()))]),
            eff: Box::new(Pure),
            body: Box::new(Unit),
        };
        self.func(
            "array#forEach",
            vec![
                type_param(t),
                tuple_param(
                    tupled.clone(),
                    [(a.clone(), a_ty.clone()), (f.clone(), f_ty.clone())],
                ),
            ],
            Unit,
            explicit_tuple_bind(
                (a.clone(), a_ty),
                (a_rhs.clone(), explicit_sigma([f_ty.clone()])),
                Ref(tupled),
                explicit_tuple_bind1(
                    f.clone(),
                    f_ty,
                    Ref(a_rhs),
                    ArrForeach(Box::new(Ref(a)), Box::new(Ref(f))),
                ),
            ),
        )
    }

    fn array_at(self) -> Self {
        let t = Var::new("T");
        let a = Var::new("a");
        let a_ty = Array(Box::new(Ref(t.clone())));
        let a_rhs = a.untupled_rhs();
        let i = Var::new("i");
        let i_ty = Number;
        let (tupled, tele) = parameters(
            [t.clone()],
            [(a.clone(), a_ty.clone()), (i.clone(), i_ty.clone())],
        );
        self.func(
            "array#at",
            tele,
            option_type(Ref(t)),
            explicit_tuple_bind(
                (a.clone(), a_ty),
                (a_rhs.clone(), explicit_sigma([i_ty.clone()])),
                tupled,
                explicit_tuple_bind1(
                    i.clone(),
                    i_ty,
                    Ref(a_rhs),
                    ArrAt(Box::new(Ref(a)), Box::new(Ref(i))),
                ),
            ),
        )
    }

    fn array_set(self) -> Self {
        let t = Var::new("T");
        let a = Var::new("a");
        let a_ty = Array(Box::new(Ref(t.clone())));
        let a_rhs = a.untupled_rhs();
        let i = Var::new("i");
        let i_ty = Number;
        let i_rhs = i.untupled_rhs();
        let v = Var::new("v");
        let v_ty = Ref(t.clone());
        let (tupled, tele) = parameters(
            [t],
            [
                (a.clone(), a_ty.clone()),
                (i.clone(), i_ty.clone()),
                (v.clone(), v_ty.clone()),
            ],
        );
        self.func(
            "array#set",
            tele,
            Unit,
            explicit_tuple_bind(
                (a.clone(), a_ty),
                (a_rhs.clone(), explicit_sigma([i_ty.clone(), v_ty.clone()])),
                tupled,
                explicit_tuple_bind(
                    (i.clone(), i_ty),
                    (i_rhs.clone(), explicit_sigma([v_ty.clone()])),
                    Ref(a_rhs),
                    explicit_tuple_bind1(
                        v.clone(),
                        v_ty,
                        Ref(i_rhs),
                        ArrInsert(Box::new(Ref(a)), Box::new(Ref(i)), Box::new(Ref(v))),
                    ),
                ),
            ),
        )
    }

    fn array_iter(self) -> Self {
        let t = Var::new("T");
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_ty = Array(Box::new(Ref(t.clone())));
        self.func(
            "array#iter",
            vec![
                type_param(t.clone()),
                tuple_param(tupled.clone(), [(a.clone(), a_ty.clone())]),
            ],
            ArrayIterator(Box::new(Ref(t))),
            explicit_tuple_bind1(a.clone(), a_ty, Ref(tupled), ArrIter(Box::new(Ref(a)))),
        )
    }

    fn map_iterator_type(self) -> Self {
        let t = Var::new("T");
        self.func(
            "NativeMapIterator",
            vec![type_param(t.clone())],
            Univ,
            MapIterator(Box::new(Ref(t))),
        )
    }

    fn map_iterator_next(self) -> Self {
        let t = Var::new("T");
        let m = Var::new("m");
        let m_ty = MapIterator(Box::new(Ref(t.clone())));
        let (tupled, tele) = parameters([t.clone()], [(m.clone(), m_ty.clone())]);
        self.func(
            "mapIter#next",
            tele,
            option_type(Ref(t)),
            explicit_tuple_bind1(m.clone(), m_ty, tupled, MapIterNext(Box::new(Ref(m)))),
        )
    }

    fn map_type(self) -> Self {
        let k = Var::new("K");
        let v = Var::new("V");
        self.func(
            "NativeMap",
            vec![type_param(k.clone()), type_param(v.clone())],
            Univ,
            Map(Box::new(Ref(k)), Box::new(Ref(v))),
        )
    }

    fn map_has(self) -> Self {
        let k = Var::new("K");
        let v = Var::new("V");
        let tupled = Var::tupled();
        let m = Var::new("m");
        let m_ty = Map(Box::new(Ref(k.clone())), Box::new(Ref(v.clone())));
        let m_rhs = m.untupled_rhs();
        let key = Var::new("k");
        let key_ty = Ref(k.clone());
        self.func(
            "map#has",
            vec![
                type_param(k.clone()),
                type_param(v),
                tuple_param(
                    tupled.clone(),
                    [(m.clone(), m_ty.clone()), (key.clone(), key_ty.clone())],
                ),
            ],
            Boolean,
            explicit_tuple_bind(
                (m.clone(), m_ty),
                (m_rhs.clone(), explicit_sigma([key_ty.clone()])),
                Ref(tupled),
                explicit_tuple_bind1(
                    key.clone(),
                    key_ty,
                    Ref(m_rhs),
                    MapHas(Box::new(Ref(m)), Box::new(Ref(key))),
                ),
            ),
        )
    }

    fn map_get(self) -> Self {
        let k = Var::new("K");
        let v = Var::new("V");
        let m = Var::new("m");
        let m_ty = Map(Box::new(Ref(k.clone())), Box::new(Ref(v.clone())));
        let m_rhs = m.untupled_rhs();
        let key = Var::new("k");
        let key_ty = Ref(k.clone());
        let (tupled, tele) = parameters(
            [k, v.clone()],
            [(m.clone(), m_ty.clone()), (key.clone(), key_ty.clone())],
        );
        self.func(
            "map#get",
            tele,
            Ref(v),
            explicit_tuple_bind(
                (m.clone(), m_ty),
                (m_rhs.clone(), explicit_sigma([key_ty.clone()])),
                tupled,
                explicit_tuple_bind1(
                    key.clone(),
                    key_ty,
                    Ref(m_rhs),
                    MapGet(Box::new(Ref(m)), Box::new(Ref(key))),
                ),
            ),
        )
    }

    fn map_set(self) -> Self {
        let k = Var::new("K");
        let v = Var::new("T");
        let m = Var::new("m");
        let m_ty = Map(Box::new(Ref(k.clone())), Box::new(Ref(v.clone())));
        let m_rhs = m.untupled_rhs();
        let key = Var::new("k");
        let key_ty = Ref(k.clone());
        let key_rhs = key.untupled_rhs();
        let val = Var::new("v");
        let val_ty = Ref(v.clone());
        let (tupled, tele) = parameters(
            [k.clone(), v.clone()],
            [
                (m.clone(), m_ty.clone()),
                (key.clone(), key_ty.clone()),
                (val.clone(), val_ty.clone()),
            ],
        );
        self.func(
            "map#set",
            tele,
            Unit,
            explicit_tuple_bind(
                (m.clone(), m_ty),
                (
                    m_rhs.clone(),
                    explicit_sigma([key_ty.clone(), val_ty.clone()]),
                ),
                tupled,
                explicit_tuple_bind(
                    (key.clone(), key_ty),
                    (key_rhs.clone(), explicit_sigma([val_ty.clone()])),
                    Ref(m_rhs),
                    explicit_tuple_bind1(
                        val.clone(),
                        val_ty,
                        Ref(key_rhs),
                        MapSet(Box::new(Ref(m)), Box::new(Ref(key)), Box::new(Ref(val))),
                    ),
                ),
            ),
        )
    }

    fn map_delete(self) -> Self {
        let k = Var::new("K");
        let v = Var::new("V");
        let m = Var::new("m");
        let m_ty = Map(Box::new(Ref(k.clone())), Box::new(Ref(v.clone())));
        let m_rhs = m.untupled_rhs();
        let key = Var::new("k");
        let key_ty = Ref(k.clone());
        let (tupled, tele) = parameters(
            [k, v],
            [(m.clone(), m_ty.clone()), (key.clone(), key_ty.clone())],
        );
        self.func(
            "map#delete",
            tele,
            Boolean,
            explicit_tuple_bind(
                (m.clone(), m_ty),
                (m_rhs.clone(), explicit_sigma([key_ty.clone()])),
                tupled,
                explicit_tuple_bind1(
                    key.clone(),
                    key_ty,
                    Ref(m_rhs),
                    MapDelete(Box::new(Ref(m)), Box::new(Ref(key))),
                ),
            ),
        )
    }

    fn map_clear(self) -> Self {
        let k = Var::new("K");
        let v = Var::new("V");
        let m = Var::new("m");
        let m_ty = Map(Box::new(Ref(k.clone())), Box::new(Ref(v.clone())));
        let (tupled, tele) = parameters([k.clone(), v.clone()], [(m.clone(), m_ty.clone())]);
        self.func(
            "map#clear",
            tele,
            Unit,
            explicit_tuple_bind1(m.clone(), m_ty, tupled, MapClear(Box::new(Ref(m)))),
        )
    }

    fn map_iter(self) -> Self {
        let k = Var::new("K");
        let v = Var::new("V");
        let m = Var::new("m");
        let m_ty = Map(Box::new(Ref(k.clone())), Box::new(Ref(v.clone())));
        let (tupled, tele) = parameters([k.clone(), v.clone()], [(m.clone(), m_ty.clone())]);
        self.func(
            "map#iter",
            tele,
            MapIterator(Box::new(entry_type(Ref(k), Ref(v)))),
            explicit_tuple_bind1(m.clone(), m_ty, tupled, MapIter(Box::new(Ref(m)))),
        )
    }

    fn executors_type(&self, v_ty: Term) -> Term {
        App(
            Box::new(self.defined("NativeArray")),
            ArgInfo::UnnamedImplicit,
            Box::new(Pi {
                param: tuple_param(
                    Var::tupled(),
                    [(
                        Var::new("resolve"),
                        Pi {
                            param: tuple_param(Var::tupled(), [(Var::new("value"), v_ty)]),
                            eff: Box::new(Pure),
                            body: Box::new(Unit),
                        },
                    )],
                ),
                eff: Box::new(Pure),
                body: Box::new(Unit),
            }),
        )
    }

    fn emit_async(tupled: Term, ty: Term, interface: Var, interface_fn: Var) -> Term {
        EmitAsync(Box::new(App(
            Box::new(Find {
                interface_fn,
                instance_ty: Box::new(Interface {
                    name: interface,
                    args: Box::new([ty]),
                    should_check: false,
                }),
            }),
            ArgInfo::UnnamedExplicit,
            Box::new(tupled),
        )))
    }

    fn await_all(self) -> Self {
        let t = Var::new("T");
        let executors_ty = self.executors_type(Ref(t.clone()));
        let array_ty = self.defined("NativeArray");
        let e = Var::new("executors");
        let (tupled, tele) = parameters([t.clone()], [(e.clone(), executors_ty.clone())]);
        let async_var = self.ubiquitous.get(&Ustr::from(ASYNC)).unwrap().1.clone();
        let await_all_var = self
            .ubiquitous
            .get(&Ustr::from(AWAIT_ANY))
            .unwrap()
            .1
            .clone();
        let eff = Term::async_effect(async_var.clone());
        self.impure_func(
            "await#all",
            tele,
            eff,
            App(
                Box::new(array_ty),
                ArgInfo::UnnamedImplicit,
                Box::new(Ref(t)),
            ),
            Self::emit_async(tupled, executors_ty, async_var, await_all_var),
        )
    }

    fn await_any(self) -> Self {
        let t = Var::new("T");
        let executors_ty = self.executors_type(Ref(t.clone()));
        let e = Var::new("executors");
        let (tupled, tele) = parameters([t.clone()], [(e.clone(), executors_ty.clone())]);
        let async_var = self.ubiquitous.get(&Ustr::from(ASYNC)).unwrap().1.clone();
        let await_any_var = self
            .ubiquitous
            .get(&Ustr::from(AWAIT_ANY))
            .unwrap()
            .1
            .clone();
        let eff = Term::async_effect(async_var.clone());
        self.impure_func(
            "await#any",
            tele,
            eff,
            Ref(t),
            Self::emit_async(tupled, executors_ty, async_var, await_any_var),
        )
    }

    fn json_stringify(self) -> Self {
        let t = Var::new("T");
        let a = Var::new("a");
        let (tupled, tele) = parameters([t.clone()], [(a.clone(), Ref(t.clone()))]);
        self.func(
            "json#stringify",
            tele,
            String,
            explicit_tuple_bind1(a.clone(), Ref(t), tupled, JSONStringify(Box::new(Ref(a)))),
        )
    }

    fn html_element_add_event_listener(self) -> Self {
        let n = Var::new("n");
        let n_rhs = n.untupled_rhs();
        let n_ty = Var::new("HTMLElement");
        let e = Var::new("e");
        let e_rhs = e.untupled_rhs();
        let l = Var::new("l");
        let l_ty = Var::new("Listener");
        let (tupled, tele) = parameters(
            [n_ty.clone(), l_ty.clone()],
            [
                (n.clone(), Ref(n_ty.clone())),
                (e.clone(), String),
                (l.clone(), Ref(l_ty.clone())),
            ],
        );
        self.func(
            "htmlElement#addEventListener",
            tele,
            Unit,
            explicit_tuple_bind(
                (n.clone(), Ref(n_ty.clone())),
                (
                    n_rhs.clone(),
                    explicit_sigma([Ref(n_ty.clone()), Ref(l_ty.clone())]),
                ),
                tupled,
                explicit_tuple_bind(
                    (e.clone(), String),
                    (e_rhs.clone(), explicit_sigma([Ref(l_ty.clone())])),
                    Ref(n_rhs),
                    explicit_tuple_bind1(
                        l.clone(),
                        Ref(l_ty),
                        Ref(e_rhs),
                        HtmlElementAddEventListener(
                            Box::new(Ref(n)),
                            Box::new(Ref(e)),
                            Box::new(Ref(l)),
                        ),
                    ),
                ),
            ),
        )
    }

    fn document_get_element_by_id(self) -> Self {
        let a = Var::new("a");
        let e = Var::new("HTMLElement");
        let (tupled, tele) = parameters([e.clone()], [(a.clone(), String)]);
        self.func(
            "document#getElementById",
            tele,
            Ref(e),
            explicit_tuple_bind1(
                a.clone(),
                String,
                tupled,
                DocumentGetElementById(Box::new(Ref(a))),
            ),
        )
    }
}
