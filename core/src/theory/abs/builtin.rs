use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Body, Def, Sigma};
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::{NameMap, Param, ResolvedVar, Var};
use crate::theory::{Tele, VarKind};

fn implicit(var: Var, typ: Term) -> Param<Term> {
    Param {
        var,
        info: Implicit,
        typ: Box::new(typ),
    }
}

fn type_param(var: Var) -> Param<Term> {
    implicit(var, Term::Univ)
}

fn row_param(var: Var) -> Param<Term> {
    implicit(var, Term::Row)
}

fn explicit(var: Var, typ: Term) -> Param<Term> {
    Param {
        var,
        info: Explicit,
        typ: Box::new(typ),
    }
}

fn explicit_sigma(p: (Var, Term), b: Term) -> Term {
    Term::Sigma(explicit(p.0, p.1), Box::new(b))
}

fn explicit_sigma1(p: Var, ty: Term) -> Term {
    explicit_sigma((p, ty), Term::Unit)
}

fn explicit_tuple_local(p: (Var, Term), q: (Var, Term), a: Term, b: Term) -> Term {
    Term::TupleLocal(
        explicit(p.0, p.1),
        explicit(q.0, q.1),
        Box::new(a),
        Box::new(b),
    )
}

fn explicit_tuple_local1(p: Var, ty: Term, a: Term, b: Term) -> Term {
    explicit_tuple_local((p, ty), (Var::unbound(), Term::Unit), a, b)
}

fn tuple_param<const N: usize>(var: Var, tele: [(Var, Term); N]) -> Param<Term> {
    let mut ty = Term::Unit;
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
    Term::Enum(Box::new(Term::Fields(
        [("Ok".to_string(), t), ("None".to_string(), Term::Unit)]
            .into_iter()
            .collect(),
    )))
}

fn entry_type(k: Term, v: Term) -> Term {
    Term::Object(Box::new(Term::Fields(
        [("key".to_string(), k), ("value".to_string(), v)]
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
    (Term::Ref(tupled), tele)
}

macro_rules! un_op {
    ($name:ident, $builtin_name:literal, $typ:ident, $ret:ident, $op:ident) => {
        fn $name(self) -> Self {
            let a = Var::new("a");
            let (tupled, tele) = parameters([], [(a.clone(), Term::$typ)]);
            self.func(
                $builtin_name,
                tele,
                Term::$ret,
                explicit_tuple_local1(
                    a.clone(),
                    Term::$typ,
                    tupled,
                    Term::$op(Box::new(Term::Ref(a))),
                ),
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
            let (tupled, tele) = parameters([], [(a.clone(), Term::$typ), (b.clone(), Term::$typ)]);
            self.func(
                $builtin_name,
                tele,
                Term::$ret,
                explicit_tuple_local(
                    (a.clone(), Term::$typ),
                    (a_rhs.clone(), explicit_sigma1(b.clone(), Term::$typ)),
                    tupled,
                    explicit_tuple_local1(
                        b.clone(),
                        Term::$typ,
                        Term::Ref(a_rhs),
                        Term::$op(Box::new(Term::Ref(a)), Box::new(Term::Ref(b))),
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
            .error_throw()
            .console_log()
            .unionify()
            .reflect()
            .boolean_or()
            .boolean_and()
            .boolean_not()
            .boolean_eq()
            .boolean_neq()
            .string_add()
            .string_eq()
            .string_neq()
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
    }

    fn func(self, name: &str, tele: Tele<Term>, ret: Term, f: Term) -> Self {
        self.define(Def {
            loc: Default::default(),
            name: Var::new(name),
            tele,
            ret: Box::new(ret),
            body: Body::Fn(f),
        })
    }

    fn define(mut self, def: Def<Term>) -> Self {
        self.ubiquitous.insert(
            def.name.to_string(),
            ResolvedVar(VarKind::InModule, def.name.clone()),
        );
        self.sigma.insert(def.name.clone(), def);
        self
    }

    fn error_throw(self) -> Self {
        let t = Var::new("T");
        let tupled = Var::tupled();
        let m = Var::new("m");
        let m_ty = Term::String;
        self.func(
            "error#throw",
            vec![
                type_param(t.clone()),
                tuple_param(tupled.clone(), [(m.clone(), m_ty.clone())]),
            ],
            Term::Ref(t),
            explicit_tuple_local1(
                m.clone(),
                m_ty,
                Term::Ref(tupled),
                Term::ErrorThrow(Box::new(Term::Ref(m))),
            ),
        )
    }

    fn console_log(self) -> Self {
        let t = Var::new("T");
        let m = Var::new("m");
        let m_ty = Term::Ref(t.clone());
        let (tupled, tele) = parameters([t.clone()], [(m.clone(), m_ty.clone())]);
        self.func(
            "console#log",
            tele,
            Term::Unit,
            explicit_tuple_local1(
                m.clone(),
                m_ty,
                tupled,
                Term::ConsoleLog(Box::new(Term::Ref(m))),
            ),
        )
    }

    fn unionify(self) -> Self {
        let r = Var::new("'R");
        let a = Var::new("a");
        let a_ty = Term::Enum(Box::new(Term::Ref(r.clone())));
        let tupled = Var::tupled();
        let tele = vec![
            row_param(r),
            tuple_param(tupled.clone(), [(a.clone(), a_ty.clone())]),
        ];
        self.func(
            "unionify",
            tele,
            a_ty.clone(),
            explicit_tuple_local1(
                a.clone(),
                a_ty,
                Term::Ref(tupled),
                Term::Unionify(Box::new(Term::Ref(a))),
            ),
        )
    }

    fn reflect(self) -> Self {
        let t = Var::new("T");
        self.func(
            "Reflected",
            vec![implicit(t.clone(), Term::Univ)],
            Term::Univ,
            Term::Reflected(Box::new(Term::Ref(t))),
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

    fn array_iterator_type(self) -> Self {
        let t = Var::new("T");
        self.func(
            "NativeArrayIterator",
            vec![implicit(t.clone(), Term::Univ)],
            Term::Univ,
            Term::ArrayIterator(Box::new(Term::Ref(t))),
        )
    }

    fn array_iterator_next(self) -> Self {
        let t = Var::new("T");
        let a = Var::new("a");
        let a_ty = Term::ArrayIterator(Box::new(Term::Ref(t.clone())));
        let (tupled, tele) = parameters([t.clone()], [(a.clone(), a_ty.clone())]);
        self.func(
            "arrayIter#next",
            tele,
            option_type(Term::Ref(t)),
            explicit_tuple_local1(
                a.clone(),
                a_ty.clone(),
                tupled,
                Term::ArrIterNext(Box::new(Term::Ref(a))),
            ),
        )
    }

    fn array_type(self) -> Self {
        let t = Var::new("T");
        self.func(
            "NativeArray",
            vec![type_param(t.clone())],
            Term::Univ,
            Term::Array(Box::new(Term::Ref(t))),
        )
    }

    fn array_length(self) -> Self {
        let t = Var::new("T");
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_ty = Term::Array(Box::new(Term::Ref(t.clone())));
        self.func(
            "array#length",
            vec![
                type_param(t),
                tuple_param(tupled.clone(), [(a.clone(), a_ty.clone())]),
            ],
            Term::Number,
            explicit_tuple_local1(
                a.clone(),
                a_ty.clone(),
                Term::Ref(tupled),
                Term::ArrLength(Box::new(Term::Ref(a))),
            ),
        )
    }

    fn array_push(self) -> Self {
        let t = Var::new("T");
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_ty = Term::Array(Box::new(Term::Ref(t.clone())));
        let a_rhs = a.untupled_rhs();
        let v = Var::new("v");
        let v_ty = Term::Ref(t.clone());
        self.func(
            "array#push",
            vec![
                type_param(t),
                tuple_param(
                    tupled.clone(),
                    [(a.clone(), a_ty.clone()), (v.clone(), v_ty.clone())],
                ),
            ],
            Term::Number,
            explicit_tuple_local(
                (a.clone(), a_ty),
                (a_rhs.clone(), explicit_sigma1(v.clone(), v_ty.clone())),
                Term::Ref(tupled),
                explicit_tuple_local1(
                    v.clone(),
                    v_ty,
                    Term::Ref(a_rhs),
                    Term::ArrPush(Box::new(Term::Ref(a)), Box::new(Term::Ref(v))),
                ),
            ),
        )
    }

    fn array_foreach(self) -> Self {
        let t = Var::new("T");
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_ty = Term::Array(Box::new(Term::Ref(t.clone())));
        let a_rhs = a.untupled_rhs();
        let f = Var::new("f");
        let f_ty = Term::Pi(
            tuple_param(Var::unbound(), [(Var::new("v"), Term::Ref(t.clone()))]),
            Box::new(Term::Unit),
        );
        self.func(
            "array#forEach",
            vec![
                type_param(t),
                tuple_param(
                    tupled.clone(),
                    [(a.clone(), a_ty.clone()), (f.clone(), f_ty.clone())],
                ),
            ],
            Term::Unit,
            explicit_tuple_local(
                (a.clone(), a_ty),
                (a_rhs.clone(), explicit_sigma1(f.clone(), f_ty.clone())),
                Term::Ref(tupled),
                explicit_tuple_local1(
                    f.clone(),
                    f_ty,
                    Term::Ref(a_rhs),
                    Term::ArrForeach(Box::new(Term::Ref(a)), Box::new(Term::Ref(f))),
                ),
            ),
        )
    }

    fn array_at(self) -> Self {
        let t = Var::new("T");
        let a = Var::new("a");
        let a_ty = Term::Array(Box::new(Term::Ref(t.clone())));
        let a_rhs = a.untupled_rhs();
        let i = Var::new("i");
        let i_ty = Term::Number;
        let (tupled, tele) = parameters(
            [t.clone()],
            [(a.clone(), a_ty.clone()), (i.clone(), i_ty.clone())],
        );
        self.func(
            "array#at",
            tele,
            option_type(Term::Ref(t)),
            explicit_tuple_local(
                (a.clone(), a_ty),
                (a_rhs.clone(), explicit_sigma1(i.clone(), i_ty.clone())),
                tupled,
                explicit_tuple_local1(
                    i.clone(),
                    i_ty,
                    Term::Ref(a_rhs),
                    Term::ArrAt(Box::new(Term::Ref(a)), Box::new(Term::Ref(i))),
                ),
            ),
        )
    }

    fn array_set(self) -> Self {
        let t = Var::new("T");
        let a = Var::new("a");
        let a_ty = Term::Array(Box::new(Term::Ref(t.clone())));
        let a_rhs = a.untupled_rhs();
        let i = Var::new("i");
        let i_ty = Term::Number;
        let i_rhs = i.untupled_rhs();
        let v = Var::new("v");
        let v_ty = Term::Ref(t.clone());
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
            Term::Unit,
            explicit_tuple_local(
                (a.clone(), a_ty),
                (
                    a_rhs.clone(),
                    explicit_sigma(
                        (i.clone(), i_ty.clone()),
                        explicit_sigma1(v.clone(), v_ty.clone()),
                    ),
                ),
                tupled,
                explicit_tuple_local(
                    (i.clone(), i_ty),
                    (i_rhs.clone(), explicit_sigma1(v.clone(), v_ty.clone())),
                    Term::Ref(a_rhs),
                    explicit_tuple_local1(
                        v.clone(),
                        v_ty,
                        Term::Ref(i_rhs),
                        Term::ArrInsert(
                            Box::new(Term::Ref(a)),
                            Box::new(Term::Ref(i)),
                            Box::new(Term::Ref(v)),
                        ),
                    ),
                ),
            ),
        )
    }

    fn array_iter(self) -> Self {
        let t = Var::new("T");
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_ty = Term::Array(Box::new(Term::Ref(t.clone())));
        self.func(
            "array#iter",
            vec![
                type_param(t.clone()),
                tuple_param(tupled.clone(), [(a.clone(), a_ty.clone())]),
            ],
            Term::ArrayIterator(Box::new(Term::Ref(t))),
            explicit_tuple_local1(
                a.clone(),
                a_ty,
                Term::Ref(tupled),
                Term::ArrIter(Box::new(Term::Ref(a))),
            ),
        )
    }

    fn map_iterator_type(self) -> Self {
        let t = Var::new("T");
        self.func(
            "NativeMapIterator",
            vec![type_param(t.clone())],
            Term::Univ,
            Term::MapIterator(Box::new(Term::Ref(t))),
        )
    }

    fn map_iterator_next(self) -> Self {
        let t = Var::new("T");
        let m = Var::new("m");
        let m_ty = Term::MapIterator(Box::new(Term::Ref(t.clone())));
        let (tupled, tele) = parameters([t.clone()], [(m.clone(), m_ty.clone())]);
        self.func(
            "mapIter#next",
            tele,
            option_type(Term::Ref(t)),
            explicit_tuple_local1(
                m.clone(),
                m_ty,
                tupled,
                Term::MapIterNext(Box::new(Term::Ref(m))),
            ),
        )
    }

    fn map_type(self) -> Self {
        let k = Var::new("K");
        let v = Var::new("V");
        self.func(
            "NativeMap",
            vec![type_param(k.clone()), type_param(v.clone())],
            Term::Univ,
            Term::Map(Box::new(Term::Ref(k)), Box::new(Term::Ref(v))),
        )
    }

    fn map_has(self) -> Self {
        let k = Var::new("K");
        let v = Var::new("V");
        let tupled = Var::tupled();
        let m = Var::new("m");
        let m_ty = Term::Map(
            Box::new(Term::Ref(k.clone())),
            Box::new(Term::Ref(v.clone())),
        );
        let m_rhs = m.untupled_rhs();
        let key = Var::new("k");
        let key_ty = Term::Ref(k.clone());
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
            Term::Boolean,
            explicit_tuple_local(
                (m.clone(), m_ty),
                (m_rhs.clone(), explicit_sigma1(key.clone(), key_ty.clone())),
                Term::Ref(tupled),
                explicit_tuple_local1(
                    key.clone(),
                    key_ty,
                    Term::Ref(m_rhs),
                    Term::MapHas(Box::new(Term::Ref(m)), Box::new(Term::Ref(key))),
                ),
            ),
        )
    }

    fn map_get(self) -> Self {
        let k = Var::new("K");
        let v = Var::new("V");
        let m = Var::new("m");
        let m_ty = Term::Map(
            Box::new(Term::Ref(k.clone())),
            Box::new(Term::Ref(v.clone())),
        );
        let m_rhs = m.untupled_rhs();
        let key = Var::new("k");
        let key_ty = Term::Ref(k.clone());
        let (tupled, tele) = parameters(
            [k, v.clone()],
            [(m.clone(), m_ty.clone()), (key.clone(), key_ty.clone())],
        );
        self.func(
            "map#get",
            tele,
            Term::Ref(v),
            explicit_tuple_local(
                (m.clone(), m_ty),
                (m_rhs.clone(), explicit_sigma1(key.clone(), key_ty.clone())),
                tupled,
                explicit_tuple_local1(
                    key.clone(),
                    key_ty,
                    Term::Ref(m_rhs),
                    Term::MapGet(Box::new(Term::Ref(m)), Box::new(Term::Ref(key))),
                ),
            ),
        )
    }

    fn map_set(self) -> Self {
        let k = Var::new("K");
        let v = Var::new("T");
        let m = Var::new("m");
        let m_ty = Term::Map(
            Box::new(Term::Ref(k.clone())),
            Box::new(Term::Ref(v.clone())),
        );
        let m_rhs = m.untupled_rhs();
        let key = Var::new("k");
        let key_ty = Term::Ref(k.clone());
        let key_rhs = key.untupled_rhs();
        let val = Var::new("v");
        let val_ty = Term::Ref(v.clone());
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
            Term::Unit,
            explicit_tuple_local(
                (m.clone(), m_ty),
                (
                    m_rhs.clone(),
                    explicit_sigma(
                        (key.clone(), key_ty.clone()),
                        explicit_sigma1(val.clone(), val_ty.clone()),
                    ),
                ),
                tupled,
                explicit_tuple_local(
                    (key.clone(), key_ty),
                    (
                        key_rhs.clone(),
                        explicit_sigma1(val.clone(), val_ty.clone()),
                    ),
                    Term::Ref(m_rhs),
                    explicit_tuple_local1(
                        val.clone(),
                        val_ty,
                        Term::Ref(key_rhs),
                        Term::MapSet(
                            Box::new(Term::Ref(m)),
                            Box::new(Term::Ref(key)),
                            Box::new(Term::Ref(val)),
                        ),
                    ),
                ),
            ),
        )
    }

    fn map_delete(self) -> Self {
        let k = Var::new("K");
        let v = Var::new("V");
        let m = Var::new("m");
        let m_ty = Term::Map(
            Box::new(Term::Ref(k.clone())),
            Box::new(Term::Ref(v.clone())),
        );
        let m_rhs = m.untupled_rhs();
        let key = Var::new("k");
        let key_ty = Term::Ref(k.clone());
        let (tupled, tele) = parameters(
            [k, v],
            [(m.clone(), m_ty.clone()), (key.clone(), key_ty.clone())],
        );
        self.func(
            "map#delete",
            tele,
            Term::Boolean,
            explicit_tuple_local(
                (m.clone(), m_ty),
                (m_rhs.clone(), explicit_sigma1(key.clone(), key_ty.clone())),
                tupled,
                explicit_tuple_local1(
                    key.clone(),
                    key_ty,
                    Term::Ref(m_rhs),
                    Term::MapDelete(Box::new(Term::Ref(m)), Box::new(Term::Ref(key))),
                ),
            ),
        )
    }

    fn map_clear(self) -> Self {
        let k = Var::new("K");
        let v = Var::new("V");
        let m = Var::new("m");
        let m_ty = Term::Map(
            Box::new(Term::Ref(k.clone())),
            Box::new(Term::Ref(v.clone())),
        );
        let (tupled, tele) = parameters([k.clone(), v.clone()], [(m.clone(), m_ty.clone())]);
        self.func(
            "map#clear",
            tele,
            Term::Unit,
            explicit_tuple_local1(
                m.clone(),
                m_ty,
                tupled,
                Term::MapClear(Box::new(Term::Ref(m))),
            ),
        )
    }

    fn map_iter(self) -> Self {
        let k = Var::new("K");
        let v = Var::new("V");
        let m = Var::new("m");
        let m_ty = Term::Map(
            Box::new(Term::Ref(k.clone())),
            Box::new(Term::Ref(v.clone())),
        );
        let (tupled, tele) = parameters([k.clone(), v.clone()], [(m.clone(), m_ty.clone())]);
        self.func(
            "map#iter",
            tele,
            Term::MapIterator(Box::new(entry_type(Term::Ref(k), Term::Ref(v)))),
            explicit_tuple_local1(
                m.clone(),
                m_ty,
                tupled,
                Term::MapIter(Box::new(Term::Ref(m))),
            ),
        )
    }
}
