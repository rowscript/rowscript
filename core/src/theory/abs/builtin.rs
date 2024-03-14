use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Body, Def, Sigma};
use crate::theory::conc::data::ArgInfo::UnnamedImplicit;
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::VarKind;
use crate::theory::{NameMap, Param, ResolvedVar, Var};

fn implicit(var: Var, typ: Term) -> Param<Term> {
    Param {
        var,
        info: Implicit,
        typ: Box::new(typ),
    }
}

fn explicit(var: Var, typ: Term) -> Param<Term> {
    Param {
        var,
        info: Explicit,
        typ: Box::new(typ),
    }
}

fn tuple_param<const N: usize>(var: Var, tele: [Param<Term>; N]) -> Param<Term> {
    let mut ty = Term::Unit;
    for x in tele.into_iter().rev() {
        ty = Term::Sigma(x, Box::new(ty));
    }
    Param {
        var,
        info: Explicit,
        typ: Box::new(ty),
    }
}

fn option_type(t: Term) -> Term {
    Term::Enum(Box::new(Term::Fields(
        [("Some".to_string(), t), ("None".to_string(), Term::Unit)]
            .into_iter()
            .collect(),
    )))
}

#[derive(Default)]
pub struct Builtins {
    pub ubiquitous: NameMap,
    pub sigma: Sigma,
}

impl Builtins {
    pub fn new() -> Self {
        Self::default()
            .unionify()
            .reflect()
            .number_add()
            .number_sub()
            .number_mod()
            .number_eq()
            .number_neq()
            .number_le()
            .number_ge()
            .number_lt()
            .number_gt()
            .boolean_or()
            .boolean_and()
            .boolean_not()
            .array_iterator_next()
            .array()
            .array_length()
            .array_push()
            .array_foreach()
            .array_at()
            .array_insert()
            .array_iterator()
            .array_iter()
    }

    fn insert(mut self, def: Def<Term>) -> Self {
        self.ubiquitous.insert(
            def.name.to_string(),
            ResolvedVar(VarKind::InModule, def.name.clone()),
        );
        self.sigma.insert(def.name.clone(), def);
        self
    }

    fn get(&self, s: &str) -> Term {
        let v = self.ubiquitous.get(s).unwrap().clone().1;
        self.sigma.get(&v).unwrap().to_term(v)
    }

    fn unionify(self) -> Self {
        let r = Var::new("'R");
        let a_ty = Term::Enum(Box::new(Term::Ref(r.clone())));
        let tupled = Var::tupled();
        let tele = vec![
            implicit(r, Term::Row),
            tuple_param(tupled.clone(), [explicit(Var::new("a"), a_ty.clone())]),
        ];
        let a = Var::new("a");
        let body = Body::Fn(Term::TupleLocal(
            explicit(a.clone(), a_ty.clone()),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(tupled)),
            Box::new(Term::Unionify(Box::new(Term::Ref(a)))),
        ));
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("unionify"),
            tele,
            ret: Box::new(a_ty),
            body,
        })
    }

    fn reflect(self) -> Self {
        let t = Var::new("T");
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("Reflected"),
            tele: vec![implicit(t.clone(), Term::Univ)],
            ret: Box::new(Term::Univ),
            body: Body::Fn(Term::Reflected(Box::new(Term::Ref(t)))),
        })
    }

    fn number_add(self) -> Self {
        let tupled = Var::tupled();
        let untupled_a = Var::new("a");
        let untupled_a_rhs = untupled_a.untupled_rhs();
        let b = Var::new("b");
        let body = Body::Fn(Term::TupleLocal(
            explicit(untupled_a.clone(), Term::Number),
            explicit(
                untupled_a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLocal(
                explicit(b.clone(), Term::Number),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(untupled_a_rhs)),
                Box::new(Term::NumAdd(
                    Box::new(Term::Ref(untupled_a)),
                    Box::new(Term::Ref(b.clone())),
                )),
            )),
        ));
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("number#__add__"),
            tele: vec![tuple_param(
                tupled,
                [
                    explicit(Var::new("a"), Term::Number),
                    explicit(b, Term::Number),
                ],
            )],
            ret: Box::new(Term::Number),
            body,
        })
    }

    fn number_sub(self) -> Self {
        let tupled = Var::tupled();
        let untupled_a = Var::new("a");
        let untupled_a_rhs = untupled_a.untupled_rhs();
        let b = Var::new("b");
        let body = Body::Fn(Term::TupleLocal(
            explicit(untupled_a.clone(), Term::Number),
            explicit(
                untupled_a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLocal(
                explicit(b.clone(), Term::Number),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(untupled_a_rhs)),
                Box::new(Term::NumSub(
                    Box::new(Term::Ref(untupled_a)),
                    Box::new(Term::Ref(b.clone())),
                )),
            )),
        ));
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("number#__sub__"),
            tele: vec![tuple_param(
                tupled,
                [
                    explicit(Var::new("a"), Term::Number),
                    explicit(b, Term::Number),
                ],
            )],
            ret: Box::new(Term::Number),
            body,
        })
    }

    fn number_mod(self) -> Self {
        let tupled = Var::tupled();
        let untupled_a = Var::new("a");
        let untupled_a_rhs = untupled_a.untupled_rhs();
        let b = Var::new("b");
        let body = Body::Fn(Term::TupleLocal(
            explicit(untupled_a.clone(), Term::Number),
            explicit(
                untupled_a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLocal(
                explicit(b.clone(), Term::Number),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(untupled_a_rhs)),
                Box::new(Term::NumMod(
                    Box::new(Term::Ref(untupled_a)),
                    Box::new(Term::Ref(b.clone())),
                )),
            )),
        ));
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("number#__mod__"),
            tele: vec![tuple_param(
                tupled,
                [
                    explicit(Var::new("a"), Term::Number),
                    explicit(b, Term::Number),
                ],
            )],
            ret: Box::new(Term::Number),
            body,
        })
    }

    fn number_eq(self) -> Self {
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_rhs = a.untupled_rhs();
        let b = Var::new("b");
        let body = Body::Fn(Term::TupleLocal(
            explicit(a.clone(), Term::Number),
            explicit(
                a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLocal(
                explicit(b.clone(), Term::Number),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(a_rhs)),
                Box::new(Term::NumEq(
                    Box::new(Term::Ref(a)),
                    Box::new(Term::Ref(b.clone())),
                )),
            )),
        ));
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("number#__eq__"),
            tele: vec![tuple_param(
                tupled,
                [
                    explicit(Var::new("a"), Term::Number),
                    explicit(b, Term::Number),
                ],
            )],
            ret: Box::new(Term::Boolean),
            body,
        })
    }

    fn number_neq(self) -> Self {
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_rhs = a.untupled_rhs();
        let b = Var::new("b");
        let body = Body::Fn(Term::TupleLocal(
            explicit(a.clone(), Term::Number),
            explicit(
                a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLocal(
                explicit(b.clone(), Term::Number),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(a_rhs)),
                Box::new(Term::NumNeq(
                    Box::new(Term::Ref(a)),
                    Box::new(Term::Ref(b.clone())),
                )),
            )),
        ));
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("number#__neq__"),
            tele: vec![tuple_param(
                tupled,
                [
                    explicit(Var::new("a"), Term::Number),
                    explicit(b, Term::Number),
                ],
            )],
            ret: Box::new(Term::Boolean),
            body,
        })
    }

    fn number_le(self) -> Self {
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_rhs = a.untupled_rhs();
        let b = Var::new("b");
        let body = Body::Fn(Term::TupleLocal(
            explicit(a.clone(), Term::Number),
            explicit(
                a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLocal(
                explicit(b.clone(), Term::Number),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(a_rhs)),
                Box::new(Term::NumLe(
                    Box::new(Term::Ref(a)),
                    Box::new(Term::Ref(b.clone())),
                )),
            )),
        ));
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("number#__le__"),
            tele: vec![tuple_param(
                tupled,
                [
                    explicit(Var::new("a"), Term::Number),
                    explicit(b, Term::Number),
                ],
            )],
            ret: Box::new(Term::Boolean),
            body,
        })
    }

    fn number_ge(self) -> Self {
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_rhs = a.untupled_rhs();
        let b = Var::new("b");
        let body = Body::Fn(Term::TupleLocal(
            explicit(a.clone(), Term::Number),
            explicit(
                a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLocal(
                explicit(b.clone(), Term::Number),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(a_rhs)),
                Box::new(Term::NumGe(
                    Box::new(Term::Ref(a)),
                    Box::new(Term::Ref(b.clone())),
                )),
            )),
        ));
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("number#__ge__"),
            tele: vec![tuple_param(
                tupled,
                [
                    explicit(Var::new("a"), Term::Number),
                    explicit(b, Term::Number),
                ],
            )],
            ret: Box::new(Term::Boolean),
            body,
        })
    }

    fn number_lt(self) -> Self {
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_rhs = a.untupled_rhs();
        let b = Var::new("b");
        let body = Body::Fn(Term::TupleLocal(
            explicit(a.clone(), Term::Number),
            explicit(
                a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLocal(
                explicit(b.clone(), Term::Number),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(a_rhs)),
                Box::new(Term::NumLt(
                    Box::new(Term::Ref(a)),
                    Box::new(Term::Ref(b.clone())),
                )),
            )),
        ));
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("number#__lt__"),
            tele: vec![tuple_param(
                tupled,
                [
                    explicit(Var::new("a"), Term::Number),
                    explicit(b, Term::Number),
                ],
            )],
            ret: Box::new(Term::Boolean),
            body,
        })
    }

    fn number_gt(self) -> Self {
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_rhs = a.untupled_rhs();
        let b = Var::new("b");
        let body = Body::Fn(Term::TupleLocal(
            explicit(a.clone(), Term::Number),
            explicit(
                a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLocal(
                explicit(b.clone(), Term::Number),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(a_rhs)),
                Box::new(Term::NumGt(
                    Box::new(Term::Ref(a)),
                    Box::new(Term::Ref(b.clone())),
                )),
            )),
        ));
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("number#__gt__"),
            tele: vec![tuple_param(
                tupled,
                [
                    explicit(Var::new("a"), Term::Number),
                    explicit(b, Term::Number),
                ],
            )],
            ret: Box::new(Term::Boolean),
            body,
        })
    }

    fn boolean_or(self) -> Self {
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_rhs = a.untupled_rhs();
        let b = Var::new("b");
        let body = Body::Fn(Term::TupleLocal(
            explicit(a.clone(), Term::Boolean),
            explicit(
                a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Boolean), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLocal(
                explicit(b.clone(), Term::Boolean),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(a_rhs)),
                Box::new(Term::BoolOr(
                    Box::new(Term::Ref(a)),
                    Box::new(Term::Ref(b.clone())),
                )),
            )),
        ));
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("boolean#__or__"),
            tele: vec![tuple_param(
                tupled,
                [
                    explicit(Var::new("a"), Term::Boolean),
                    explicit(b, Term::Boolean),
                ],
            )],
            ret: Box::new(Term::Boolean),
            body,
        })
    }

    fn boolean_and(self) -> Self {
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_rhs = a.untupled_rhs();
        let b = Var::new("b");
        let body = Body::Fn(Term::TupleLocal(
            explicit(a.clone(), Term::Boolean),
            explicit(
                a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Boolean), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLocal(
                explicit(b.clone(), Term::Boolean),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(a_rhs)),
                Box::new(Term::BoolAnd(
                    Box::new(Term::Ref(a)),
                    Box::new(Term::Ref(b.clone())),
                )),
            )),
        ));
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("boolean#__and__"),
            tele: vec![tuple_param(
                tupled,
                [
                    explicit(Var::new("a"), Term::Boolean),
                    explicit(b, Term::Boolean),
                ],
            )],
            ret: Box::new(Term::Boolean),
            body,
        })
    }

    fn boolean_not(self) -> Self {
        let tupled = Var::tupled();
        let a = Var::new("a");
        let body = Body::Fn(Term::TupleLocal(
            explicit(a.clone(), Term::Boolean),
            explicit(a.untupled_rhs(), Term::Unit),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::BoolNot(Box::new(Term::Ref(a.clone())))),
        ));
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("boolean#__not__"),
            tele: vec![tuple_param(tupled, [explicit(a, Term::Boolean)])],
            ret: Box::new(Term::Boolean),
            body,
        })
    }

    fn array_iterator(self) -> Self {
        let t = Var::new("T");
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("NativeArrayIterator"),
            tele: vec![implicit(t.clone(), Term::Univ)],
            ret: Box::new(Term::Univ),
            body: Body::Fn(Term::ArrayIterator(Box::new(Term::Ref(t.clone())))),
        })
    }

    fn array_iterator_next(self) -> Self {
        let t = Var::new("T");
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_ty = Term::ArrayIterator(Box::new(Term::Ref(t.clone())));
        let a_rhs = Var::new("a").untupled_rhs();
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("arrayIter#next"),
            tele: vec![
                implicit(t.clone(), Term::Univ),
                tuple_param(tupled.clone(), [explicit(a.clone(), a_ty.clone())]),
            ],
            ret: Box::new(option_type(Term::Ref(t))),
            body: Body::Fn(Term::TupleLocal(
                explicit(a.clone(), a_ty.clone()),
                explicit(a_rhs.clone(), Term::Unit),
                Box::new(Term::Ref(tupled)),
                Box::new(Term::ArrIterNext(Box::new(Term::Ref(a.clone())))),
            )),
        })
    }

    fn array(self) -> Self {
        let t = Var::new("T");
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("NativeArray"),
            tele: vec![implicit(t.clone(), Term::Univ)],
            ret: Box::new(Term::Univ),
            body: Body::Fn(Term::Array(Box::new(Term::Ref(t.clone())))),
        })
    }

    fn array_length(self) -> Self {
        let t = Var::new("T");
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_ty = Term::Array(Box::new(Term::Ref(t.clone())));
        let a_rhs = Var::new("a").untupled_rhs();
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("array#length"),
            tele: vec![
                implicit(t, Term::Univ),
                tuple_param(tupled.clone(), [explicit(a.clone(), a_ty.clone())]),
            ],
            ret: Box::new(Term::Number),
            body: Body::Fn(Term::TupleLocal(
                explicit(a.clone(), a_ty.clone()),
                explicit(a_rhs.clone(), Term::Unit),
                Box::new(Term::Ref(tupled)),
                Box::new(Term::ArrLength(Box::new(Term::Ref(a.clone())))),
            )),
        })
    }

    fn array_push(self) -> Self {
        let t = Var::new("T");
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_ty = Term::Array(Box::new(Term::Ref(t.clone())));
        let a_rhs = a.untupled_rhs();
        let v = Var::new("v");
        let v_ty = Term::Ref(t.clone());
        let params = [
            explicit(a.clone(), a_ty.clone()),
            explicit(v.clone(), v_ty.clone()),
        ];
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("array#push"),
            tele: vec![implicit(t, Term::Univ), tuple_param(tupled.clone(), params)],
            ret: Box::new(Term::Number),
            body: Body::Fn(Term::TupleLocal(
                explicit(a.clone(), a_ty),
                explicit(
                    a_rhs.clone(),
                    Term::Sigma(explicit(v.clone(), v_ty.clone()), Box::new(Term::Unit)),
                ),
                Box::new(Term::Ref(tupled)),
                Box::new(Term::TupleLocal(
                    explicit(v.clone(), v_ty),
                    explicit(Var::unbound(), Term::Unit),
                    Box::new(Term::Ref(a_rhs)),
                    Box::new(Term::ArrPush(
                        Box::new(Term::Ref(a)),
                        Box::new(Term::Ref(v)),
                    )),
                )),
            )),
        })
    }

    fn array_foreach(self) -> Self {
        let t = Var::new("T");
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_ty = Term::Array(Box::new(Term::Ref(t.clone())));
        let a_rhs = a.untupled_rhs();
        let f = Var::new("f");
        let f_ty = Term::Pi(
            tuple_param(
                Var::unbound(),
                [explicit(Var::new("v"), Term::Ref(t.clone()))],
            ),
            Box::new(Term::Unit),
        );
        let params = [
            explicit(a.clone(), a_ty.clone()),
            explicit(f.clone(), f_ty.clone()),
        ];
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("array#forEach"),
            tele: vec![implicit(t, Term::Univ), tuple_param(tupled.clone(), params)],
            ret: Box::new(Term::Unit),
            body: Body::Fn(Term::TupleLocal(
                explicit(a.clone(), a_ty),
                explicit(
                    a_rhs.clone(),
                    Term::Sigma(explicit(f.clone(), f_ty.clone()), Box::new(Term::Unit)),
                ),
                Box::new(Term::Ref(tupled)),
                Box::new(Term::TupleLocal(
                    explicit(f.clone(), f_ty),
                    explicit(Var::unbound(), Term::Unit),
                    Box::new(Term::Ref(a_rhs)),
                    Box::new(Term::ArrForeach(
                        Box::new(Term::Ref(a)),
                        Box::new(Term::Ref(f)),
                    )),
                )),
            )),
        })
    }

    fn array_at(self) -> Self {
        let t = Var::new("T");
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_ty = Term::Array(Box::new(Term::Ref(t.clone())));
        let a_rhs = a.untupled_rhs();
        let i = Var::new("i");
        let i_ty = Term::Number;
        let params = [
            explicit(a.clone(), a_ty.clone()),
            explicit(i.clone(), i_ty.clone()),
        ];
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("array#at"),
            tele: vec![
                implicit(t.clone(), Term::Univ),
                tuple_param(tupled.clone(), params),
            ],
            ret: Box::new(option_type(Term::Ref(t))),
            body: Body::Fn(Term::TupleLocal(
                explicit(a.clone(), a_ty),
                explicit(
                    a_rhs.clone(),
                    Term::Sigma(explicit(i.clone(), i_ty.clone()), Box::new(Term::Unit)),
                ),
                Box::new(Term::Ref(tupled)),
                Box::new(Term::TupleLocal(
                    explicit(i.clone(), i_ty),
                    explicit(Var::unbound(), Term::Unit),
                    Box::new(Term::Ref(a_rhs)),
                    Box::new(Term::ArrAt(Box::new(Term::Ref(a)), Box::new(Term::Ref(i)))),
                )),
            )),
        })
    }

    fn array_insert(self) -> Self {
        let t = Var::new("T");
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_ty = Term::Array(Box::new(Term::Ref(t.clone())));
        let a_rhs = a.untupled_rhs();
        let i = Var::new("i");
        let i_ty = Term::Number;
        let i_rhs = i.untupled_rhs();
        let v = Var::new("v");
        let v_ty = Term::Ref(t.clone());
        let params = [
            explicit(a.clone(), a_ty.clone()),
            explicit(i.clone(), i_ty.clone()),
            explicit(v.clone(), v_ty.clone()),
        ];
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("array#insert"),
            tele: vec![
                implicit(t.clone(), Term::Univ),
                tuple_param(tupled.clone(), params),
            ],
            ret: Box::new(Term::Unit),
            body: Body::Fn(Term::TupleLocal(
                explicit(a.clone(), a_ty),
                explicit(
                    a_rhs.clone(),
                    Term::Sigma(
                        explicit(i.clone(), i_ty.clone()),
                        Box::new(Term::Sigma(
                            explicit(v.clone(), v_ty.clone()),
                            Box::new(Term::Unit),
                        )),
                    ),
                ),
                Box::new(Term::Ref(tupled)),
                Box::new(Term::TupleLocal(
                    explicit(i.clone(), i_ty),
                    explicit(
                        i_rhs.clone(),
                        Term::Sigma(explicit(v.clone(), v_ty.clone()), Box::new(Term::Unit)),
                    ),
                    Box::new(Term::Ref(a_rhs)),
                    Box::new(Term::TupleLocal(
                        explicit(v.clone(), v_ty),
                        explicit(Var::unbound(), Term::Unit),
                        Box::new(Term::Ref(i_rhs)),
                        Box::new(Term::ArrInsert(
                            Box::new(Term::Ref(a)),
                            Box::new(Term::Ref(i)),
                            Box::new(Term::Ref(v)),
                        )),
                    )),
                )),
            )),
        })
    }

    fn array_iter(self) -> Self {
        let t = Var::new("T");
        let iterator = self.get("NativeArrayIterator");
        let ret = Box::new(Term::App(
            Box::new(iterator),
            UnnamedImplicit,
            Box::new(Term::Ref(t.clone())),
        ));
        let tupled = Var::tupled();
        let a = Var::new("a");
        let a_ty = Term::Array(Box::new(Term::Ref(t.clone())));
        let a_rhs = Var::new("a").untupled_rhs();
        self.insert(Def {
            loc: Default::default(),
            name: Var::new("array#iter"),
            tele: vec![
                implicit(t, Term::Univ),
                tuple_param(tupled.clone(), [explicit(a.clone(), a_ty.clone())]),
            ],
            ret,
            body: Body::Fn(Term::TupleLocal(
                explicit(a.clone(), a_ty.clone()),
                explicit(a_rhs.clone(), Term::Unit),
                Box::new(Term::Ref(tupled)),
                Box::new(Term::ArrIter(Box::new(Term::Ref(a.clone())))),
            )),
        })
    }
}
