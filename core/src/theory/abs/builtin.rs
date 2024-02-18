use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Body, Def, Sigma};
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::VarKind;
use crate::theory::{NameMap, Param, ResolvedVar, Tele, Var};

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

fn tuple_params<const N: usize>(var: Var, tele: [Param<Term>; N]) -> Tele<Term> {
    let mut ty = Term::Unit;
    for x in tele.into_iter().rev() {
        ty = Term::Sigma(x, Box::new(ty));
    }
    vec![Param {
        var,
        info: Explicit,
        typ: Box::new(ty),
    }]
}

pub fn setup() -> (NameMap, Sigma) {
    let mut m = NameMap::default();
    let mut sigma = Sigma::default();

    insert_def(&mut m, &mut sigma, unionify());

    insert_def(&mut m, &mut sigma, reflect());

    insert_def(&mut m, &mut sigma, number_add());
    insert_def(&mut m, &mut sigma, number_sub());
    insert_def(&mut m, &mut sigma, number_eq());
    insert_def(&mut m, &mut sigma, number_neq());
    insert_def(&mut m, &mut sigma, number_le());
    insert_def(&mut m, &mut sigma, number_ge());
    insert_def(&mut m, &mut sigma, number_lt());
    insert_def(&mut m, &mut sigma, number_gt());

    insert_def(&mut m, &mut sigma, boolean_or());
    insert_def(&mut m, &mut sigma, boolean_and());
    insert_def(&mut m, &mut sigma, boolean_not());

    let array = array();
    let array_ref = Term::Ref(array.name.clone());
    insert_def(&mut m, &mut sigma, array);
    insert_def(&mut m, &mut sigma, array_length(array_ref.clone()));
    insert_def(&mut m, &mut sigma, array_push(array_ref.clone()));
    insert_def(&mut m, &mut sigma, array_foreach(array_ref));

    (m, sigma)
}

fn insert_def(ubiquitous: &mut NameMap, sigma: &mut Sigma, def: Def<Term>) {
    ubiquitous.insert(
        def.name.to_string(),
        ResolvedVar(VarKind::InModule, def.name.clone()),
    );
    sigma.insert(def.name.clone(), def);
}

fn unionify() -> Def<Term> {
    let r = Var::new("'R");
    let a_ty = Term::Enum(Box::new(Term::Ref(r.clone())));
    let tupled = Var::tupled();
    let mut tele = vec![implicit(r, Term::Row)];
    let tupled_tele = tuple_params(tupled.clone(), [explicit(Var::new("a"), a_ty.clone())]);
    let a = Var::new("a");
    let body = Body::Fn(Term::TupleLet(
        explicit(a.clone(), a_ty.clone()),
        explicit(Var::unbound(), Term::Unit),
        Box::new(Term::Ref(tupled)),
        Box::new(Term::Unionify(Box::new(Term::Ref(a)))),
    ));
    tele.extend(tupled_tele);
    Def {
        loc: Default::default(),
        name: Var::new("unionify"),
        tele,
        ret: Box::new(a_ty),
        body,
    }
}

fn reflect() -> Def<Term> {
    let t = Var::new("T");
    Def {
        loc: Default::default(),
        name: Var::new("Reflected"),
        tele: vec![implicit(t.clone(), Term::Univ)],
        ret: Box::new(Term::Univ),
        body: Body::Fn(Term::Reflected(Box::new(Term::Ref(t)))),
    }
}

fn number_add() -> Def<Term> {
    let tupled = Var::tupled();
    let untupled_a = Var::new("a");
    let untupled_a_rhs = untupled_a.untupled_rhs();
    let b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(untupled_a.clone(), Term::Number),
        explicit(
            untupled_a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(b.clone(), Term::Number),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(untupled_a_rhs)),
            Box::new(Term::NumAdd(
                Box::new(Term::Ref(untupled_a)),
                Box::new(Term::Ref(b.clone())),
            )),
        )),
    ));
    Def {
        loc: Default::default(),
        name: Var::new("number#__add__"),
        tele: tuple_params(
            tupled,
            [
                explicit(Var::new("a"), Term::Number),
                explicit(b, Term::Number),
            ],
        ),
        ret: Box::new(Term::Number),
        body,
    }
}

fn number_sub() -> Def<Term> {
    let tupled = Var::tupled();
    let untupled_a = Var::new("a");
    let untupled_a_rhs = untupled_a.untupled_rhs();
    let b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(untupled_a.clone(), Term::Number),
        explicit(
            untupled_a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(b.clone(), Term::Number),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(untupled_a_rhs)),
            Box::new(Term::NumSub(
                Box::new(Term::Ref(untupled_a)),
                Box::new(Term::Ref(b.clone())),
            )),
        )),
    ));
    Def {
        loc: Default::default(),
        name: Var::new("number#__sub__"),
        tele: tuple_params(
            tupled,
            [
                explicit(Var::new("a"), Term::Number),
                explicit(b, Term::Number),
            ],
        ),
        ret: Box::new(Term::Number),
        body,
    }
}

fn number_eq() -> Def<Term> {
    let tupled = Var::tupled();
    let a = Var::new("a");
    let a_rhs = a.untupled_rhs();
    let b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(a.clone(), Term::Number),
        explicit(
            a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(b.clone(), Term::Number),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(a_rhs)),
            Box::new(Term::NumEq(
                Box::new(Term::Ref(a)),
                Box::new(Term::Ref(b.clone())),
            )),
        )),
    ));
    Def {
        loc: Default::default(),
        name: Var::new("number#__eq__"),
        tele: tuple_params(
            tupled,
            [
                explicit(Var::new("a"), Term::Number),
                explicit(b, Term::Number),
            ],
        ),
        ret: Box::new(Term::Boolean),
        body,
    }
}

fn number_neq() -> Def<Term> {
    let tupled = Var::tupled();
    let a = Var::new("a");
    let a_rhs = a.untupled_rhs();
    let b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(a.clone(), Term::Number),
        explicit(
            a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(b.clone(), Term::Number),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(a_rhs)),
            Box::new(Term::NumNeq(
                Box::new(Term::Ref(a)),
                Box::new(Term::Ref(b.clone())),
            )),
        )),
    ));
    Def {
        loc: Default::default(),
        name: Var::new("number#__neq__"),
        tele: tuple_params(
            tupled,
            [
                explicit(Var::new("a"), Term::Number),
                explicit(b, Term::Number),
            ],
        ),
        ret: Box::new(Term::Boolean),
        body,
    }
}

fn number_le() -> Def<Term> {
    let tupled = Var::tupled();
    let a = Var::new("a");
    let a_rhs = a.untupled_rhs();
    let b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(a.clone(), Term::Number),
        explicit(
            a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(b.clone(), Term::Number),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(a_rhs)),
            Box::new(Term::NumLe(
                Box::new(Term::Ref(a)),
                Box::new(Term::Ref(b.clone())),
            )),
        )),
    ));
    Def {
        loc: Default::default(),
        name: Var::new("number#__le__"),
        tele: tuple_params(
            tupled,
            [
                explicit(Var::new("a"), Term::Number),
                explicit(b, Term::Number),
            ],
        ),
        ret: Box::new(Term::Boolean),
        body,
    }
}

fn number_ge() -> Def<Term> {
    let tupled = Var::tupled();
    let a = Var::new("a");
    let a_rhs = a.untupled_rhs();
    let b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(a.clone(), Term::Number),
        explicit(
            a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(b.clone(), Term::Number),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(a_rhs)),
            Box::new(Term::NumGe(
                Box::new(Term::Ref(a)),
                Box::new(Term::Ref(b.clone())),
            )),
        )),
    ));
    Def {
        loc: Default::default(),
        name: Var::new("number#__ge__"),
        tele: tuple_params(
            tupled,
            [
                explicit(Var::new("a"), Term::Number),
                explicit(b, Term::Number),
            ],
        ),
        ret: Box::new(Term::Boolean),
        body,
    }
}

fn number_lt() -> Def<Term> {
    let tupled = Var::tupled();
    let a = Var::new("a");
    let a_rhs = a.untupled_rhs();
    let b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(a.clone(), Term::Number),
        explicit(
            a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(b.clone(), Term::Number),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(a_rhs)),
            Box::new(Term::NumLt(
                Box::new(Term::Ref(a)),
                Box::new(Term::Ref(b.clone())),
            )),
        )),
    ));
    Def {
        loc: Default::default(),
        name: Var::new("number#__lt__"),
        tele: tuple_params(
            tupled,
            [
                explicit(Var::new("a"), Term::Number),
                explicit(b, Term::Number),
            ],
        ),
        ret: Box::new(Term::Boolean),
        body,
    }
}

fn number_gt() -> Def<Term> {
    let tupled = Var::tupled();
    let a = Var::new("a");
    let a_rhs = a.untupled_rhs();
    let b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(a.clone(), Term::Number),
        explicit(
            a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(b.clone(), Term::Number),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(a_rhs)),
            Box::new(Term::NumGt(
                Box::new(Term::Ref(a)),
                Box::new(Term::Ref(b.clone())),
            )),
        )),
    ));
    Def {
        loc: Default::default(),
        name: Var::new("number#__gt__"),
        tele: tuple_params(
            tupled,
            [
                explicit(Var::new("a"), Term::Number),
                explicit(b, Term::Number),
            ],
        ),
        ret: Box::new(Term::Boolean),
        body,
    }
}

fn boolean_or() -> Def<Term> {
    let tupled = Var::tupled();
    let a = Var::new("a");
    let a_rhs = a.untupled_rhs();
    let b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(a.clone(), Term::Boolean),
        explicit(
            a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Boolean), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(b.clone(), Term::Boolean),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(a_rhs)),
            Box::new(Term::BoolOr(
                Box::new(Term::Ref(a)),
                Box::new(Term::Ref(b.clone())),
            )),
        )),
    ));
    Def {
        loc: Default::default(),
        name: Var::new("boolean#__or__"),
        tele: tuple_params(
            tupled,
            [
                explicit(Var::new("a"), Term::Boolean),
                explicit(b, Term::Boolean),
            ],
        ),
        ret: Box::new(Term::Boolean),
        body,
    }
}

fn boolean_and() -> Def<Term> {
    let tupled = Var::tupled();
    let a = Var::new("a");
    let a_rhs = a.untupled_rhs();
    let b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(a.clone(), Term::Boolean),
        explicit(
            a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Boolean), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(b.clone(), Term::Boolean),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(a_rhs)),
            Box::new(Term::BoolAnd(
                Box::new(Term::Ref(a)),
                Box::new(Term::Ref(b.clone())),
            )),
        )),
    ));
    Def {
        loc: Default::default(),
        name: Var::new("boolean#__and__"),
        tele: tuple_params(
            tupled,
            [
                explicit(Var::new("a"), Term::Boolean),
                explicit(b, Term::Boolean),
            ],
        ),
        ret: Box::new(Term::Boolean),
        body,
    }
}

fn boolean_not() -> Def<Term> {
    let tupled = Var::tupled();
    let a = Var::new("a");
    let body = Body::Fn(Term::TupleLet(
        explicit(a.clone(), Term::Boolean),
        explicit(a.untupled_rhs(), Term::Unit),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::BoolNot(Box::new(Term::Ref(a.clone())))),
    ));
    Def {
        loc: Default::default(),
        name: Var::new("boolean#__not__"),
        tele: tuple_params(tupled, [explicit(a, Term::Boolean)]),
        ret: Box::new(Term::Boolean),
        body,
    }
}

fn array() -> Def<Term> {
    Def {
        loc: Default::default(),
        name: Var::new("NativeArray"),
        tele: Default::default(),
        ret: Box::new(Term::Univ),
        body: Body::Postulate,
    }
}

fn array_length(arr_typ: Term) -> Def<Term> {
    let tupled = Var::tupled();
    let a = Var::new("a");
    let a_rhs = Var::new("a").untupled_rhs();
    let body = Body::Fn(Term::TupleLet(
        explicit(a.clone(), arr_typ.clone()),
        explicit(a_rhs.clone(), Term::Unit),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::ArrLength(Box::new(Term::Ref(a.clone())))),
    ));
    Def {
        loc: Default::default(),
        name: Var::new("array#length"),
        tele: tuple_params(tupled, [explicit(a, arr_typ)]),
        ret: Box::new(Term::Number),
        body,
    }
}

fn array_push(arr_typ: Term) -> Def<Term> {
    let a = Var::new("a");
    let a_rhs = a.untupled_rhs();
    let v = Var::new("v");
    let t = Var::new("T");
    let v_ty = Term::Ref(t.clone());
    let tupled = Var::tupled();

    let mut tele = vec![implicit(t, Term::Univ)];
    let tupled_tele = tuple_params(
        tupled.clone(),
        [
            explicit(a.clone(), arr_typ.clone()),
            explicit(v.clone(), v_ty.clone()),
        ],
    );
    tele.extend(tupled_tele);

    let body = Body::Fn(Term::TupleLet(
        explicit(a.clone(), arr_typ),
        explicit(
            a_rhs.clone(),
            Term::Sigma(explicit(v.clone(), v_ty.clone()), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(v.clone(), v_ty),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(a_rhs)),
            Box::new(Term::ArrPush(
                Box::new(Term::Ref(a)),
                Box::new(Term::Ref(v)),
            )),
        )),
    ));

    Def {
        loc: Default::default(),
        name: Var::new("array#push"),
        tele,
        ret: Box::new(Term::Number),
        body,
    }
}

fn array_foreach(arr_typ: Term) -> Def<Term> {
    let a = Var::new("a");
    let a_rhs = a.untupled_rhs();
    let f = Var::new("f");
    let t = Var::new("T");
    let f_ty = Term::Pi(
        Param {
            var: Var::new("v"),
            info: Explicit,
            typ: Box::new(Term::Ref(t.clone())),
        },
        Box::new(Term::Unit),
    );
    let tupled = Var::tupled();

    let mut tele = vec![implicit(t, Term::Univ)];
    let tupled_tele = tuple_params(
        tupled.clone(),
        [
            explicit(a.clone(), arr_typ.clone()),
            explicit(f.clone(), f_ty.clone()),
        ],
    );
    tele.extend(tupled_tele);

    let body = Body::Fn(Term::TupleLet(
        explicit(a.clone(), arr_typ),
        explicit(
            a_rhs.clone(),
            Term::Sigma(explicit(f.clone(), f_ty.clone()), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(f.clone(), f_ty),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(a_rhs)),
            Box::new(Term::ArrForeach(
                Box::new(Term::Ref(a)),
                Box::new(Term::Ref(f)),
            )),
        )),
    ));

    Def {
        loc: Default::default(),
        name: Var::new("array#forEach"),
        tele,
        ret: Box::new(Term::Unit),
        body,
    }
}
