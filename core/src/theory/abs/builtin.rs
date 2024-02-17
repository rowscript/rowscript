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
    insert_unionify(&mut m, &mut sigma);
    insert_reflect(&mut m, &mut sigma);
    insert_number_add(&mut m, &mut sigma);
    insert_number_sub(&mut m, &mut sigma);
    insert_number_eq(&mut m, &mut sigma);
    insert_number_neq(&mut m, &mut sigma);
    insert_number_le(&mut m, &mut sigma);
    insert_number_ge(&mut m, &mut sigma);
    insert_number_lt(&mut m, &mut sigma);
    insert_number_gt(&mut m, &mut sigma);
    insert_boolean_or(&mut m, &mut sigma);
    insert_boolean_and(&mut m, &mut sigma);
    insert_boolean_not(&mut m, &mut sigma);
    // insert_array_length(&mut m, &mut sigma);
    // insert_array_push(&mut m, &mut sigma);
    // insert_array_foreach(&mut m, &mut sigma);
    (m, sigma)
}

fn insert_def(ubiquitous: &mut NameMap, sigma: &mut Sigma, def: Def<Term>) {
    ubiquitous.insert(
        def.name.to_string(),
        ResolvedVar(VarKind::InModule, def.name.clone()),
    );
    sigma.insert(def.name.clone(), def);
}

fn insert_unionify(ubiquitous: &mut NameMap, sigma: &mut Sigma) {
    let r = Var::new("'R");
    let a_ty = Term::Enum(Box::new(Term::Ref(r.clone())));
    let tupled = Var::tupled();
    let mut tele = vec![implicit(r, Term::Row)];
    let tupled_tele = tuple_params(tupled.clone(), [explicit(Var::new("a"), a_ty.clone())]);
    let untupled_a = Var::new("a");
    let body = Body::Fn(Term::TupleLet(
        explicit(untupled_a.clone(), a_ty.clone()),
        explicit(Var::unbound(), Term::Unit),
        Box::new(Term::Ref(tupled)),
        Box::new(Term::Unionify(Box::new(Term::Ref(untupled_a)))),
    ));
    tele.extend(tupled_tele);
    insert_def(
        ubiquitous,
        sigma,
        Def {
            loc: Default::default(),
            name: Var::new("unionify"),
            tele,
            ret: Box::new(a_ty),
            body,
        },
    )
}

fn insert_reflect(ubiquitous: &mut NameMap, sigma: &mut Sigma) {
    let t = Var::new("T");
    insert_def(
        ubiquitous,
        sigma,
        Def {
            loc: Default::default(),
            name: Var::new("Reflected"),
            tele: vec![implicit(t.clone(), Term::Univ)],
            ret: Box::new(Term::Univ),
            body: Body::Fn(Term::Reflected(Box::new(Term::Ref(t)))),
        },
    )
}

fn insert_number_add(ubiquitous: &mut NameMap, sigma: &mut Sigma) {
    let b = Var::new("b");
    let tupled = Var::tupled();
    let untupled_a = Var::new("a");
    let untupled_a_rhs = Var::new("a").untupled_rhs();
    let untupled_b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(untupled_a.clone(), Term::Number),
        explicit(
            untupled_a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(untupled_b.clone(), Term::Number),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(untupled_a_rhs)),
            Box::new(Term::NumAdd(
                Box::new(Term::Ref(untupled_a)),
                Box::new(Term::Ref(untupled_b)),
            )),
        )),
    ));
    insert_def(
        ubiquitous,
        sigma,
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
        },
    )
}

fn insert_number_sub(ubiquitous: &mut NameMap, sigma: &mut Sigma) {
    let b = Var::new("b");
    let tupled = Var::tupled();
    let untupled_a = Var::new("a");
    let untupled_a_rhs = Var::new("a").untupled_rhs();
    let untupled_b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(untupled_a.clone(), Term::Number),
        explicit(
            untupled_a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(untupled_b.clone(), Term::Number),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(untupled_a_rhs)),
            Box::new(Term::NumSub(
                Box::new(Term::Ref(untupled_a)),
                Box::new(Term::Ref(untupled_b)),
            )),
        )),
    ));
    insert_def(
        ubiquitous,
        sigma,
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
        },
    )
}

fn insert_number_eq(ubiquitous: &mut NameMap, sigma: &mut Sigma) {
    let b = Var::new("b");
    let tupled = Var::tupled();
    let untupled_a = Var::new("a");
    let untupled_a_rhs = Var::new("a").untupled_rhs();
    let untupled_b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(untupled_a.clone(), Term::Number),
        explicit(
            untupled_a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(untupled_b.clone(), Term::Number),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(untupled_a_rhs)),
            Box::new(Term::NumEq(
                Box::new(Term::Ref(untupled_a)),
                Box::new(Term::Ref(untupled_b)),
            )),
        )),
    ));
    insert_def(
        ubiquitous,
        sigma,
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
        },
    )
}

fn insert_number_neq(ubiquitous: &mut NameMap, sigma: &mut Sigma) {
    let b = Var::new("b");
    let tupled = Var::tupled();
    let untupled_a = Var::new("a");
    let untupled_a_rhs = Var::new("a").untupled_rhs();
    let untupled_b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(untupled_a.clone(), Term::Number),
        explicit(
            untupled_a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(untupled_b.clone(), Term::Number),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(untupled_a_rhs)),
            Box::new(Term::NumNeq(
                Box::new(Term::Ref(untupled_a)),
                Box::new(Term::Ref(untupled_b)),
            )),
        )),
    ));
    insert_def(
        ubiquitous,
        sigma,
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
        },
    )
}

fn insert_number_le(ubiquitous: &mut NameMap, sigma: &mut Sigma) {
    let b = Var::new("b");
    let tupled = Var::tupled();
    let untupled_a = Var::new("a");
    let untupled_a_rhs = Var::new("a").untupled_rhs();
    let untupled_b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(untupled_a.clone(), Term::Number),
        explicit(
            untupled_a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(untupled_b.clone(), Term::Number),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(untupled_a_rhs)),
            Box::new(Term::NumLe(
                Box::new(Term::Ref(untupled_a)),
                Box::new(Term::Ref(untupled_b)),
            )),
        )),
    ));
    insert_def(
        ubiquitous,
        sigma,
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
        },
    )
}

fn insert_number_ge(ubiquitous: &mut NameMap, sigma: &mut Sigma) {
    let b = Var::new("b");
    let tupled = Var::tupled();
    let untupled_a = Var::new("a");
    let untupled_a_rhs = Var::new("a").untupled_rhs();
    let untupled_b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(untupled_a.clone(), Term::Number),
        explicit(
            untupled_a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(untupled_b.clone(), Term::Number),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(untupled_a_rhs)),
            Box::new(Term::NumGe(
                Box::new(Term::Ref(untupled_a)),
                Box::new(Term::Ref(untupled_b)),
            )),
        )),
    ));
    insert_def(
        ubiquitous,
        sigma,
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
        },
    )
}

fn insert_number_lt(ubiquitous: &mut NameMap, sigma: &mut Sigma) {
    let b = Var::new("b");
    let tupled = Var::tupled();
    let untupled_a = Var::new("a");
    let untupled_a_rhs = Var::new("a").untupled_rhs();
    let untupled_b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(untupled_a.clone(), Term::Number),
        explicit(
            untupled_a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(untupled_b.clone(), Term::Number),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(untupled_a_rhs)),
            Box::new(Term::NumLt(
                Box::new(Term::Ref(untupled_a)),
                Box::new(Term::Ref(untupled_b)),
            )),
        )),
    ));
    insert_def(
        ubiquitous,
        sigma,
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
        },
    )
}

fn insert_number_gt(ubiquitous: &mut NameMap, sigma: &mut Sigma) {
    let b = Var::new("b");
    let tupled = Var::tupled();
    let untupled_a = Var::new("a");
    let untupled_a_rhs = Var::new("a").untupled_rhs();
    let untupled_b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(untupled_a.clone(), Term::Number),
        explicit(
            untupled_a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(untupled_b.clone(), Term::Number),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(untupled_a_rhs)),
            Box::new(Term::NumGt(
                Box::new(Term::Ref(untupled_a)),
                Box::new(Term::Ref(untupled_b)),
            )),
        )),
    ));
    insert_def(
        ubiquitous,
        sigma,
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
        },
    )
}

fn insert_boolean_or(ubiquitous: &mut NameMap, sigma: &mut Sigma) {
    let b = Var::new("b");
    let tupled = Var::tupled();
    let untupled_a = Var::new("a");
    let untupled_a_rhs = Var::new("a").untupled_rhs();
    let untupled_b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(untupled_a.clone(), Term::Boolean),
        explicit(
            untupled_a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Boolean), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(untupled_b.clone(), Term::Boolean),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(untupled_a_rhs)),
            Box::new(Term::BoolOr(
                Box::new(Term::Ref(untupled_a)),
                Box::new(Term::Ref(untupled_b)),
            )),
        )),
    ));
    insert_def(
        ubiquitous,
        sigma,
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
        },
    )
}

fn insert_boolean_and(ubiquitous: &mut NameMap, sigma: &mut Sigma) {
    let b = Var::new("b");
    let tupled = Var::tupled();
    let untupled_a = Var::new("a");
    let untupled_a_rhs = Var::new("a").untupled_rhs();
    let untupled_b = Var::new("b");
    let body = Body::Fn(Term::TupleLet(
        explicit(untupled_a.clone(), Term::Boolean),
        explicit(
            untupled_a_rhs.clone(),
            Term::Sigma(explicit(b.clone(), Term::Boolean), Box::new(Term::Unit)),
        ),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::TupleLet(
            explicit(untupled_b.clone(), Term::Boolean),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(untupled_a_rhs)),
            Box::new(Term::BoolAnd(
                Box::new(Term::Ref(untupled_a)),
                Box::new(Term::Ref(untupled_b)),
            )),
        )),
    ));
    insert_def(
        ubiquitous,
        sigma,
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
        },
    )
}

fn insert_boolean_not(ubiquitous: &mut NameMap, sigma: &mut Sigma) {
    let tupled = Var::tupled();
    let untupled_a = Var::new("a");
    let untupled_a_rhs = Var::new("a").untupled_rhs();
    let body = Body::Fn(Term::TupleLet(
        explicit(untupled_a.clone(), Term::Boolean),
        explicit(untupled_a_rhs.clone(), Term::Unit),
        Box::new(Term::Ref(tupled.clone())),
        Box::new(Term::BoolNot(Box::new(Term::Ref(untupled_a)))),
    ));
    insert_def(
        ubiquitous,
        sigma,
        Def {
            loc: Default::default(),
            name: Var::new("boolean#__not__"),
            tele: tuple_params(tupled, [explicit(Var::new("a"), Term::Boolean)]),
            ret: Box::new(Term::Boolean),
            body,
        },
    )
}
