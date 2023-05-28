use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Body, Def};
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::{Param, Tele, Var};

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

pub fn all_builtins() -> [Def<Term>; 4] {
    [unionify(), reflect(), number_add(), number_sub()]
}

fn unionify() -> Def<Term> {
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
        name: Var::new("Reflect"),
        tele: vec![implicit(t.clone(), Term::Univ)],
        ret: Box::new(Term::Univ),
        body: Body::Fn(Term::Reflect(Box::new(Term::Ref(t)))),
    }
}

fn number_add() -> Def<Term> {
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
