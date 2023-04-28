use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Body, Def};
use crate::theory::ParamInfo::Explicit;
use crate::theory::{Loc, Param, Tele, Var};

fn tuple_args_body(args: Tele<Term>, mut body: Term) -> (Tele<Term>, Term) {
    let param_var = Var::tupled();
    let mut param_typ = Term::Unit;

    let mut untupled_params = Vec::default();
    for p in args.iter().rev() {
        let mut untupled = p.clone();
        untupled.var = untupled.var.untupled_rhs();
        untupled_params.push(untupled);
        param_typ = Term::Sigma(p.clone(), Box::new(param_typ));
    }
    let param = Param {
        var: param_var,
        info: Explicit,
        typ: Box::new(param_typ),
    };
    untupled_params.push(param.clone());

    for (i, lhs) in args.into_iter().rev().enumerate() {
        let rhs = untupled_params.get(i).unwrap();
        let tm = untupled_params.get(i + 1).unwrap();
        body = Term::TupleLet(
            lhs,
            rhs.clone(),
            Box::new(Term::Ref(tm.var.clone())),
            Box::new(body),
        );
    }

    (vec![param], body)
}

pub fn number_add() -> Def<Term> {
    let a = Var::new("a");
    let b = Var::new("b");
    let (tele, body) = tuple_args_body(
        vec![
            Param {
                var: a.clone(),
                info: Explicit,
                typ: Box::new(Term::Number),
            },
            Param {
                var: b.clone(),
                info: Explicit,
                typ: Box::new(Term::Number),
            },
        ],
        Term::NumAdd(Box::new(Term::Ref(a)), Box::new(Term::Ref(b))),
    );
    Def {
        loc: Loc::default(),
        name: Var::new("number#__add__"),
        tele,
        ret: Box::new(Term::Number),
        body: Body::Fn(body),
    }
}
