use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Body, Def};
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::{Param, Tele, Var};

fn implicit_param(var: Var, typ: Term) -> Param<Term> {
    Param {
        var,
        info: Implicit,
        typ: Box::new(typ),
    }
}

fn explicit_param(var: Var, typ: Term) -> Param<Term> {
    Param {
        var,
        info: Explicit,
        typ: Box::new(typ),
    }
}

fn tuple_args_body(mut args: Tele<Term>, mut body: Term) -> (Tele<Term>, Term) {
    let param_var = Var::tupled();
    let mut param_typ = Term::Unit;

    for p in args.iter().rev() {
        param_typ = Term::Sigma(p.clone(), Box::new(param_typ));
    }
    args.push(Param {
        var: param_var.clone(),
        info: Explicit,
        typ: Box::new(Term::Unit),
    });
    args.reverse();

    for i in 0..args.len() - 1 {
        let lhs = args.get(i + 1).unwrap().clone();
        let mut rhs = args.get(i).unwrap().clone();
        let tm = Box::new(Term::Ref(rhs.var.clone()));
        rhs.var = lhs.var.untupled_rhs();
        body = Term::TupleLet(lhs, rhs, tm, Box::new(body));
    }

    (
        vec![Param {
            var: param_var,
            info: Explicit,
            typ: Box::new(param_typ),
        }],
        body,
    )
}

pub fn all_builtins() -> [Def<Term>; 3] {
    [unionify(), number_add(), number_sub()]
}

fn unionify() -> Def<Term> {
    let r = Var::new("'R");
    let a = Var::new("a");
    let mut tele = vec![implicit_param(r.clone(), Term::Row)];
    let (tupled_tele, body) = tuple_args_body(
        vec![explicit_param(
            a.clone(),
            Term::Enum(Box::new(Term::Ref(r.clone()))),
        )],
        Term::Unionify(Box::new(Term::Ref(a))),
    );
    tele.extend(tupled_tele);
    Def {
        loc: Default::default(),
        name: Var::new("unionify"),
        tele,
        ret: Box::new(Term::Enum(Box::new(Term::Ref(r)))),
        body: Body::Fn(body),
    }
}

fn number_add() -> Def<Term> {
    let a = Var::new("a");
    let b = Var::new("b");
    let (tele, body) = tuple_args_body(
        vec![
            explicit_param(a.clone(), Term::Number),
            explicit_param(b.clone(), Term::Number),
        ],
        Term::NumAdd(Box::new(Term::Ref(a)), Box::new(Term::Ref(b))),
    );
    Def {
        loc: Default::default(),
        name: Var::new("number#__add__"),
        tele,
        ret: Box::new(Term::Number),
        body: Body::Fn(body),
    }
}

fn number_sub() -> Def<Term> {
    let a = Var::new("a");
    let b = Var::new("b");
    let (tele, body) = tuple_args_body(
        vec![
            explicit_param(a.clone(), Term::Number),
            explicit_param(b.clone(), Term::Number),
        ],
        Term::NumSub(Box::new(Term::Ref(a)), Box::new(Term::Ref(b))),
    );
    Def {
        loc: Default::default(),
        name: Var::new("number#__sub__"),
        tele,
        ret: Box::new(Term::Number),
        body: Body::Fn(body),
    }
}
