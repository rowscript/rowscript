use std::collections::HashMap;

use pest::iterators::{Pair, Pairs};

use crate::theory::abs::data::Dir;
use crate::theory::abs::def::Body;
use crate::theory::abs::def::Def;
use crate::theory::conc::data::ArgInfo::{NamedImplicit, UnnamedExplicit, UnnamedImplicit};
use crate::theory::conc::data::{ArgInfo, Expr};
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::{Loc, Param, Tele, Var};
use crate::Rule;

pub fn file(mut f: Pairs<Rule>) -> Vec<Def<Expr>> {
    let mut defs = Vec::default();
    for d in f.next().unwrap().into_inner() {
        match d.as_rule() {
            Rule::fn_def => defs.push(fn_def(d, None)),
            Rule::fn_postulate => defs.push(fn_postulate(d)),
            Rule::type_postulate => defs.push(type_postulate(d)),
            Rule::type_alias => defs.push(type_alias(d)),
            Rule::class_def => defs.extend(class_def(d)),
            Rule::interface_def => defs.extend(interface_def(d)),
            Rule::implements_def => defs.extend(implements_def(d)),
            Rule::EOI => break,
            _ => unreachable!(),
        }
    }
    defs
}

fn fn_def(f: Pair<Rule>, this: Option<(Expr, Tele<Expr>)>) -> Def<Expr> {
    use Body::*;
    use Expr::*;

    let loc = Loc::from(f.as_span());
    let mut pairs = f.into_inner();

    let name = Var::from(pairs.next().unwrap());

    let mut tele = Tele::default();
    let mut untupled = UntupledParams::new(loc);
    let mut preds = Tele::default();
    let mut ret = Box::new(Unit(loc));
    let mut body = None;

    if let Some((ty, implicits)) = this {
        untupled.push(
            loc,
            Param {
                var: Var::this(),
                info: Explicit,
                typ: Box::new(wrap_implicit_apps(&implicits, ty)),
            },
        );
        tele.extend(implicits);
    }

    for p in pairs {
        match p.as_rule() {
            Rule::row_id => tele.push(row_param(p)),
            Rule::implicit_id => tele.push(implicit_param(p)),
            Rule::hkt_param => tele.push(hkt_param(p)),
            Rule::param => untupled.push(Loc::from(p.as_span()), param(p)),
            Rule::type_expr => ret = Box::new(type_expr(p)),
            Rule::fn_body => {
                body = Some(fn_body(p));
                break;
            }
            Rule::pred => preds.push(pred(p)),
            _ => unreachable!(),
        }
    }
    let untupled_vars = untupled.unresolved();
    let untupled_loc = untupled.0;
    let tupled_param = Param::from(untupled);
    let body = Fn(Expr::wrap_tuple_lets(
        untupled_loc,
        &tupled_param.var,
        untupled_vars,
        body.unwrap(),
    ));
    tele.push(tupled_param);
    tele.extend(preds);

    Def {
        loc,
        name,
        tele,
        ret,
        body,
    }
}

fn fn_postulate(f: Pair<Rule>) -> Def<Expr> {
    use Body::*;
    use Expr::*;

    let loc = Loc::from(f.as_span());
    let mut pairs = f.into_inner();

    let name = Var::from(pairs.next().unwrap());

    let mut tele = Tele::default();
    let mut untupled = UntupledParams::new(loc);
    let mut ret = Box::new(Unit(loc));

    for p in pairs {
        match p.as_rule() {
            Rule::implicit_id => tele.push(implicit_param(p)),
            Rule::param => untupled.push(Loc::from(p.as_span()), param(p)),
            Rule::type_expr => ret = Box::new(type_expr(p)),
            _ => unreachable!(),
        }
    }
    tele.push(Param::from(untupled));

    Def {
        loc,
        name,
        tele,
        ret,
        body: Postulate,
    }
}

fn type_postulate(t: Pair<Rule>) -> Def<Expr> {
    use Body::*;
    use Expr::*;

    let loc = Loc::from(t.as_span());
    let name = Var::from(t.into_inner().next().unwrap());
    let ret = Box::new(Univ(loc));

    Def {
        loc,
        name,
        tele: Default::default(),
        ret,
        body: Postulate,
    }
}

fn type_alias(t: Pair<Rule>) -> Def<Expr> {
    use Body::*;
    use Expr::*;

    let loc = Loc::from(t.as_span());
    let mut pairs = t.into_inner();

    let name = Var::from(pairs.next().unwrap());
    let mut tele = Tele::default();
    let mut target = None;
    for p in pairs {
        match p.as_rule() {
            Rule::row_id => tele.push(row_param(p)),
            Rule::implicit_id => tele.push(implicit_param(p)),
            Rule::type_expr => target = Some(type_expr(p)),
            _ => unreachable!(),
        }
    }

    Def {
        loc,
        name,
        tele,
        ret: Box::new(Univ(loc)),
        body: Alias(target.unwrap()),
    }
}

fn wrap_implicit_apps(implicits: &Tele<Expr>, mut e: Expr) -> Expr {
    use Expr::*;
    for p in implicits {
        let loc = p.typ.loc();
        e = App(
            loc,
            Box::new(e),
            UnnamedImplicit,
            Box::new(Unresolved(loc, p.var.clone())),
        );
    }
    e
}

fn class_def(c: Pair<Rule>) -> Vec<Def<Expr>> {
    use Body::*;
    use Expr::*;

    let loc = Loc::from(c.as_span());
    let mut pairs = c.into_inner();

    let name = Var::from(pairs.next().unwrap());
    let vptr_name = name.vptr_type();
    let vptr_ctor_name = name.vptr_ctor();
    let ctor_name = name.ctor();
    let vtbl_name = name.vtbl_type();
    let vtbl_lookup_name = name.vtbl_lookup();

    let mut tele = Tele::default();
    let mut members = Vec::default();
    let mut method_defs = Vec::default();
    let mut methods = Vec::default();

    let mut vtbl_fields = Vec::default();
    for p in pairs {
        match p.as_rule() {
            Rule::implicit_id => tele.push(implicit_param(p)),
            Rule::class_member => {
                let loc = Loc::from(p.as_span());
                let mut p = p.into_inner();
                members.push((
                    loc,
                    Param {
                        var: Var::from(p.next().unwrap()),
                        info: Explicit,
                        typ: Box::new(type_expr(p.next().unwrap())),
                    },
                ));
            }
            Rule::class_method => {
                let mut m = fn_def(p, Some((Unresolved(loc, name.clone()), tele.clone())));
                vtbl_fields.push((m.name.to_string(), m.to_type()));

                let meth_name = m.name.to_string();
                let fn_name = name.method(m.name);
                m.name = fn_name.clone();

                m.body = match m.body {
                    Fn(f) => Method(f),
                    _ => unreachable!(),
                };

                methods.push((meth_name, fn_name));
                method_defs.push(m);
            }
            _ => unreachable!(),
        }
    }

    let vptr_def = Def {
        loc,
        name: vptr_name.clone(),
        tele: tele.clone(),
        ret: Box::new(Univ(loc)),
        body: VptrType(Vptr(
            loc,
            vtbl_lookup_name.clone(),
            tele.iter()
                .map(|p| Unresolved(loc, p.var.clone()))
                .collect(),
        )),
    };
    let vptr_ctor_def = Def {
        loc,
        name: vptr_ctor_name.clone(),
        tele: tele.clone(),
        ret: Box::new(wrap_implicit_apps(
            &tele,
            Unresolved(loc, vptr_name.clone()),
        )),
        body: VptrCtor(name.to_string()),
    };

    let mut ctor_untupled = UntupledParams::new(loc);
    let mut ty_fields = Vec::default();
    let mut tm_fields = Vec::default();
    for (loc, m) in members {
        ty_fields.push((m.var.to_string(), *m.typ.clone()));
        tm_fields.push((m.var.to_string(), Unresolved(loc, m.var.clone())));
        ctor_untupled.push(loc, m)
    }
    ty_fields.push((
        Var::vptr().to_string(),
        wrap_implicit_apps(&tele, Unresolved(loc, name.vptr_type())),
    ));
    tm_fields.push((
        Var::vptr().to_string(),
        wrap_implicit_apps(&tele, Unresolved(loc, name.vptr_ctor())),
    ));
    let object = Object(loc, Box::new(Fields(loc, ty_fields)));

    let untupled_vars = ctor_untupled.unresolved();
    let untupled_loc = ctor_untupled.0;
    let tupled_param = Param::from(ctor_untupled);
    let ctor_body = Ctor(Expr::wrap_tuple_lets(
        untupled_loc,
        &tupled_param.var,
        untupled_vars,
        Obj(loc, Box::new(Fields(loc, tm_fields))),
    ));
    let mut ctor_tele = tele.clone();
    ctor_tele.push(tupled_param);
    let ctor_def = Def {
        loc,
        name: ctor_name.clone(),
        tele: ctor_tele,
        ret: Box::new(Unresolved(loc, name.clone())),
        body: ctor_body,
    };

    let body = Class {
        object,
        methods,
        ctor: ctor_name,
        vptr: vptr_name.clone(),
        vptr_ctor: vptr_ctor_name,
        vtbl: vtbl_name.clone(),
        vtbl_lookup: vtbl_lookup_name.clone(),
    };

    let cls_def = Def {
        loc,
        name,
        tele: tele.clone(),
        ret: Box::new(Univ(loc)),
        body,
    };

    let vtbl_def = Def {
        loc,
        name: vtbl_name.clone(),
        tele: tele.clone(),
        ret: Box::new(Univ(loc)),
        body: VtblType(Object(loc, Box::new(Fields(loc, vtbl_fields)))),
    };
    let mut lookup_tele = tele.clone();
    lookup_tele.push(Param {
        var: Var::new("vp"),
        info: Explicit,
        typ: Box::new(wrap_implicit_apps(&tele, Unresolved(loc, vptr_name))),
    });
    let vtbl_lookup_def = Def {
        loc,
        name: vtbl_lookup_name,
        tele: lookup_tele,
        ret: Box::new(wrap_implicit_apps(&tele, Unresolved(loc, vtbl_name))),
        body: VtblLookup,
    };

    let mut defs = vec![
        vptr_def,
        vptr_ctor_def,
        cls_def,
        ctor_def,
        vtbl_def,
        vtbl_lookup_def,
    ];
    defs.extend(method_defs);
    defs
}

fn interface_def(i: Pair<Rule>) -> Vec<Def<Expr>> {
    fn alias_type(loc: Loc, tele: &Tele<Expr>) -> Expr {
        Expr::pi(tele, Univ(loc))
    }

    use Body::*;
    use Expr::*;

    let loc = Loc::from(i.as_span());
    let mut pairs = i.into_inner();

    let name_pair = pairs.next().unwrap();
    let ret = Box::new(Univ(Loc::from(name_pair.as_span())));
    let name = Var::from(name_pair);

    let alias_pair = pairs.next().unwrap();
    let alias_loc = Loc::from(alias_pair.as_span());
    let alias = Var::from(alias_pair);

    let mut im_tele = Tele::default();
    let mut fn_defs = Vec::default();
    let mut fns = Vec::default();
    for p in pairs {
        match p.as_rule() {
            Rule::row_id => im_tele.push(row_param(p)),
            Rule::implicit_id => im_tele.push(implicit_param(p)),
            Rule::interface_fn => {
                let mut d = fn_postulate(p);
                let mut tele = vec![Param {
                    var: alias.clone(),
                    info: Implicit,
                    typ: Box::new(alias_type(alias_loc, &im_tele)),
                }];
                tele.extend(d.tele);
                d.tele = tele;

                d.body = Findable(name.clone());
                fns.push(d.name.clone());
                fn_defs.push(d);
            }
            _ => unreachable!(),
        }
    }

    let mut defs = vec![Def {
        loc,
        name,
        tele: vec![Param {
            var: alias,
            info: Implicit,
            typ: Box::new(alias_type(alias_loc, &im_tele)),
        }],
        ret,
        body: Interface {
            fns,
            ims: Default::default(),
        },
    }];
    defs.extend(fn_defs);
    defs
}

fn implements_def(i: Pair<Rule>) -> Vec<Def<Expr>> {
    use Body::*;
    use Expr::*;

    let loc = Loc::from(i.as_span());
    let mut pairs = i.into_inner();

    let mut defs = Vec::default();

    let i = Var::from(pairs.next().unwrap());
    let im = Var::from(pairs.next().unwrap());

    let mut fns = HashMap::default();
    for p in pairs {
        let mut def = fn_def(p, None);
        let fn_name = def.name.implement_func(&i, &im);
        fns.insert(def.name.clone(), fn_name.clone());
        def.name = fn_name;
        def.body = match def.body {
            Fn(f) => ImplementsFn(f),
            _ => unreachable!(),
        };
        defs.push(def);
    }

    defs.push(Def {
        loc,
        name: i.implements(&im),
        tele: Default::default(),
        ret: Box::new(Univ(loc)),
        body: Implements { i: (i, im), fns },
    });
    defs
}

fn type_expr(t: Pair<Rule>) -> Expr {
    use Expr::*;

    let p = t.into_inner().next().unwrap();
    let loc = Loc::from(p.as_span());
    match p.as_rule() {
        Rule::fn_type => {
            let ps = p.into_inner();
            let mut untupled = UntupledParams::new(loc);
            for fp in ps {
                match fp.as_rule() {
                    Rule::param => untupled.push(Loc::from(fp.as_span()), param(fp)),
                    Rule::type_expr => {
                        return Pi(loc, Param::from(untupled), Box::new(type_expr(fp)));
                    }
                    _ => unreachable!(),
                }
            }
            unreachable!()
        }
        Rule::string_type => String(loc),
        Rule::number_type => Number(loc),
        Rule::bigint_type => BigInt(loc),
        Rule::boolean_type => Boolean(loc),
        Rule::unit_type => Unit(loc),
        Rule::object_type_ref => Object(loc, Box::new(unresolved(p.into_inner().next().unwrap()))),
        Rule::object_type_literal => Object(loc, Box::new(fields(p))),
        Rule::enum_type_ref => Enum(loc, Box::new(unresolved(p.into_inner().next().unwrap()))),
        Rule::enum_type_literal => Enum(loc, Box::new(fields(p))),
        Rule::type_app => type_app(p),
        Rule::tyref => unresolved(p),
        Rule::paren_type_expr => type_expr(p.into_inner().next().unwrap()),
        Rule::hole => Hole(loc),
        _ => unreachable!(),
    }
}

fn type_app(a: Pair<Rule>) -> Expr {
    use Expr::*;

    let mut pairs = a.into_inner();
    let f = pairs.next().unwrap();
    let f = match f.as_rule() {
        Rule::type_expr => type_expr(f),
        Rule::tyref => unresolved(f),
        _ => unreachable!(),
    };

    pairs
        .map(|arg| {
            let loc = Loc::from(arg.as_span());
            let (i, e) = match arg.as_rule() {
                Rule::row_arg => row_arg(arg),
                Rule::type_arg => type_arg(arg),
                _ => unreachable!(),
            };
            (loc, i, e)
        })
        .fold(f, |a, (loc, i, x)| App(loc, Box::new(a), i, Box::new(x)))
}

fn pred(pred: Pair<Rule>) -> Param<Expr> {
    use Expr::*;

    let p = pred.into_inner().next().unwrap();
    let loc = Loc::from(p.as_span());
    Param {
        var: Var::unbound(),
        info: Implicit,
        typ: match p.as_rule() {
            Rule::row_ord => {
                let mut p = p.into_inner();
                let lhs = row_expr(p.next().unwrap());
                let dir = p.next().unwrap();
                let dir = match dir.as_rule() {
                    Rule::row_le => Dir::Le,
                    Rule::row_ge => Dir::Ge,
                    _ => unreachable!(),
                };
                let rhs = row_expr(p.next().unwrap());
                Box::new(RowOrd(loc, Box::new(lhs), dir, Box::new(rhs)))
            }
            Rule::row_eq => {
                let mut p = p.into_inner();
                let lhs = row_expr(p.next().unwrap());
                let rhs = row_expr(p.next().unwrap());
                Box::new(RowEq(loc, Box::new(lhs), Box::new(rhs)))
            }
            Rule::constraint_expr => Box::new(ImplementsOf(loc, Box::new(type_app(p)))),
            _ => unreachable!(),
        },
    }
}

fn row_expr(e: Pair<Rule>) -> Expr {
    use Expr::*;

    let p = e.into_inner().next().unwrap();
    let loc = Loc::from(p.as_span());
    match p.as_rule() {
        Rule::row_concat => {
            let mut p = p.into_inner();
            let lhs = row_primary_expr(p.next().unwrap());
            let rhs = row_expr(p.next().unwrap());
            Combine(loc, Box::new(lhs), Box::new(rhs))
        }
        Rule::row_primary_expr => row_primary_expr(p),
        _ => unreachable!(),
    }
}

fn row_primary_expr(e: Pair<Rule>) -> Expr {
    let p = e.into_inner().next().unwrap();
    match p.as_rule() {
        Rule::row_id => unresolved(p),
        Rule::paren_fields => fields(p),
        Rule::paren_row_expr => row_expr(p.into_inner().next().unwrap()),
        _ => unreachable!(),
    }
}

fn type_arg(a: Pair<Rule>) -> (ArgInfo, Expr) {
    let mut p = a.into_inner();
    let id_or_type = p.next().unwrap();
    match id_or_type.as_rule() {
        Rule::type_expr => (UnnamedImplicit, type_expr(id_or_type)),
        Rule::tyref => (
            NamedImplicit(id_or_type.as_str().to_string()),
            type_expr(p.next().unwrap()),
        ),
        _ => unreachable!(),
    }
}

fn row_arg(a: Pair<Rule>) -> (ArgInfo, Expr) {
    let mut p = a.into_inner();
    let id_or_fields = p.next().unwrap();
    match id_or_fields.as_rule() {
        Rule::paren_fields => (UnnamedImplicit, fields(id_or_fields)),
        Rule::row_id => (
            NamedImplicit(id_or_fields.as_str().to_string()),
            fields(p.next().unwrap()),
        ),
        _ => unreachable!(),
    }
}

fn fn_body(b: Pair<Rule>) -> Expr {
    use Expr::*;

    let p = b.into_inner().next().unwrap();
    let loc = Loc::from(p.as_span());
    match p.as_rule() {
        Rule::fn_body_let => {
            let mut l = p.into_inner();
            let (id, typ, tm) = partial_let(&mut l);
            Let(loc, id, typ, tm, Box::new(fn_body(l.next().unwrap())))
        }
        Rule::fn_body_unit_let => {
            let mut l = p.into_inner();
            UnitLet(
                loc,
                Box::new(expr(l.next().unwrap())),
                Box::new(fn_body(l.next().unwrap())),
            )
        }
        Rule::fn_body_ret => p.into_inner().next().map_or(TT(loc), expr),
        _ => unreachable!(),
    }
}

fn expr(e: Pair<Rule>) -> Expr {
    use Expr::*;

    let p = e.into_inner().next().unwrap();
    let loc = Loc::from(p.as_span());
    match p.as_rule() {
        Rule::string => Str(loc, p.into_inner().next().unwrap().as_str().to_string()),
        Rule::number => Num(loc, p.into_inner().next().unwrap().as_str().to_string()),
        Rule::bigint => Big(loc, p.as_str().to_string()),
        Rule::boolean_false => False(loc),
        Rule::boolean_true => True(loc),
        Rule::boolean_if => {
            let mut pairs = p.into_inner();
            If(
                loc,
                Box::new(expr(pairs.next().unwrap())),
                Box::new(branch(pairs.next().unwrap())),
                Box::new(branch(pairs.next().unwrap())),
            )
        }
        Rule::method_app => {
            let loc = Loc::from(p.as_span());
            let mut pairs = p.into_inner();

            let o = pairs.next().unwrap();
            let o = Box::new(match o.as_rule() {
                Rule::expr => expr(o),
                Rule::idref => unresolved(o),
                _ => unreachable!(),
            });
            let n = pairs.next().unwrap().as_str().to_string();
            let arg = tupled_args(pairs.next().unwrap());

            pairs
                .map(|arg| (Loc::from(arg.as_span()), tupled_args(arg)))
                .fold(Lookup(loc, o, n, Box::new(arg)), |a, (loc, x)| {
                    App(loc, Box::new(a), UnnamedExplicit, Box::new(x))
                })
        }
        Rule::rev_app => {
            let mut pairs = p.into_inner();
            let arg = pairs.next().unwrap();
            pairs
                .fold(
                    (
                        Loc::from(arg.as_span()),
                        match arg.as_rule() {
                            Rule::expr => expr(arg),
                            Rule::idref => unresolved(arg),
                            _ => unreachable!(),
                        },
                    ),
                    |(loc, a), p| (Loc::from(p.as_span()), app(p, Some((loc, a)))),
                )
                .1
        }
        Rule::new_expr => {
            let mut pairs = p.into_inner();
            let cls = match unresolved(pairs.next().unwrap()) {
                Unresolved(loc, v) => Unresolved(loc, v.ctor()),
                _ => unreachable!(),
            };
            pairs
                .map(|arg| {
                    let loc = Loc::from(arg.as_span());
                    let (i, e) = match arg.as_rule() {
                        Rule::type_arg => type_arg(arg),
                        Rule::args => (UnnamedExplicit, tupled_args(arg)),
                        _ => unreachable!(),
                    };
                    (loc, i, e)
                })
                .fold(cls, |a, (loc, i, x)| App(loc, Box::new(a), i, Box::new(x)))
        }
        Rule::object_literal => object_literal(p),
        Rule::object_concat => {
            let mut pairs = p.into_inner();
            let a = object_operand(pairs.next().unwrap());
            let b = object_operand(pairs.next().unwrap());
            Concat(loc, Box::new(a), Box::new(b))
        }
        Rule::object_access => {
            let mut pairs = p.into_inner();
            let a = object_operand(pairs.next().unwrap());
            let n = pairs.next().unwrap().as_str().to_string();
            App(loc, Box::new(Access(loc, n)), UnnamedExplicit, Box::new(a))
        }
        Rule::object_cast => Downcast(
            loc,
            Box::new(object_operand(p.into_inner().next().unwrap())),
        ),
        Rule::enum_variant => enum_variant(p),
        Rule::enum_cast => Upcast(loc, Box::new(enum_operand(p.into_inner().next().unwrap()))),
        Rule::enum_switch => {
            let mut pairs = p.into_inner();
            let e = expr(pairs.next().unwrap().into_inner().next().unwrap());
            let mut cases = Vec::default();
            for p in pairs {
                let mut c = p.into_inner();
                let n = c.next().unwrap().as_str().to_string();
                let mut v = None;
                let mut body = None;
                for p in c {
                    match p.as_rule() {
                        Rule::param_id => v = Some(Var::from(p)),
                        Rule::expr => body = Some(expr(p)),
                        _ => unreachable!(),
                    };
                }
                cases.push((n, v.unwrap_or(Var::unbound()), body.unwrap()));
            }
            Switch(loc, Box::new(e), cases)
        }
        Rule::lambda_expr => {
            let pairs = p.into_inner();
            let mut vars = Vec::default();
            let mut body = None;
            for p in pairs {
                match p.as_rule() {
                    Rule::param_id => vars.push(unresolved(p)),
                    Rule::lambda_body => {
                        let b = p.into_inner().next().unwrap();
                        body = Some(match b.as_rule() {
                            Rule::expr => expr(b),
                            Rule::fn_body => fn_body(b),
                            _ => unreachable!(),
                        });
                        break;
                    }
                    _ => unreachable!(),
                }
            }
            TupledLam(loc, vars, Box::new(body.unwrap()))
        }
        Rule::app => app(p, None),
        Rule::tt => TT(loc),
        Rule::idref => unresolved(p),
        Rule::paren_expr => expr(p.into_inner().next().unwrap()),
        Rule::hole => Hole(loc),
        _ => unreachable!(),
    }
}

fn branch(b: Pair<Rule>) -> Expr {
    use Expr::*;

    let p = b.into_inner().next().unwrap();
    let loc = Loc::from(p.as_span());
    match p.as_rule() {
        Rule::branch_let => {
            let mut l = p.into_inner();
            let (id, typ, tm) = partial_let(&mut l);
            Let(loc, id, typ, tm, Box::new(branch(l.next().unwrap())))
        }
        Rule::branch_unit_let => {
            let mut l = p.into_inner();
            UnitLet(
                loc,
                Box::new(expr(l.next().unwrap())),
                Box::new(branch(l.next().unwrap())),
            )
        }
        Rule::expr => expr(p),
        _ => unreachable!(),
    }
}

fn app(a: Pair<Rule>, mut rev_operand: Option<(Loc, Expr)>) -> Expr {
    use Expr::*;

    let mut pairs = a.into_inner();
    let f = pairs.next().unwrap();
    let f = match f.as_rule() {
        Rule::expr => expr(f),
        Rule::idref => unresolved(f),
        _ => unreachable!(),
    };

    pairs
        .map(|arg| {
            let loc = Loc::from(arg.as_span());
            let (i, e) = match arg.as_rule() {
                Rule::row_arg => row_arg(arg),
                Rule::type_arg => type_arg(arg),
                Rule::args => {
                    let mut args = tupled_args(arg);
                    if let Some((loc, a)) = rev_operand.clone() {
                        args = Tuple(loc, Box::new(a), Box::new(args));
                    }
                    rev_operand = None; // only guarantee first reverse application
                    (UnnamedExplicit, args)
                }
                _ => unreachable!(),
            };
            (loc, i, e)
        })
        .fold(f, |a, (loc, i, x)| App(loc, Box::new(a), i, Box::new(x)))
}

fn unresolved(p: Pair<Rule>) -> Expr {
    use Expr::*;
    Unresolved(Loc::from(p.as_span()), Var::from(p))
}

fn row_param(p: Pair<Rule>) -> Param<Expr> {
    use Expr::*;
    let loc = Loc::from(p.as_span());
    Param {
        var: Var::from(p),
        info: Implicit,
        typ: Box::new(Row(loc)),
    }
}

fn implicit_param(p: Pair<Rule>) -> Param<Expr> {
    use Expr::*;
    let loc = Loc::from(p.as_span());
    Param {
        var: Var::from(p),
        info: Implicit,
        typ: Box::new(Univ(loc)),
    }
}

fn hkt_param(p: Pair<Rule>) -> Param<Expr> {
    use Expr::*;
    let mut pairs = p.into_inner();
    let var = Var::from(pairs.next().unwrap());
    let kind = Box::new(Univ(Loc::from(pairs.next().unwrap().as_span())));
    let typ = pairs.fold(kind, |a, b| {
        let loc = Loc::from(b.as_span());
        let p = Param {
            var: Var::unbound(),
            info: Implicit,
            typ: Box::new(Univ(loc)),
        };
        Box::new(Pi(loc, p, a))
    });
    Param {
        var,
        info: Implicit,
        typ,
    }
}

fn param(p: Pair<Rule>) -> Param<Expr> {
    let mut pairs = p.into_inner();
    Param {
        var: Var::from(pairs.next().unwrap()),
        info: Explicit,
        typ: Box::new(type_expr(pairs.next().unwrap())),
    }
}

fn fields(p: Pair<Rule>) -> Expr {
    use Expr::*;

    let loc = Loc::from(p.as_span());

    let mut fields = Vec::default();
    for pair in p.into_inner() {
        let mut f = pair.into_inner();
        let id = f.next().unwrap().as_str().to_string();
        let typ = f.next().map_or(Unit(loc), type_expr);
        fields.push((id, typ));
    }

    Fields(loc, fields)
}

fn label(l: Pair<Rule>) -> (String, Expr) {
    let mut p = l.into_inner();
    (
        p.next().unwrap().as_str().to_string(),
        expr(p.next().unwrap()),
    )
}

fn object_literal(l: Pair<Rule>) -> Expr {
    use Expr::*;
    let loc = Loc::from(l.as_span());
    Obj(
        loc,
        Box::new(Fields(loc, l.into_inner().map(label).collect())),
    )
}

fn object_operand(o: Pair<Rule>) -> Expr {
    let p = o.into_inner().next().unwrap();
    match p.as_rule() {
        Rule::app => app(p, None),
        Rule::object_literal => object_literal(p),
        Rule::idref => unresolved(p),
        Rule::paren_expr => expr(p.into_inner().next().unwrap()),
        _ => unreachable!(),
    }
}

fn enum_variant(v: Pair<Rule>) -> Expr {
    use Expr::*;
    let loc = Loc::from(v.as_span());
    let mut pairs = v.into_inner();
    let n = pairs.next().unwrap().as_str().to_string();
    let a = pairs
        .next()
        .map_or(TT(loc), |p| expr(p.into_inner().next().unwrap()));
    Variant(loc, n, Box::new(a))
}

fn enum_operand(o: Pair<Rule>) -> Expr {
    let p = o.into_inner().next().unwrap();
    match p.as_rule() {
        Rule::app => app(p, None),
        Rule::enum_variant => enum_variant(p),
        Rule::idref => unresolved(p),
        Rule::paren_expr => expr(p.into_inner().next().unwrap()),
        _ => unreachable!(),
    }
}

fn tupled_args(a: Pair<Rule>) -> Expr {
    use Expr::*;
    let loc = Loc::from(a.as_span());
    a.into_inner()
        .map(|pair| match pair.as_rule() {
            Rule::expr => (Loc::from(pair.as_span()), expr(pair)),
            _ => unreachable!(),
        })
        .rfold(TT(loc), |a, (loc, x)| Tuple(loc, Box::new(x), Box::new(a)))
}

fn partial_let(pairs: &mut Pairs<Rule>) -> (Var, Option<Box<Expr>>, Box<Expr>) {
    let id = Var::from(pairs.next().unwrap());
    let mut typ = None;
    let type_or_expr = pairs.next().unwrap();
    let tm = match type_or_expr.as_rule() {
        Rule::type_expr => {
            typ = Some(Box::new(type_expr(type_or_expr)));
            expr(pairs.next().unwrap())
        }
        Rule::expr => expr(type_or_expr),
        _ => unreachable!(),
    };
    (id, typ, Box::new(tm))
}

struct UntupledParams(Loc, Vec<(Loc, Param<Expr>)>);

impl UntupledParams {
    fn new(loc: Loc) -> Self {
        Self(loc, Default::default())
    }

    fn push(&mut self, loc: Loc, param: Param<Expr>) {
        self.1.push((loc, param))
    }

    fn unresolved(&self) -> Vec<Expr> {
        use Expr::*;
        self.1
            .iter()
            .map(|(loc, p)| Unresolved(*loc, p.var.clone()))
            .collect()
    }
}

impl From<UntupledParams> for Param<Expr> {
    fn from(ps: UntupledParams) -> Self {
        use Expr::*;
        let mut ret = Unit(ps.0);
        for p in ps.1.into_iter().rev() {
            ret = Sigma(p.0, p.1, Box::new(ret));
        }
        Self {
            var: Var::tupled(),
            info: Explicit,
            typ: Box::new(ret),
        }
    }
}
