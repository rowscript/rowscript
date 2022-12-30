use pest::iterators::{Pair, Pairs};

use crate::theory::abs::data::Dir;
use crate::theory::abs::def::Body::{Fun, Postulate};
use crate::theory::abs::def::Def;
use crate::theory::conc::data::ArgInfo::{NamedImplicit, UnnamedExplicit, UnnamedImplicit};
use crate::theory::conc::data::Case;
use crate::theory::conc::data::{ArgInfo, Expr};
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::{Loc, Param, Tele, Var};
use crate::Rule;

pub fn fn_def(f: Pair<Rule>) -> Def<Expr> {
    use Expr::*;

    let loc = Loc::from(f.as_span());
    let mut pairs = f.into_inner();

    let name = Var::from(pairs.next().unwrap());

    let mut tele = Tele::<Expr>::default();
    let mut untupled = UntupledParams::new(loc);
    let mut row_preds = Tele::<Expr>::default();
    let mut ret = Box::new(Unit(loc));
    let mut body = None;

    for p in pairs {
        match p.as_rule() {
            Rule::row_id => tele.push(row_param(p)),
            Rule::implicit_id => tele.push(implicit_param(p)),
            Rule::param => untupled.push(Loc::from(p.as_span()), param(p)),
            Rule::type_expr => ret = Box::new(type_expr(p)),
            Rule::fn_body => {
                body = Some(fn_body(p));
                break;
            }
            Rule::row_pred => row_preds.push(row_pred(p)),
            _ => unreachable!(),
        }
    }
    let untupled_vars = untupled.unresolved();
    let untupled_loc = untupled.0;
    let tupled_param = Param::from(untupled);
    let body = Fun(Expr::wrap_tuple_lets(
        untupled_loc,
        &tupled_param.var,
        untupled_vars,
        Box::new(body.unwrap()),
    ));
    tele.push(tupled_param);
    tele.extend(row_preds);

    Def {
        loc,
        name,
        tele,
        ret,
        body,
    }
}

pub fn fn_postulate(f: Pair<Rule>) -> Def<Expr> {
    use Expr::*;

    let loc = Loc::from(f.as_span());
    let mut pairs = f.into_inner();

    let name = Var::from(pairs.next().unwrap());

    let mut untupled = UntupledParams::new(loc);
    let mut ret = Box::new(Unit(loc));

    for p in pairs {
        match p.as_rule() {
            Rule::param => untupled.push(Loc::from(p.as_span()), param(p)),
            Rule::type_expr => ret = Box::new(type_expr(p)),
            _ => unreachable!(),
        }
    }

    Def {
        loc,
        name,
        tele: vec![Param::from(untupled)],
        ret,
        body: Postulate,
    }
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
        Rule::tyref => unresolved(p),
        Rule::paren_type_expr => type_expr(p.into_inner().next().unwrap()),
        Rule::hole => Hole(loc),
        _ => unreachable!(),
    }
}

fn row_pred(pred: Pair<Rule>) -> Param<Expr> {
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
        Rule::fn_body_ret => p.into_inner().next().map_or(TT(loc), expr),
        _ => unreachable!(),
    }
}

fn expr(e: Pair<Rule>) -> Expr {
    use Expr::*;

    let p = e.into_inner().next().unwrap();
    let loc = Loc::from(p.as_span());
    match p.as_rule() {
        Rule::string => Str(loc, p.as_str().to_string()),
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
            use Case::*;
            let mut pairs = p.into_inner();
            let e = expr(pairs.next().unwrap().into_inner().next().unwrap());
            let mut cases = Vec::default();
            for p in pairs {
                let mut c = p.into_inner();
                let n = c.next().unwrap().as_str().to_string();
                let mut t = None;
                let mut v = None;
                let mut body = None;
                for p in c {
                    match p.as_rule() {
                        Rule::param_id => v = Some(Var::from(p)),
                        Rule::type_expr => t = Some(type_expr(p)),
                        Rule::expr => body = Some(expr(p)),
                        _ => unreachable!(),
                    };
                }
                cases.push(if let Some(t) = t {
                    Annotated(n, v.unwrap(), t, body.unwrap())
                } else if let Some(v) = v {
                    Unannotated(n, v, body.unwrap())
                } else {
                    Unbound(n, body.unwrap())
                });
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
        Rule::app => app(p),
        Rule::tt => TT(loc),
        Rule::idref => unresolved(p),
        Rule::paren_expr => expr(p.into_inner().next().unwrap()),
        Rule::hole => Hole(loc),
        _ => unreachable!(),
    }
}

fn branch(b: Pair<Rule>) -> Expr {
    use Expr::*;

    let pair = b.into_inner().next().unwrap();
    let loc = Loc::from(pair.as_span());
    match pair.as_rule() {
        Rule::branch_let => {
            let mut l = pair.into_inner();
            let (id, typ, tm) = partial_let(&mut l);
            Let(loc, id, typ, tm, Box::new(branch(l.next().unwrap())))
        }
        Rule::expr => expr(pair),
        _ => unreachable!(),
    }
}

fn app(a: Pair<Rule>) -> Expr {
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
            match arg.as_rule() {
                Rule::row_arg => {
                    let (i, e) = row_arg(arg);
                    (loc, i, e)
                }
                Rule::type_arg => {
                    let (i, e) = type_arg(arg);
                    (loc, i, e)
                }
                Rule::args => (
                    loc,
                    UnnamedExplicit,
                    tupled_args(loc, &mut arg.into_inner()),
                ),
                _ => unreachable!(),
            }
        })
        .fold(f, |a, (loc, i, x)| App(loc, Box::new(a), i, Box::new(x)))
}

fn unresolved(p: Pair<Rule>) -> Expr {
    use Expr::*;
    Unresolved(Loc::from(p.as_span()), Var::from(p))
}

fn row_param(p: Pair<Rule>) -> Param<Expr> {
    use Expr::*;
    Param {
        var: Var::new(p.as_str()),
        info: Implicit,
        typ: Box::new(Row(Loc::from(p.as_span()))),
    }
}

fn implicit_param(p: Pair<Rule>) -> Param<Expr> {
    use Expr::*;
    Param {
        var: Var::new(p.as_str()),
        info: Implicit,
        typ: Box::new(Univ(Loc::from(p.as_span()))),
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
        Rule::app => app(p),
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
        Rule::app => app(p),
        Rule::enum_variant => enum_variant(p),
        Rule::idref => unresolved(p),
        Rule::paren_expr => expr(p.into_inner().next().unwrap()),
        _ => unreachable!(),
    }
}

fn tupled_args(tt_loc: Loc, pairs: &mut Pairs<Rule>) -> Expr {
    use Expr::*;
    pairs
        .map(|pair| match pair.as_rule() {
            Rule::expr => (Loc::from(pair.as_span()), expr(pair)),
            _ => unreachable!(),
        })
        .rfold(TT(tt_loc), |a, (loc, x)| {
            Tuple(loc, Box::new(x), Box::new(a))
        })
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
