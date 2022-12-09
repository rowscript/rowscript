use pest::iterators::{Pair, Pairs};

use crate::theory::abs::data::Dir;
use crate::theory::abs::def::Body::{Fun, Postulate};
use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::theory::conc::data::Expr::Unresolved;
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::{Loc, LocalVar, Param, Tele};
use crate::Rule;

pub fn fn_def(f: Pair<Rule>) -> Def<Expr> {
    use Expr::*;

    let loc = Loc::from(f.as_span());
    let mut pairs = f.into_inner();

    let name = LocalVar::from(pairs.next().unwrap());
    let mut tele: Tele<Expr> = Default::default();
    let mut untupled = UntupledParams::new(loc);
    let mut ret = Box::new(Unit(loc));
    let mut body: Option<Expr> = None;

    for p in pairs {
        match p.as_rule() {
            Rule::implicit_id => tele.push(implicit(p)),
            Rule::row_id => tele.push(row_param(p)),
            Rule::param => untupled.push(Loc::from(p.as_span()), param(p)),
            Rule::type_expr => ret = Box::new(type_expr(p)),
            Rule::fn_body => {
                body = Some(fn_body(p));
                break;
            }
            Rule::row_pred => tele.push(row_pred(p)),
            _ => unreachable!(),
        }
    }
    tele.push(Param::from(untupled));

    Def {
        loc,
        name,
        tele,
        ret,
        body: Fun(Box::new(body.unwrap())),
    }
}

pub fn fn_postulate(f: Pair<Rule>) -> Def<Expr> {
    use Expr::*;

    let loc = Loc::from(f.as_span());
    let mut pairs = f.into_inner();

    let name = LocalVar::from(pairs.next().unwrap());
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
        Rule::object_type => {
            let p = p.into_inner().next().unwrap();
            match p.as_rule() {
                Rule::object_ref => {
                    let loc = Loc::from(p.as_span());
                    let p = p.into_inner().next().unwrap();
                    let r = Box::new(unresolved(p));
                    Object(loc, r)
                }
                Rule::simple_object => fields(p),
                _ => unreachable!(),
            }
        }
        Rule::idref => unresolved(p),
        Rule::paren_type_expr => type_expr(p.into_inner().next().unwrap()),
        Rule::hole => Hole(loc),
        _ => unreachable!(),
    }
}

fn row_pred(pred: Pair<Rule>) -> Param<Expr> {
    use Expr::*;

    fn row_expr(e: Pair<Rule>) -> Expr {
        let p = e.into_inner().next().unwrap();
        let loc = Loc::from(p.as_span());
        match p.as_rule() {
            Rule::row_concat => {
                let mut p = p.into_inner();
                let lhs = row_primary_expr(p.next().unwrap());
                let rhs = row_expr(p.next().unwrap());
                Concat(loc, Box::new(lhs), Box::new(rhs))
            }
            Rule::row_primary_expr => row_primary_expr(p),
            _ => unreachable!(),
        }
    }

    fn row_primary_expr(e: Pair<Rule>) -> Expr {
        let p = e.into_inner().next().unwrap();
        match p.as_rule() {
            Rule::idref => unresolved(p),
            Rule::paren_fields => fields(p),
            Rule::paren_row_expr => row_expr(p.into_inner().next().unwrap()),
            _ => unreachable!(),
        }
    }

    let p = pred.into_inner().next().unwrap();
    let loc = Loc::from(p.as_span());
    Param {
        var: LocalVar::unbound(),
        info: Implicit,
        typ: match p.as_rule() {
            Rule::row_ord => {
                let mut p = p.into_inner();
                let lhs = row_expr(p.next().unwrap());
                let dir = p.next().unwrap();
                let dir = match dir.as_rule() {
                    Rule::row_lt => Dir::Lt,
                    Rule::row_gt => Dir::Gt,
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
        Rule::fn_body_ret => p.into_inner().next().map_or(TT(loc), primary_expr),
        _ => unreachable!(),
    }
}

fn primary_expr(e: Pair<Rule>) -> Expr {
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
            fn branch(b: Pair<Rule>) -> Expr {
                let pair = b.into_inner().next().unwrap();
                let loc = Loc::from(pair.as_span());
                match pair.as_rule() {
                    Rule::branch_let => {
                        let mut l = pair.into_inner();
                        let (id, typ, tm) = partial_let(&mut l);
                        Let(loc, id, typ, tm, Box::new(branch(l.next().unwrap())))
                    }
                    Rule::primary_expr => primary_expr(pair),
                    _ => unreachable!(),
                }
            }

            let mut pairs = p.into_inner();
            If(
                loc,
                Box::new(primary_expr(pairs.next().unwrap())),
                Box::new(branch(pairs.next().unwrap())),
                Box::new(branch(pairs.next().unwrap())),
            )
        }
        Rule::lambda_expr => {
            let pairs = p.into_inner();
            let mut vars: Vec<Expr> = Default::default();
            let mut body: Option<Expr> = None;
            for p in pairs {
                match p.as_rule() {
                    Rule::param_id => vars.push(unresolved(p)),
                    Rule::lambda_body => {
                        let b = p.into_inner().next().unwrap();
                        body = Some(match b.as_rule() {
                            Rule::primary_expr => primary_expr(b),
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
        Rule::app => {
            let mut pairs = p.into_inner();
            let f = pairs.next().unwrap();
            let f = match f.as_rule() {
                Rule::primary_expr => primary_expr(f),
                Rule::idref => unresolved(f),
                _ => unreachable!(),
            };
            pairs
                .map(|arg| {
                    let loc = Loc::from(arg.as_span());
                    match arg.as_rule() {
                        Rule::type_expr => (loc, type_expr(arg)),
                        Rule::args => (loc, tupled_args(loc, &mut arg.into_inner())),
                        _ => unreachable!(),
                    }
                })
                .fold(f, |a, (loc, x)| App(loc, Box::new(a), Box::new(x)))
        }
        Rule::tt => TT(loc),
        Rule::idref => unresolved(p),
        Rule::paren_primary_expr => primary_expr(p.into_inner().next().unwrap()),
        Rule::hole => Hole(loc),
        _ => unreachable!(),
    }
}

fn unresolved(p: Pair<Rule>) -> Expr {
    Unresolved(Loc::from(p.as_span()), LocalVar::from(p))
}

fn implicit(p: Pair<Rule>) -> Param<Expr> {
    use Expr::*;
    Param {
        var: LocalVar::new(p.as_str()),
        info: Implicit,
        typ: Box::new(Univ(Loc::from(p.as_span()))),
    }
}

fn row_param(p: Pair<Rule>) -> Param<Expr> {
    use Expr::*;
    Param {
        var: LocalVar::new(p.as_str()),
        info: Implicit,
        typ: Box::new(Row(Loc::from(p.as_span()))),
    }
}

fn param(p: Pair<Rule>) -> Param<Expr> {
    let mut pairs = p.into_inner();
    Param {
        var: LocalVar::from(pairs.next().unwrap()),
        info: Explicit,
        typ: Box::new(type_expr(pairs.next().unwrap())),
    }
}

fn fields(p: Pair<Rule>) -> Expr {
    use Expr::Fields;

    let loc = Loc::from(p.as_span());

    let mut fields: Vec<(String, Expr)> = Default::default();
    for pair in p.into_inner() {
        let mut f = pair.into_inner();
        let id = f.next().unwrap().as_str().to_string();
        let typ = type_expr(f.next().unwrap());
        fields.push((id, typ));
    }

    Fields(loc, fields)
}

fn tupled_args(tt_loc: Loc, pairs: &mut Pairs<Rule>) -> Expr {
    use Expr::*;
    pairs
        .map(|pair| match pair.as_rule() {
            Rule::primary_expr => (Loc::from(pair.as_span()), primary_expr(pair)),
            _ => unreachable!(),
        })
        .rfold(TT(tt_loc), |a, (loc, x)| {
            Tuple(loc, Box::new(x), Box::new(a))
        })
}

fn partial_let(pairs: &mut Pairs<Rule>) -> (LocalVar, Option<Box<Expr>>, Box<Expr>) {
    let id = LocalVar::from(pairs.next().unwrap());
    let mut typ = None;
    let type_or_primary_expr = pairs.next().unwrap();
    let tm = match type_or_primary_expr.as_rule() {
        Rule::type_expr => {
            typ = Some(Box::new(type_expr(type_or_primary_expr)));
            primary_expr(pairs.next().unwrap())
        }
        Rule::primary_expr => primary_expr(type_or_primary_expr),
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
}

impl From<UntupledParams> for Param<Expr> {
    fn from(ps: UntupledParams) -> Self {
        use Expr::*;
        let mut ret = Unit(ps.0);
        for p in ps.1.into_iter().rev() {
            ret = Sigma(p.0, p.1, Box::new(ret));
        }
        Self {
            var: LocalVar::tupled(),
            info: Explicit,
            typ: Box::new(ret),
        }
    }
}
