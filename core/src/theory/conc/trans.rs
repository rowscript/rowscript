use pest::iterators::{Pair, Pairs};

use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::theory::conc::data::Expr::{
    App, Big, BigInt, Boolean, False, If, Let, Num, Number, Pi, Sigma, Str, String, True, Tuple,
    TupledLam, Unit, Univ, Unresolved, TT,
};
use crate::theory::{Loc, LocalVar, Param};
use crate::Rule;

pub fn fn_def(f: Pair<Rule>) -> Def<Expr> {
    let loc = Loc::from(f.as_span());
    let mut pairs = f.into_inner();

    let name = pairs.next().unwrap();
    let mut tele: Vec<Param<Expr>> = Default::default();
    let mut untupled = UntupledParams::new(loc);
    let mut ret = Unit(loc);
    let mut body: Option<Expr> = None;

    for p in pairs {
        match p.as_rule() {
            Rule::implicit_id => tele.push(implicit(p)),
            Rule::param => untupled.push(Loc::from(p.as_span()), param(p)),
            Rule::type_expr => ret = type_expr(p),
            Rule::fn_body => {
                body = Some(fn_body(p));
                break;
            }
            _ => unreachable!(),
        }
    }
    tele.push(Param::from(untupled));

    Def::fun(
        loc,
        LocalVar::from(name),
        tele,
        Box::new(ret),
        Box::new(body.unwrap()),
    )
}

fn type_expr(t: Pair<Rule>) -> Expr {
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
        Rule::string_type => String(Loc::from(p.as_span())),
        Rule::number_type => Number(Loc::from(p.as_span())),
        Rule::bigint_type => BigInt(Loc::from(p.as_span())),
        Rule::boolean_type => Boolean(Loc::from(p.as_span())),
        Rule::unit_type => Unit(Loc::from(p.as_span())),
        Rule::idref => Unresolved(Loc::from(p.as_span()), LocalVar::from(p)),
        Rule::paren_type_expr => type_expr(p.into_inner().next().unwrap()),
        _ => unreachable!(),
    }
}

fn fn_body(b: Pair<Rule>) -> Expr {
    let p = b.into_inner().next().unwrap();
    let loc = Loc::from(p.as_span());
    match p.as_rule() {
        Rule::fn_body_let => {
            let mut l = p.into_inner();
            let (id, typ, tm) = partial_let(&mut l);
            Let(loc, id, typ, tm, Box::new(fn_body(l.next().unwrap())))
        }
        Rule::fn_body_ret => p.into_inner().next().map_or(Unit(loc), primary_expr),
        _ => unreachable!(),
    }
}

fn primary_expr(e: Pair<Rule>) -> Expr {
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
                Box::new(primary_expr(pairs.next().unwrap())),
                Box::new(branch(pairs.next().unwrap())),
                Box::new(branch(pairs.next().unwrap())),
            )
        }
        Rule::lambda_expr => {
            let pairs = p.into_inner();
            let mut vars: Vec<LocalVar> = Default::default();
            let mut body: Option<Expr> = None;
            for p in pairs {
                match p.as_rule() {
                    Rule::param_id => vars.push(LocalVar::from(p)),
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
            let floc = Loc::from(f.as_span());
            let f = match f.as_rule() {
                Rule::primary_expr => primary_expr(f),
                Rule::idref => Unresolved(Loc::from(f.as_span()), LocalVar::from(f)),
                _ => unreachable!(),
            };
            let mut type_args: Vec<Expr> = Default::default();
            let mut untupled_args: Vec<Expr> = Default::default();
            for arg in pairs {
                match arg.as_rule() {
                    Rule::type_expr => type_args.push(type_expr(arg)),
                    Rule::primary_expr => untupled_args.push(primary_expr(arg)),
                    _ => unreachable!(),
                }
            }
            let app = type_args
                .into_iter()
                .fold(f, |a, x| App(floc, Box::new(a), Box::new(x)));
            let tupled_arg = untupled_args
                .into_iter()
                .rfold(TT(floc), |a, x| Tuple(floc, Box::new(x), Box::new(a)));
            App(floc, Box::new(app), Box::new(tupled_arg))
        }
        Rule::tt => TT(loc),
        Rule::idref => Unresolved(loc, LocalVar::from(p)),
        Rule::paren_primary_expr => primary_expr(p.into_inner().next().unwrap()),
        _ => unreachable!(),
    }
}

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

fn implicit(p: Pair<Rule>) -> Param<Expr> {
    Param {
        var: LocalVar::new(p.as_str()),
        typ: Box::new(Univ(Loc::from(p.as_span()))),
    }
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

fn param(p: Pair<Rule>) -> Param<Expr> {
    let mut pairs = p.into_inner();
    Param {
        var: LocalVar::from(pairs.next().unwrap()),
        typ: Box::new(type_expr(pairs.next().unwrap())),
    }
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
        let mut ret = Unit(ps.0);
        for p in ps.1.into_iter().rev() {
            ret = Sigma(p.0, p.1, Box::new(ret));
        }
        Self {
            var: LocalVar::tupled(),
            typ: Box::new(ret),
        }
    }
}
