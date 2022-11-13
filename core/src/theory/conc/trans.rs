use pest::iterators::Pair;

use crate::theory::abs::def::{Def, Fun};
use crate::theory::conc::data::Expr;
use crate::theory::conc::data::Expr::{
    Big, BigInt, Boolean, False, Let, Num, Number, Pi, Sig, Str, String, True, TupledLam, Unit,
    Univ, Unresolved, TT,
};
use crate::theory::{LineCol, LocalVar, Param};
use crate::Rule;

pub fn fn_def(f: Pair<Rule>) -> Box<dyn Def<Expr>> {
    let loc = LineCol::from(f.as_span());
    let mut pairs = f.into_inner();

    let name = pairs.next().unwrap();
    let mut params: Vec<Param<Expr>> = Default::default();
    let mut untupled = UntupledParams::new(loc);
    let mut ret = Unit(loc);
    let mut body: Option<Expr> = None;

    for p in pairs {
        match p.as_rule() {
            Rule::implicit_id => params.push(implicit(p)),
            Rule::param => untupled.push(LineCol::from(p.as_span()), param(p)),
            Rule::type_expr => ret = type_expr(p),
            Rule::fn_body => {
                body = Some(fn_body(p));
                break;
            }
            _ => unreachable!(),
        }
    }
    params.push(Param::from(untupled));

    Box::new(Fun::new(
        loc,
        LocalVar::from(name),
        params,
        Box::new(ret),
        Box::new(body.unwrap()),
    ))
}

fn type_expr(t: Pair<Rule>) -> Expr {
    let p = t.into_inner().next().unwrap();
    let loc = LineCol::from(p.as_span());
    match p.as_rule() {
        Rule::paren_type_expr => type_expr(p),
        Rule::fn_type => {
            let ps = p.into_inner();
            let mut untupled = UntupledParams::new(loc);
            for fp in ps {
                match fp.as_rule() {
                    Rule::param => untupled.push(LineCol::from(fp.as_span()), param(fp)),
                    Rule::type_expr => {
                        return Pi(loc, Param::from(untupled), Box::new(type_expr(fp)));
                    }
                    _ => unreachable!(),
                }
            }
            unreachable!()
        }
        Rule::string_type => String(LineCol::from(p.as_span())),
        Rule::number_type => Number(LineCol::from(p.as_span())),
        Rule::bigint_type => BigInt(LineCol::from(p.as_span())),
        Rule::boolean_type => Boolean(LineCol::from(p.as_span())),
        Rule::unit_type => Unit(LineCol::from(p.as_span())),
        Rule::idref => Unresolved(LineCol::from(p.as_span()), LocalVar::from(p)),
        _ => unreachable!(),
    }
}

fn fn_body(b: Pair<Rule>) -> Expr {
    let p = b.into_inner().next().unwrap();
    let loc = LineCol::from(p.as_span());
    match p.as_rule() {
        Rule::fn_body_let => {
            let mut pairs = p.into_inner();
            Let(
                loc,
                param(pairs.next().unwrap()),
                Box::new(primary_expr(pairs.next().unwrap())),
                Box::new(fn_body(pairs.next().unwrap())),
            )
        }
        Rule::fn_body_ret => p.into_inner().next().map_or(Unit(loc), primary_expr),
        _ => unreachable!(),
    }
}

fn primary_expr(e: Pair<Rule>) -> Expr {
    let p = e.into_inner().next().unwrap();
    let loc = LineCol::from(p.as_span());
    match p.as_rule() {
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
        Rule::string => Str(loc, p.as_str().to_string()),
        Rule::number => Num(loc, p.into_inner().next().unwrap().as_str().to_string()),
        Rule::bigint => Big(loc, p.as_str().to_string()),
        Rule::boolean_false => False(loc),
        Rule::boolean_true => True(loc),
        Rule::tt => TT(loc),
        Rule::idref => Unresolved(loc, LocalVar::from(p)),
        _ => unreachable!(),
    }
}

fn implicit(p: Pair<Rule>) -> Param<Expr> {
    Param {
        var: LocalVar::new(p.as_str()),
        typ: Box::new(Univ(LineCol::from(p.as_span()))),
    }
}

fn param(p: Pair<Rule>) -> Param<Expr> {
    let mut pairs = p.into_inner();
    let id = pairs.next().unwrap();
    let typ = pairs.next().unwrap();
    Param {
        var: LocalVar::from(id),
        typ: Box::new(type_expr(typ)),
    }
}

struct UntupledParams(LineCol, Vec<(LineCol, Param<Expr>)>);

impl UntupledParams {
    fn new(loc: LineCol) -> Self {
        Self(loc, Default::default())
    }

    fn push(&mut self, loc: LineCol, param: Param<Expr>) {
        self.1.push((loc, param))
    }
}

impl From<UntupledParams> for Param<Expr> {
    fn from(ps: UntupledParams) -> Self {
        let mut ret = Unit(ps.0);
        for p in ps.1.into_iter().rev() {
            ret = Sig(p.0, p.1, Box::new(ret));
        }
        Self {
            var: LocalVar::tupled(),
            typ: Box::new(ret),
        }
    }
}
