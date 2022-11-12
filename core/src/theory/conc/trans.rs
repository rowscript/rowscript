use pest::iterators::Pair;

use crate::theory::abs::def::{Def, Fun};
use crate::theory::conc::data::Expr;
use crate::theory::conc::data::Expr::{Sig, Unit, Univ, TT};
use crate::theory::{LineCol, LocalVar, Param};
use crate::{Driver, Rule};

pub struct Trans<'a> {
    file: &'a str,
}

impl<'a> From<Driver<'a>> for Trans<'a> {
    fn from(d: Driver<'a>) -> Self {
        Self { file: d.file }
    }
}

impl<'a> Trans<'a> {
    pub fn fn_def(&self, f: Pair<Rule>) -> Box<dyn Def<Expr>> {
        let loc = LineCol::from(f.as_span());

        let mut rules = f.into_inner();
        let name = rules.next().unwrap();

        let mut params: Vec<Param<Expr>> = Default::default();
        let mut untupled = UntupledParams::new();
        for p in rules {
            match p.as_rule() {
                Rule::implicit_id => params.push(Param::implicit(p)),
                Rule::param => untupled.push(LineCol::from(p.as_span()), Param::param(p)),
                _ => break,
            }
        }
        params.push(Param::from(untupled));

        Box::new(Fun::new(
            loc,
            LocalVar::from(name),
            params,
            Box::new(Unit(loc)),
            Box::new(TT(loc)),
        ))
    }
}

impl Param<Expr> {
    pub fn implicit(p: Pair<Rule>) -> Self {
        Self {
            var: LocalVar::new(p.as_str()),
            typ: Box::new(Univ(LineCol::from(p.as_span()))),
        }
    }

    pub fn param(p: Pair<Rule>) -> Self {
        let mut pairs = p.into_inner();
        let id = pairs.next().unwrap();
        let typ = pairs.next().unwrap();
        Self {
            var: LocalVar::new(id.as_str()),
            // TODO: Type expression.
            typ: Box::new(TT(LineCol::from(typ.as_span()))),
        }
    }
}

struct UntupledParam(LineCol, Param<Expr>);

struct UntupledParams(Option<LineCol>, Vec<UntupledParam>);

impl UntupledParams {
    pub fn new() -> Self {
        Self(None, Default::default())
    }

    pub fn push(&mut self, loc: LineCol, param: Param<Expr>) {
        self.0.get_or_insert(loc);
        self.1.push(UntupledParam(loc, param))
    }
}

impl From<UntupledParams> for Param<Expr> {
    fn from(ps: UntupledParams) -> Self {
        let mut ret = Unit(ps.0.unwrap());
        for p in ps.1.into_iter().rev() {
            ret = Sig(p.0, p.1, Box::new(ret));
        }
        Self {
            var: LocalVar::tupled(),
            typ: Box::new(ret),
        }
    }
}
