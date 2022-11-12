use pest::iterators::Pair;

use crate::theory::abs::def::{Def, Fun};
use crate::theory::conc::data::Expr;
use crate::theory::conc::data::Expr::{
    BigInt, Boolean, Number, Pi, Sig, String, Unit, Univ, Unresolved, TT,
};
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

        let mut pairs = f.into_inner();
        let name = pairs.next().unwrap();

        let mut params: Vec<Param<Expr>> = Default::default();
        let mut untupled = UntupledParams::new(loc);

        let mut ret = Unit(loc);

        for p in pairs {
            match p.as_rule() {
                Rule::implicit_id => params.push(self.implicit(p)),
                Rule::param => untupled.push(LineCol::from(p.as_span()), self.param(p)),
                Rule::type_expr => ret = self.type_expr(p),
                Rule::fn_body_block => {
                    // TODO
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
            // TODO: Function body.
            Box::new(TT(loc)),
        ))
    }

    fn type_expr(&self, t: Pair<Rule>) -> Expr {
        let p = t.into_inner().next().unwrap();
        let loc = LineCol::from(p.as_span());
        match p.as_rule() {
            Rule::paren_type_expr => self.type_expr(p),
            Rule::fn_type => {
                let ps = p.into_inner();
                let mut untupled = UntupledParams::new(loc);
                for fp in ps {
                    match fp.as_rule() {
                        Rule::param => untupled.push(LineCol::from(fp.as_span()), self.param(fp)),
                        Rule::type_expr => {
                            return Pi(loc, Param::from(untupled), Box::new(self.type_expr(fp)));
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

    fn implicit(&self, p: Pair<Rule>) -> Param<Expr> {
        Param {
            var: LocalVar::new(p.as_str()),
            typ: Box::new(Univ(LineCol::from(p.as_span()))),
        }
    }

    fn param(&self, p: Pair<Rule>) -> Param<Expr> {
        let mut pairs = p.into_inner();
        let id = pairs.next().unwrap();
        let typ = pairs.next().unwrap();
        Param {
            var: LocalVar::from(id),
            typ: Box::new(self.type_expr(typ)),
        }
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
