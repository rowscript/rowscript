use std::string;

use pest::iterators::{Pair, Pairs};

use crate::theory::abs::data::Dir;
use crate::theory::abs::def::Body::{Fun, Postulate};
use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::theory::conc::data::Expr::Unresolved;
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::{Loc, Param, Tele, Var, VarMap};
use crate::Rule;

#[derive(Default)]
pub struct Translator {
    name: Option<Var>,
}

impl Translator {
    pub fn fn_def(&mut self, f: Pair<Rule>) -> Def<Expr> {
        use Expr::*;

        let loc = Loc::from(f.as_span());
        let mut pairs = f.into_inner();

        let name = Var::from(pairs.next().unwrap());
        self.name = Some(name.clone());

        let mut tele = Tele::<Expr>::default();
        let mut local_holes = VarMap::default();
        let mut untupled = UntupledParams::new(loc);
        let mut ret = Box::new(Unit(loc));
        let mut body = None;

        for p in pairs {
            match p.as_rule() {
                Rule::implicit_id => tele.push(Self::implicit(p)),
                Rule::row_hole => {
                    let hole = Var::local_hole(name.clone(), p.as_str());
                    local_holes.insert(hole.name.to_string(), hole);
                }
                Rule::param => untupled.push(Loc::from(p.as_span()), self.param(p)),
                Rule::type_expr => ret = Box::new(self.type_expr(p)),
                Rule::fn_body => {
                    body = Some(self.fn_body(p));
                    break;
                }
                Rule::row_pred => tele.push(self.row_pred(p)),
                _ => unreachable!(),
            }
        }
        tele.push(Param::from(untupled));

        Def {
            loc,
            name,
            tele,
            ret,
            body: Fun {
                local_holes,
                f: Box::new(body.unwrap()),
            },
        }
    }

    pub fn fn_postulate(&mut self, f: Pair<Rule>) -> Def<Expr> {
        use Expr::*;

        let loc = Loc::from(f.as_span());
        let mut pairs = f.into_inner();

        let name = Var::from(pairs.next().unwrap());
        self.name = Some(name.clone());

        let mut untupled = UntupledParams::new(loc);
        let mut ret = Box::new(Unit(loc));

        for p in pairs {
            match p.as_rule() {
                Rule::param => untupled.push(Loc::from(p.as_span()), self.param(p)),
                Rule::type_expr => ret = Box::new(self.type_expr(p)),
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

    fn type_expr(&self, t: Pair<Rule>) -> Expr {
        use Expr::*;

        let p = t.into_inner().next().unwrap();
        let loc = Loc::from(p.as_span());
        match p.as_rule() {
            Rule::fn_type => {
                let ps = p.into_inner();
                let mut untupled = UntupledParams::new(loc);
                for fp in ps {
                    match fp.as_rule() {
                        Rule::param => untupled.push(Loc::from(fp.as_span()), self.param(fp)),
                        Rule::type_expr => {
                            return Pi(loc, Param::from(untupled), Box::new(self.type_expr(fp)));
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
                        let p = p.into_inner().next().unwrap();
                        let name = self.name.clone().unwrap();
                        Object(
                            loc,
                            Box::new(RowHole(
                                Loc::from(p.as_span()),
                                Var::local_hole(name, p.as_str()),
                            )),
                        )
                    }
                    Rule::object_type_literal => Object(loc, Box::new(self.fields(p))),
                    _ => unreachable!(),
                }
            }
            Rule::idref => Self::unresolved(p),
            Rule::paren_type_expr => self.type_expr(p.into_inner().next().unwrap()),
            Rule::hole => Hole(loc),
            _ => unreachable!(),
        }
    }

    fn row_pred(&self, pred: Pair<Rule>) -> Param<Expr> {
        use Expr::*;

        let p = pred.into_inner().next().unwrap();
        let loc = Loc::from(p.as_span());
        Param {
            var: Var::unbound(),
            info: Implicit,
            typ: match p.as_rule() {
                Rule::row_ord => {
                    let mut p = p.into_inner();
                    let lhs = self.row_expr(p.next().unwrap());
                    let dir = p.next().unwrap();
                    let dir = match dir.as_rule() {
                        Rule::row_le => Dir::Le,
                        Rule::row_ge => Dir::Ge,
                        _ => unreachable!(),
                    };
                    let rhs = self.row_expr(p.next().unwrap());
                    Box::new(RowOrd(loc, Box::new(lhs), dir, Box::new(rhs)))
                }
                Rule::row_eq => {
                    let mut p = p.into_inner();
                    let lhs = self.row_expr(p.next().unwrap());
                    let rhs = self.row_expr(p.next().unwrap());
                    Box::new(RowEq(loc, Box::new(lhs), Box::new(rhs)))
                }
                _ => unreachable!(),
            },
        }
    }

    fn row_expr(&self, e: Pair<Rule>) -> Expr {
        use Expr::*;

        let p = e.into_inner().next().unwrap();
        let loc = Loc::from(p.as_span());
        match p.as_rule() {
            Rule::row_concat => {
                let mut p = p.into_inner();
                let lhs = self.row_primary_expr(p.next().unwrap());
                let rhs = self.row_expr(p.next().unwrap());
                Combine(loc, Box::new(lhs), Box::new(rhs))
            }
            Rule::row_primary_expr => self.row_primary_expr(p),
            _ => unreachable!(),
        }
    }

    fn row_primary_expr(&self, e: Pair<Rule>) -> Expr {
        use Expr::*;

        let p = e.into_inner().next().unwrap();
        let loc = Loc::from(p.as_span());
        match p.as_rule() {
            Rule::row_hole => {
                let name = self.name.clone().unwrap();
                RowHole(loc, Var::local_hole(name, p.as_str()))
            }
            Rule::paren_fields => self.fields(p),
            Rule::paren_row_expr => self.row_expr(p.into_inner().next().unwrap()),
            _ => unreachable!(),
        }
    }

    fn fn_body(&self, b: Pair<Rule>) -> Expr {
        use Expr::*;

        let p = b.into_inner().next().unwrap();
        let loc = Loc::from(p.as_span());
        match p.as_rule() {
            Rule::fn_body_let => {
                let mut l = p.into_inner();
                let (id, typ, tm) = self.partial_let(&mut l);
                Let(loc, id, typ, tm, Box::new(self.fn_body(l.next().unwrap())))
            }
            Rule::fn_body_ret => p.into_inner().next().map_or(TT(loc), |e| self.expr(e)),
            _ => unreachable!(),
        }
    }

    fn expr(&self, e: Pair<Rule>) -> Expr {
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
                    Box::new(self.expr(pairs.next().unwrap())),
                    Box::new(self.branch(pairs.next().unwrap())),
                    Box::new(self.branch(pairs.next().unwrap())),
                )
            }
            Rule::lambda_expr => {
                let pairs = p.into_inner();
                let mut vars: Vec<Expr> = Default::default();
                let mut body: Option<Expr> = None;
                for p in pairs {
                    match p.as_rule() {
                        Rule::param_id => vars.push(Self::unresolved(p)),
                        Rule::lambda_body => {
                            let b = p.into_inner().next().unwrap();
                            body = Some(match b.as_rule() {
                                Rule::expr => self.expr(b),
                                Rule::fn_body => self.fn_body(b),
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
                    Rule::expr => self.expr(f),
                    Rule::idref => Self::unresolved(f),
                    _ => unreachable!(),
                };
                pairs
                    .map(|arg| {
                        let loc = Loc::from(arg.as_span());
                        match arg.as_rule() {
                            Rule::type_expr => (loc, self.type_expr(arg)),
                            Rule::args => (loc, self.tupled_args(loc, &mut arg.into_inner())),
                            _ => unreachable!(),
                        }
                    })
                    .fold(f, |a, (loc, x)| App(loc, Box::new(a), Box::new(x)))
            }
            Rule::tt => TT(loc),
            Rule::labels => Obj(
                loc,
                Box::new(Fields(loc, p.into_inner().map(|l| self.label(l)).collect())),
            ),
            Rule::idref => Self::unresolved(p),
            Rule::paren_expr => self.expr(p.into_inner().next().unwrap()),
            Rule::hole => Hole(loc),
            _ => unreachable!(),
        }
    }

    fn branch(&self, b: Pair<Rule>) -> Expr {
        use Expr::*;

        let pair = b.into_inner().next().unwrap();
        let loc = Loc::from(pair.as_span());
        match pair.as_rule() {
            Rule::branch_let => {
                let mut l = pair.into_inner();
                let (id, typ, tm) = self.partial_let(&mut l);
                Let(loc, id, typ, tm, Box::new(self.branch(l.next().unwrap())))
            }
            Rule::expr => self.expr(pair),
            _ => unreachable!(),
        }
    }

    fn unresolved(p: Pair<Rule>) -> Expr {
        Unresolved(Loc::from(p.as_span()), Var::from(p))
    }

    fn implicit(p: Pair<Rule>) -> Param<Expr> {
        use Expr::*;
        Param {
            var: Var::new(p.as_str()),
            info: Implicit,
            typ: Box::new(Univ(Loc::from(p.as_span()))),
        }
    }

    fn param(&self, p: Pair<Rule>) -> Param<Expr> {
        let mut pairs = p.into_inner();
        Param {
            var: Var::from(pairs.next().unwrap()),
            info: Explicit,
            typ: Box::new(self.type_expr(pairs.next().unwrap())),
        }
    }

    fn fields(&self, p: Pair<Rule>) -> Expr {
        use Expr::*;

        let loc = Loc::from(p.as_span());

        let mut fields = Vec::<(string::String, Expr)>::default();
        for pair in p.into_inner() {
            let mut f = pair.into_inner();
            let id = f.next().unwrap().as_str().to_string();
            let typ = self.type_expr(f.next().unwrap());
            fields.push((id, typ));
        }

        Fields(loc, fields)
    }

    fn label(&self, l: Pair<Rule>) -> (String, Expr) {
        let mut p = l.into_inner();
        (
            p.next().unwrap().as_str().to_string(),
            self.expr(p.next().unwrap()),
        )
    }

    fn tupled_args(&self, tt_loc: Loc, pairs: &mut Pairs<Rule>) -> Expr {
        use Expr::*;
        pairs
            .map(|pair| match pair.as_rule() {
                Rule::expr => (Loc::from(pair.as_span()), self.expr(pair)),
                _ => unreachable!(),
            })
            .rfold(TT(tt_loc), |a, (loc, x)| {
                Tuple(loc, Box::new(x), Box::new(a))
            })
    }

    fn partial_let(&self, pairs: &mut Pairs<Rule>) -> (Var, Option<Box<Expr>>, Box<Expr>) {
        let id = Var::from(pairs.next().unwrap());
        let mut typ = None;
        let type_or_expr = pairs.next().unwrap();
        let tm = match type_or_expr.as_rule() {
            Rule::type_expr => {
                typ = Some(Box::new(self.type_expr(type_or_expr)));
                self.expr(pairs.next().unwrap())
            }
            Rule::expr => self.expr(type_or_expr),
            _ => unreachable!(),
        };
        (id, typ, Box::new(tm))
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
