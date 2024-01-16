use std::collections::HashMap;
use std::path::PathBuf;

use pest::iterators::{Pair, Pairs};
use pest::pratt_parser::{Assoc, Op, PrattParser};

use crate::theory::abs::data::Dir;
use crate::theory::abs::def::Def;
use crate::theory::abs::def::{Body, ImplementsBody};
use crate::theory::conc::data::ArgInfo::{NamedImplicit, UnnamedExplicit, UnnamedImplicit};
use crate::theory::conc::data::{ArgInfo, Expr};
use crate::theory::conc::load::ImportedPkg::Vendor;
use crate::theory::conc::load::{Import, ImportedDefs, ImportedPkg, ModuleID};
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::{Loc, Param, Tele, Var};
use crate::Rule;

pub struct Trans {
    pratt: PrattParser<Rule>,
}

impl Default for Trans {
    fn default() -> Self {
        Self {
            pratt: PrattParser::new()
                .op(Op::infix(Rule::infix_or, Assoc::Left))
                .op(Op::infix(Rule::infix_and, Assoc::Left))
                .op(Op::infix(Rule::infix_eq, Assoc::Left)
                    | Op::infix(Rule::infix_neq, Assoc::Left)
                    | Op::infix(Rule::infix_le, Assoc::Left)
                    | Op::infix(Rule::infix_ge, Assoc::Left)
                    | Op::infix(Rule::infix_lt, Assoc::Left)
                    | Op::infix(Rule::infix_gt, Assoc::Left))
                .op(Op::infix(Rule::infix_add, Assoc::Left)
                    | Op::infix(Rule::infix_sub, Assoc::Left))
                .op(Op::prefix(Rule::prefix_not)),
        }
    }
}

impl Trans {
    pub fn file(&self, mut f: Pairs<Rule>) -> (Vec<Import>, Vec<Def<Expr>>) {
        let mut imports = Vec::default();
        let mut defs = Vec::default();
        for d in f.next().unwrap().into_inner() {
            match d.as_rule() {
                Rule::import_std | Rule::import_vendor | Rule::import_local => {
                    imports.push(self.import(d))
                }
                Rule::fn_def => defs.push(self.fn_def(d, None)),
                Rule::fn_postulate => defs.push(self.fn_postulate(d)),
                Rule::type_postulate => defs.push(self.type_postulate(d)),
                Rule::type_alias => defs.push(self.type_alias(d)),
                Rule::interface_def => defs.extend(self.interface_def(d)),
                Rule::implements_def => defs.extend(self.implements_def(d)),
                Rule::const_def => defs.push(self.const_def(d)),
                Rule::class_def => defs.extend(self.class_def(d)),
                Rule::EOI => break,
                _ => unreachable!(),
            }
        }
        (imports, defs)
    }

    fn import(&self, d: Pair<Rule>) -> Import {
        use ImportedDefs::*;
        use ImportedPkg::*;

        let mut i = d.into_inner();

        let m = i.next().unwrap();
        let loc = Loc::from(m.as_span());

        let mut modules = PathBuf::default();
        let mut ms = m.into_inner();
        let p = ms.next().unwrap();
        let item = p.as_str().to_string();
        let pkg = match p.as_rule() {
            Rule::std_pkg_id => Std(item),
            Rule::vendor_pkg_id => self.vendor_pkg(p),
            Rule::module_id => {
                modules.push(item);
                Root
            }
            _ => unreachable!(),
        };
        for p in ms {
            if p.as_rule() != Rule::module_id {
                unreachable!()
            }
            modules.push(p.as_str())
        }

        let mut importables = Vec::default();
        for p in i {
            let loc = Loc::from(p.as_span());
            match p.as_rule() {
                Rule::importable => importables.push((loc, p.as_str().to_string())),
                Rule::importable_loaded => {
                    return Import::new(loc, ModuleID { pkg, modules }, Loaded);
                }
                _ => unreachable!(),
            };
        }

        Import::new(
            loc,
            ModuleID { pkg, modules },
            if importables.is_empty() {
                Qualified
            } else {
                Unqualified(importables)
            },
        )
    }

    fn vendor_pkg(&self, v: Pair<Rule>) -> ImportedPkg {
        let mut p = v.into_inner();
        Vendor(
            p.next().unwrap().as_str().to_string(),
            p.next().unwrap().as_str().to_string(),
        )
    }

    fn fn_def(&self, f: Pair<Rule>, this: Option<(Expr, Tele<Expr>)>) -> Def<Expr> {
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
                    typ: Box::new(Self::wrap_implicit_apps(&implicits, ty)),
                },
            );
            tele.extend(implicits);
        }

        for p in pairs {
            match p.as_rule() {
                Rule::row_id => tele.push(Self::row_param(p)),
                Rule::implicit_id => tele.push(Self::implicit_param(p)),
                Rule::hkt_param => tele.push(Self::hkt_param(p)),
                Rule::param => untupled.push(Loc::from(p.as_span()), self.param(p)),
                Rule::type_expr => ret = Box::new(self.type_expr(p)),
                Rule::fn_body => {
                    body = Some(self.fn_body(p, false));
                    break;
                }
                Rule::pred => preds.push(self.pred(p)),
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

    fn fn_postulate(&self, f: Pair<Rule>) -> Def<Expr> {
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
                Rule::implicit_id => tele.push(Self::implicit_param(p)),
                Rule::param => untupled.push(Loc::from(p.as_span()), self.param(p)),
                Rule::type_expr => ret = Box::new(self.type_expr(p)),
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

    fn type_postulate(&self, t: Pair<Rule>) -> Def<Expr> {
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

    fn type_alias(&self, t: Pair<Rule>) -> Def<Expr> {
        use Body::*;
        use Expr::*;

        let loc = Loc::from(t.as_span());
        let mut pairs = t.into_inner();

        let name = Var::from(pairs.next().unwrap());
        let mut tele = Tele::default();
        let mut target = None;
        for p in pairs {
            match p.as_rule() {
                Rule::row_id => tele.push(Self::row_param(p)),
                Rule::implicit_id => tele.push(Self::implicit_param(p)),
                Rule::type_expr => target = Some(self.type_expr(p)),
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
                Box::new(Unresolved(loc, None, p.var.clone())),
            );
        }
        e
    }

    fn interface_def(&self, i: Pair<Rule>) -> Vec<Def<Expr>> {
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
                Rule::row_id => im_tele.push(Self::row_param(p)),
                Rule::implicit_id => im_tele.push(Self::implicit_param(p)),
                Rule::interface_fn => {
                    let mut d = self.fn_postulate(p);
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

    fn implements_def(&self, i: Pair<Rule>) -> Vec<Def<Expr>> {
        use Body::*;
        use Expr::*;

        let loc = Loc::from(i.as_span());
        let mut pairs = i.into_inner();

        let mut defs = Vec::default();

        let i = Var::from(pairs.next().unwrap());
        let im = {
            let p = pairs.next().unwrap();
            match p.as_rule() {
                Rule::tyref => Self::unresolved(p),
                Rule::primitive_type => self.primitive_type(p),
                _ => unreachable!(),
            }
        };

        let mut fns = HashMap::default();
        for p in pairs {
            let mut def = self.fn_def(p, None);
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
            body: Implements(Box::new(ImplementsBody {
                i: (i, Box::new(im)),
                fns,
            })),
        });
        defs
    }

    fn const_def(&self, c: Pair<Rule>) -> Def<Expr> {
        use Body::*;
        use Expr::*;
        let loc = Loc::from(c.as_span());
        let mut name = Var::unbound();
        let mut ret = Box::new(Unit(loc));
        let mut is_annotated = false;
        for p in c.into_inner() {
            match p.as_rule() {
                Rule::fn_id => name = Var::from(p),
                Rule::type_expr => {
                    is_annotated = true;
                    ret = Box::new(self.type_expr(p))
                }
                Rule::expr => {
                    return Def {
                        loc,
                        name,
                        tele: Default::default(),
                        ret,
                        body: Const(is_annotated, self.expr(p)),
                    };
                }
                _ => break,
            }
        }
        unreachable!()
    }

    fn class_def(&self, c: Pair<Rule>) -> Vec<Def<Expr>> {
        use Body::*;
        use Expr::*;

        let loc = Loc::from(c.as_span());
        let mut pairs = c.into_inner();

        let name = Var::from(pairs.next().unwrap());

        let mut tele = Tele::default();
        let mut members = Vec::default();
        let mut methods = Vec::default();
        let mut method_names = Vec::default();
        let mut ctor_body_obj = Vec::default();
        let mut ctor_params = UntupledParams::new(loc);

        for p in pairs {
            match p.as_rule() {
                Rule::implicit_id => tele.push(Self::implicit_param(p)),
                Rule::class_member => {
                    let loc = Loc::from(p.as_span());
                    let mut f = p.into_inner();
                    let m = Var::from(f.next().unwrap());
                    let typ = self.type_expr(f.next().unwrap());
                    members.push((loc, m.to_string(), typ.clone()));
                    ctor_body_obj.push((m.to_string(), Unresolved(loc, None, m.clone())));
                    ctor_params.push(
                        loc,
                        Param {
                            var: m,
                            info: Explicit,
                            typ: Box::new(typ),
                        },
                    );
                }
                Rule::class_method => {
                    let loc = Loc::from(p.as_span());
                    let mut m =
                        self.fn_def(p, Some((Unresolved(loc, None, name.clone()), tele.clone())));
                    let method_name = name.method(m.name);
                    m.name = method_name.clone();
                    m.body = match m.body {
                        Fn(f) => Method(name.clone(), f),
                        _ => unreachable!(),
                    };
                    methods.push(m);
                    method_names.push(method_name);
                }
                _ => unreachable!(),
            }
        }

        let ctor_loc = ctor_params.0;
        let ctor_param_vars = ctor_params.unresolved();
        let ctor_tupled_params = Param::from(ctor_params);
        let ctor_body = Fn(Expr::wrap_tuple_lets(
            ctor_loc,
            &ctor_tupled_params.var,
            ctor_param_vars,
            Obj(loc, Box::new(Fields(loc, ctor_body_obj))),
        ));
        let mut ctor_tele = tele.clone();
        ctor_tele.push(ctor_tupled_params);

        let mut defs = vec![
            Def {
                loc,
                name: name.clone(),
                tele,
                ret: Box::new(Univ(loc)),
                body: Class(members, method_names),
            },
            Def {
                loc,
                name: name.ctor(),
                tele: ctor_tele,
                ret: Box::new(Unresolved(loc, None, name)),
                body: ctor_body,
            },
        ];
        defs.extend(methods);
        defs
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
            Rule::primitive_type => self.primitive_type(p),
            Rule::object_type_ref => Object(
                loc,
                Box::new(Self::unresolved(p.into_inner().next().unwrap())),
            ),
            Rule::object_type_literal => Object(loc, Box::new(self.fields(p))),
            Rule::enum_type_ref => Enum(
                loc,
                Box::new(Self::unresolved(p.into_inner().next().unwrap())),
            ),
            Rule::enum_type_literal => Enum(loc, Box::new(self.fields(p))),
            Rule::type_app => self.type_app(p),
            Rule::tyref => self.maybe_qualified(p),
            Rule::paren_type_expr => self.type_expr(p.into_inner().next().unwrap()),
            Rule::hole => Hole(loc),
            _ => unreachable!(),
        }
    }

    fn primitive_type(&self, p: Pair<Rule>) -> Expr {
        use Expr::*;
        let loc = Loc::from(p.as_span());
        let t = p.into_inner().next().unwrap();
        match t.as_rule() {
            Rule::string_type => String(loc),
            Rule::number_type => Number(loc),
            Rule::bigint_type => BigInt(loc),
            Rule::boolean_type => Boolean(loc),
            Rule::unit_type => Unit(loc),
            _ => unreachable!(),
        }
    }

    fn type_app(&self, a: Pair<Rule>) -> Expr {
        use Expr::*;

        let mut pairs = a.into_inner();
        let f = pairs.next().unwrap();
        let f = match f.as_rule() {
            Rule::type_expr => self.type_expr(f),
            Rule::tyref => self.maybe_qualified(f),
            _ => unreachable!(),
        };

        pairs
            .map(|arg| {
                let loc = Loc::from(arg.as_span());
                let (i, e) = match arg.as_rule() {
                    Rule::row_arg => self.row_arg(arg),
                    Rule::type_arg => self.type_arg(arg),
                    _ => unreachable!(),
                };
                (loc, i, e)
            })
            .fold(f, |a, (loc, i, x)| App(loc, Box::new(a), i, Box::new(x)))
    }

    fn pred(&self, pred: Pair<Rule>) -> Param<Expr> {
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
                Rule::constraint_expr => Box::new(ImplementsOf(loc, Box::new(self.type_app(p)))),
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
        let p = e.into_inner().next().unwrap();
        match p.as_rule() {
            Rule::row_id => Self::unresolved(p),
            Rule::row_literal => self.fields(p),
            Rule::paren_row_expr => self.row_expr(p.into_inner().next().unwrap()),
            _ => unreachable!(),
        }
    }

    fn type_arg(&self, a: Pair<Rule>) -> (ArgInfo, Expr) {
        let mut p = a.into_inner();
        let id_or_type = p.next().unwrap();
        match id_or_type.as_rule() {
            Rule::type_expr => (UnnamedImplicit, self.type_expr(id_or_type)),
            Rule::tyref => (
                NamedImplicit(Var::from(id_or_type)),
                self.type_expr(p.next().unwrap()),
            ),
            _ => unreachable!(),
        }
    }

    fn row_arg(&self, a: Pair<Rule>) -> (ArgInfo, Expr) {
        let mut p = a.into_inner();
        let id_or_fields = p.next().unwrap();
        match id_or_fields.as_rule() {
            Rule::row_literal => (UnnamedImplicit, self.fields(id_or_fields)),
            Rule::row_id => (
                NamedImplicit(Var::from(id_or_fields)),
                self.fields(p.next().unwrap()),
            ),
            _ => unreachable!(),
        }
    }

    fn fn_body(&self, b: Pair<Rule>, force_returns_unit: bool) -> Expr {
        use Expr::*;

        let p = b.into_inner().next().unwrap();
        let loc = Loc::from(p.as_span());
        match p.as_rule() {
            Rule::fn_body_let => {
                let mut l = p.into_inner();
                let (id, typ, tm) = self.partial_let(&mut l);
                Let(
                    loc,
                    id,
                    typ,
                    Box::new(tm),
                    Box::new(self.fn_body(l.next().unwrap(), force_returns_unit)),
                )
            }
            Rule::fn_body_unit_let => {
                let mut l = p.into_inner();
                UnitLet(
                    loc,
                    Box::new(self.expr(l.next().unwrap())),
                    Box::new(self.fn_body(l.next().unwrap(), force_returns_unit)),
                )
            }
            Rule::fn_body_object_assign => {
                let mut pairs = p.into_inner();
                let a = pairs.next().unwrap();
                let a_loc = Loc::from(a.as_span());
                let a_var = Var::from(a);
                let n = pairs.next().unwrap();
                let n_loc = Loc::from(n.as_span());
                let fields = vec![(n.as_str().to_string(), self.expr(pairs.next().unwrap()))];
                let expr = Concat(
                    loc,
                    Box::new(Unresolved(a_loc, None, a_var.clone())),
                    Box::new(Obj(n_loc, Box::new(Fields(n_loc, fields)))),
                );
                let body = self.fn_body(pairs.next().unwrap(), force_returns_unit);
                Let(loc, a_var, None, Box::new(expr), Box::new(body))
            }
            Rule::fn_body_while => {
                let mut pairs = p.into_inner();
                While(
                    loc,
                    Box::new(self.expr(pairs.next().unwrap())),
                    Box::new(self.branch(pairs.next().unwrap())),
                    Box::new(self.fn_body(pairs.next().unwrap(), false)),
                )
            }
            Rule::expr if force_returns_unit => self.expr(p),
            Rule::fn_body_ret if !force_returns_unit => {
                p.into_inner().next().map_or(TT(loc), |e| self.expr(e))
            }
            _ => unreachable!(),
        }
    }

    fn expr(&self, e: Pair<Rule>) -> Expr {
        self.pratt
            .map_primary(|p| self.primary_expr(p))
            .map_infix(|lhs, op, rhs| {
                let loc = Loc::from(op.as_span());
                match op.as_rule() {
                    Rule::infix_or => Self::infix_app(loc, "__or__", lhs, rhs),
                    Rule::infix_and => Self::infix_app(loc, "__and__", lhs, rhs),
                    Rule::infix_eq => Self::infix_app(loc, "__eq__", lhs, rhs),
                    Rule::infix_neq => Self::infix_app(loc, "__neq__", lhs, rhs),
                    Rule::infix_le => Self::infix_app(loc, "__le__", lhs, rhs),
                    Rule::infix_ge => Self::infix_app(loc, "__ge__", lhs, rhs),
                    Rule::infix_lt => Self::infix_app(loc, "__lt__", lhs, rhs),
                    Rule::infix_gt => Self::infix_app(loc, "__gt__", lhs, rhs),
                    Rule::infix_add => Self::infix_app(loc, "__add__", lhs, rhs),
                    Rule::infix_sub => Self::infix_app(loc, "__sub__", lhs, rhs),
                    _ => unreachable!(),
                }
            })
            .map_prefix(|op, x| {
                let loc = Loc::from(op.as_span());
                match op.as_rule() {
                    Rule::prefix_not => Self::prefix_app(loc, "__not__", x),
                    _ => unreachable!(),
                }
            })
            .parse(e.into_inner())
    }

    fn infix_app(loc: Loc, r: &'static str, lhs: Expr, rhs: Expr) -> Expr {
        use Expr::*;
        App(
            loc,
            Box::new(Unresolved(loc, None, Var::new(r))),
            UnnamedExplicit,
            Box::new(Tuple(
                lhs.loc(),
                Box::new(lhs),
                Box::new(Tuple(rhs.loc(), Box::new(rhs), Box::new(TT(loc)))),
            )),
        )
    }

    fn prefix_app(loc: Loc, r: &'static str, x: Expr) -> Expr {
        use Expr::*;
        App(
            loc,
            Box::new(Unresolved(loc, None, Var::new(r))),
            UnnamedExplicit,
            Box::new(Tuple(x.loc(), Box::new(x), Box::new(TT(loc)))),
        )
    }

    fn primary_expr(&self, e: Pair<Rule>) -> Expr {
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
                    Box::new(self.expr(pairs.next().unwrap())),
                    Box::new(self.branch(pairs.next().unwrap())),
                    Box::new(self.branch(pairs.next().unwrap())),
                )
            }
            Rule::rev_app => {
                let mut pairs = p.into_inner();
                let arg = pairs.next().unwrap();
                pairs
                    .fold(
                        (
                            Loc::from(arg.as_span()),
                            match arg.as_rule() {
                                Rule::expr => self.expr(arg),
                                Rule::idref => self.maybe_qualified(arg),
                                Rule::new_expr => self.new_expr(arg),
                                _ => unreachable!(),
                            },
                        ),
                        |(loc, arg), p| (Loc::from(p.as_span()), self.app(p, Some((loc, arg)))),
                    )
                    .1
            }
            Rule::object_literal => self.object_literal(p),
            Rule::object_concat => {
                let mut pairs = p.into_inner();
                let a = self.object_operand(pairs.next().unwrap());
                let b = self.object_operand(pairs.next().unwrap());
                Concat(loc, Box::new(a), Box::new(b))
            }
            Rule::object_access => {
                let mut pairs = p.into_inner();
                let a = self.object_operand(pairs.next().unwrap());
                let n = pairs.next().unwrap().as_str().to_string();
                App(loc, Box::new(Access(loc, n)), UnnamedExplicit, Box::new(a))
            }
            Rule::object_cast => Downcast(
                loc,
                Box::new(self.object_operand(p.into_inner().next().unwrap())),
            ),
            Rule::enum_variant => self.enum_variant(p),
            Rule::enum_cast => Upcast(
                loc,
                Box::new(self.enum_operand(p.into_inner().next().unwrap())),
            ),
            Rule::enum_switch => {
                let mut pairs = p.into_inner();
                let e = self.expr(pairs.next().unwrap().into_inner().next().unwrap());
                let mut cases = Vec::default();
                for p in pairs {
                    let mut c = p.into_inner();
                    let n = c.next().unwrap().as_str().to_string();
                    let mut v = None;
                    let mut body = None;
                    for p in c {
                        match p.as_rule() {
                            Rule::param_id => v = Some(Var::from(p)),
                            Rule::expr => body = Some(self.expr(p)),
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
                        Rule::param_id => vars.push(Self::unresolved(p)),
                        Rule::lambda_body => {
                            let b = p.into_inner().next().unwrap();
                            body = Some(match b.as_rule() {
                                Rule::expr => self.expr(b),
                                Rule::fn_body => self.fn_body(b, false),
                                _ => unreachable!(),
                            });
                            break;
                        }
                        _ => unreachable!(),
                    }
                }
                TupledLam(loc, vars, Box::new(body.unwrap()))
            }
            Rule::new_expr => self.new_expr(p),
            Rule::app => self.app(p, None),
            Rule::tt => TT(loc),
            Rule::idref => self.maybe_qualified(p),
            Rule::paren_expr => self.expr(p.into_inner().next().unwrap()),
            Rule::hole => Hole(loc),
            _ => unreachable!(),
        }
    }

    fn new_expr(&self, e: Pair<Rule>) -> Expr {
        use Expr::*;
        let mut pairs = e.into_inner();
        let cls = match self.maybe_qualified(pairs.next().unwrap()) {
            Unresolved(loc, m, v) => Unresolved(loc, m, v.ctor()),
            _ => unreachable!(),
        };
        pairs
            .map(|arg| {
                let loc = Loc::from(arg.as_span());
                let (i, e) = match arg.as_rule() {
                    Rule::type_arg => self.type_arg(arg),
                    Rule::args => (UnnamedExplicit, self.tupled_args(arg)),
                    _ => unreachable!(),
                };
                (loc, i, e)
            })
            .fold(cls, |a, (loc, i, x)| App(loc, Box::new(a), i, Box::new(x)))
    }

    fn branch(&self, b: Pair<Rule>) -> Expr {
        use Expr::*;

        let p = b.into_inner().next().unwrap();
        let loc = Loc::from(p.as_span());
        match p.as_rule() {
            Rule::branch_let => {
                let mut l = p.into_inner();
                let (id, typ, tm) = self.partial_let(&mut l);
                Let(
                    loc,
                    id,
                    typ,
                    Box::new(tm),
                    Box::new(self.branch(l.next().unwrap())),
                )
            }
            Rule::branch_unit_let => {
                let mut l = p.into_inner();
                UnitLet(
                    loc,
                    Box::new(self.expr(l.next().unwrap())),
                    Box::new(self.branch(l.next().unwrap())),
                )
            }
            Rule::branch_object_assign => {
                let mut pairs = p.into_inner();
                let a = pairs.next().unwrap();
                let a_loc = Loc::from(a.as_span());
                let a_var = Var::from(a);
                let n = pairs.next().unwrap();
                let n_loc = Loc::from(n.as_span());
                let fields = vec![(n.as_str().to_string(), self.expr(pairs.next().unwrap()))];
                let expr = Concat(
                    loc,
                    Box::new(Unresolved(a_loc, None, a_var.clone())),
                    Box::new(Obj(n_loc, Box::new(Fields(n_loc, fields)))),
                );
                let body = self.branch(pairs.next().unwrap());
                Let(loc, a_var, None, Box::new(expr), Box::new(body))
            }
            Rule::branch_while => {
                let mut pairs = p.into_inner();
                While(
                    loc,
                    Box::new(self.expr(pairs.next().unwrap())),
                    Box::new(self.branch(pairs.next().unwrap())),
                    Box::new(self.branch(pairs.next().unwrap())),
                )
            }
            Rule::expr => self.expr(p),
            _ => unreachable!(),
        }
    }

    fn app(&self, a: Pair<Rule>, mut rev_arg: Option<(Loc, Expr)>) -> Expr {
        use Expr::*;

        let mut pairs = a.into_inner();
        let f = pairs.next().unwrap();
        let f = match f.as_rule() {
            Rule::expr => self.expr(f),
            Rule::idref => self.maybe_qualified(f),
            _ => unreachable!(),
        };

        pairs
            .map(|arg| {
                let loc = Loc::from(arg.as_span());
                let mut is_rev = false;
                let (i, e) = match arg.as_rule() {
                    Rule::row_arg => self.row_arg(arg),
                    Rule::type_arg => self.type_arg(arg),
                    Rule::args => {
                        let mut args = self.tupled_args(arg);
                        if let Some((loc, a)) = &rev_arg {
                            args = Tuple(*loc, Box::new(a.clone()), Box::new(args));
                            is_rev = true;
                        }
                        rev_arg = None; // only guarantee first reverse application
                        (UnnamedExplicit, args)
                    }
                    _ => unreachable!(),
                };
                (loc, is_rev, i, e)
            })
            .fold(f, |f, (loc, is_rev, i, x)| {
                if is_rev {
                    RevApp(loc, Box::new(f), Box::new(x))
                } else {
                    App(loc, Box::new(f), i, Box::new(x))
                }
            })
    }

    fn maybe_qualified(&self, p: Pair<Rule>) -> Expr {
        use Expr::*;
        let loc = Loc::from(p.as_span());
        let mut i = p.into_inner();
        let id = i.next().unwrap();
        match id.as_rule() {
            Rule::qualifier => {
                Unresolved(loc, Some(self.qualifier(id)), Var::from(i.next().unwrap()))
            }
            _ => Unresolved(loc, None, Var::from(id)),
        }
    }

    fn qualifier(&self, q: Pair<Rule>) -> ModuleID {
        use ImportedPkg::*;
        let mut pairs = q.into_inner();
        let prefix = pairs.next().unwrap();
        let pkg = match prefix.as_rule() {
            Rule::std_pkg_id => Std(prefix.as_str().to_string()),
            Rule::vendor_pkg_id => self.vendor_pkg(prefix),
            Rule::root_prefix => Root,
            _ => unreachable!(),
        };
        let mut modules = PathBuf::default();
        for p in pairs {
            modules.push(p.as_str())
        }
        ModuleID { pkg, modules }
    }

    fn unresolved(p: Pair<Rule>) -> Expr {
        use Expr::*;
        Unresolved(Loc::from(p.as_span()), None, Var::from(p))
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

        let mut fields = Vec::default();
        for pair in p.into_inner() {
            let mut f = pair.into_inner();
            let id = f.next().unwrap().as_str().to_string();
            let typ = f.next().map_or(Unit(loc), |e| self.type_expr(e));
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

    fn object_literal(&self, l: Pair<Rule>) -> Expr {
        use Expr::*;
        let loc = Loc::from(l.as_span());
        Obj(
            loc,
            Box::new(Fields(loc, l.into_inner().map(|e| self.label(e)).collect())),
        )
    }

    fn object_operand(&self, o: Pair<Rule>) -> Expr {
        let p = o.into_inner().next().unwrap();
        match p.as_rule() {
            Rule::app => self.app(p, None),
            Rule::object_literal => self.object_literal(p),
            Rule::idref => self.maybe_qualified(p),
            Rule::paren_expr => self.expr(p.into_inner().next().unwrap()),
            _ => unreachable!(),
        }
    }

    fn enum_variant(&self, v: Pair<Rule>) -> Expr {
        use Expr::*;
        let loc = Loc::from(v.as_span());
        let mut pairs = v.into_inner();
        let n = pairs.next().unwrap().as_str().to_string();
        let a = pairs
            .next()
            .map_or(TT(loc), |p| self.expr(p.into_inner().next().unwrap()));
        Variant(loc, n, Box::new(a))
    }

    fn enum_operand(&self, o: Pair<Rule>) -> Expr {
        let p = o.into_inner().next().unwrap();
        match p.as_rule() {
            Rule::app => self.app(p, None),
            Rule::enum_variant => self.enum_variant(p),
            Rule::idref => self.maybe_qualified(p),
            Rule::paren_expr => self.expr(p.into_inner().next().unwrap()),
            _ => unreachable!(),
        }
    }

    fn tupled_args(&self, a: Pair<Rule>) -> Expr {
        use Expr::*;
        let loc = Loc::from(a.as_span());
        a.into_inner()
            .map(|pair| match pair.as_rule() {
                Rule::expr => (Loc::from(pair.as_span()), self.expr(pair)),
                _ => unreachable!(),
            })
            .rfold(TT(loc), |a, (loc, x)| Tuple(loc, Box::new(x), Box::new(a)))
    }

    fn partial_let(&self, pairs: &mut Pairs<Rule>) -> (Var, Option<Box<Expr>>, Expr) {
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
        (id, typ, tm)
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

    fn unresolved(&self) -> Vec<Expr> {
        use Expr::*;
        self.1
            .iter()
            .map(|(loc, p)| Unresolved(*loc, None, p.var.clone()))
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
