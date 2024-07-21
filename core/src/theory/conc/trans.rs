use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::OnceLock;

use pest::iterators::{Pair, Pairs};
use pest::pratt_parser::{Assoc, Op, PrattParser};

use crate::theory::abs::def::{Body, InstanceBody};
use crate::theory::abs::def::{ClassMembers, Def};
use crate::theory::conc::data::ArgInfo::{NamedImplicit, UnnamedExplicit, UnnamedImplicit};
use crate::theory::conc::data::{ArgInfo, Catch, Expr};
use crate::theory::conc::load::ImportedPkg::Vendor;
use crate::theory::conc::load::{Import, ImportedDefs, ImportedPkg, ModuleID};
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::{Loc, Param, Tele, Var};
use crate::Rule;

fn type_pratt() -> &'static PrattParser<Rule> {
    static ONCE: OnceLock<PrattParser<Rule>> = OnceLock::new();
    ONCE.get_or_init(|| PrattParser::new().op(Op::infix(Rule::infix_concat, Assoc::Left)))
}

fn expr_pratt() -> &'static PrattParser<Rule> {
    static ONCE: OnceLock<PrattParser<Rule>> = OnceLock::new();
    ONCE.get_or_init(|| {
        PrattParser::new()
            .op(Op::infix(Rule::infix_or, Assoc::Left))
            .op(Op::infix(Rule::infix_and, Assoc::Left))
            .op(Op::infix(Rule::infix_eq, Assoc::Left)
                | Op::infix(Rule::infix_neq, Assoc::Left)
                | Op::infix(Rule::infix_le, Assoc::Left)
                | Op::infix(Rule::infix_ge, Assoc::Left)
                | Op::infix(Rule::infix_lt, Assoc::Left)
                | Op::infix(Rule::infix_gt, Assoc::Left))
            .op(Op::infix(Rule::infix_add, Assoc::Left) | Op::infix(Rule::infix_sub, Assoc::Left))
            .op(Op::infix(Rule::infix_mul, Assoc::Left)
                | Op::infix(Rule::infix_div, Assoc::Left)
                | Op::infix(Rule::infix_mod, Assoc::Left))
            .op(Op::infix(Rule::infix_concat, Assoc::Left))
            .op(Op::infix(Rule::infix_at, Assoc::Left))
            .op(Op::prefix(Rule::prefix_not) | Op::prefix(Rule::prefix_neg))
            .op(Op::prefix(Rule::prefix_typeof) | Op::prefix(Rule::prefix_keyof))
    })
}

#[derive(Default)]
pub struct Trans {
    predicates: Vec<Param<Expr>>,
}

impl Trans {
    pub fn file(&mut self, mut f: Pairs<Rule>) -> (Vec<Import>, Vec<Def<Expr>>) {
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
                Rule::instance_def => defs.extend(self.instance_def(d)),
                Rule::const_def => defs.push(self.const_def(d)),
                Rule::class_def => defs.extend(self.class_def(d)),
                Rule::namespace_def => defs.extend(self.namespace_def(d)),
                Rule::type_verify => defs.push(self.type_verify(d)),
                Rule::fn_verify => defs.push(self.fn_verify(d)),
                Rule::EOI => break,
                _ => unreachable!(),
            }
        }
        (imports, defs)
    }

    fn import(&mut self, d: Pair<Rule>) -> Import {
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

    fn vendor_pkg(&mut self, v: Pair<Rule>) -> ImportedPkg {
        let mut p = v.into_inner();
        Vendor(
            p.next().unwrap().as_str().to_string(),
            p.next().unwrap().as_str().to_string(),
        )
    }

    fn fn_def(&mut self, f: Pair<Rule>, this: Option<(Expr, Tele<Expr>)>) -> Def<Expr> {
        use Body::*;
        use Expr::*;

        self.predicates.clear();

        let loc = Loc::from(f.as_span());
        let mut pairs = f.into_inner();

        let (name, eff) = self.name_maybe_async(&mut pairs);

        let mut tele = Tele::default();
        let mut untupled = UntupledParams::new(loc);
        let mut untupled_ends = None;
        let mut preds = Tele::default();
        let mut capabilities = Vec::default();
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
                Rule::variadic_param => match self.variadic_param(p) {
                    VariadicParam::Named(loc, p) => untupled.push(loc, p),
                    VariadicParam::Unnamed(t) => untupled_ends = Some(t),
                },
                Rule::type_expr => ret = Box::new(self.type_expr(p)),
                Rule::fn_body => {
                    body = Some(self.fn_body(p));
                    break;
                }
                Rule::pred => preds.push(self.pred(p)),
                Rule::capability => capabilities.push(Self::unresolved(p)),
                _ => unreachable!(),
            }
        }

        preds.extend(self.predicates.clone());

        let untupled_vars = untupled.unresolved();
        let untupled_loc = untupled.0;
        let tupled_param = untupled.param(untupled_ends);
        let body = Fn(Box::new(Expr::wrap_tuple_binds(
            untupled_loc,
            tupled_param.var.clone(),
            untupled_vars,
            body.unwrap(),
        )));
        tele.push(tupled_param);
        tele.extend(preds);

        Def {
            loc,
            name,
            tele,
            eff: Self::concat_effects(*eff, capabilities),
            ret,
            body,
        }
    }

    fn name_maybe_async(&mut self, pairs: &mut Pairs<Rule>) -> (Var, Box<Expr>) {
        let (p, eff) = self.name_pair_maybe_async(pairs);
        (Var::from(p), eff)
    }

    fn idref_maybe_async(&mut self, pairs: &mut Pairs<Rule>) -> (Expr, Box<Expr>) {
        let (p, eff) = self.name_pair_maybe_async(pairs);
        (self.maybe_qualified(p), eff)
    }

    fn name_pair_maybe_async<'a>(
        &mut self,
        pairs: &mut Pairs<'a, Rule>,
    ) -> (Pair<'a, Rule>, Box<Expr>) {
        let p = pairs.next().unwrap();
        let loc = Loc::from(p.as_span());
        match p.as_rule() {
            Rule::is_async => (pairs.next().unwrap(), Box::new(Expr::async_effect(loc))),
            _ => (p, Box::new(Expr::Pure(loc))),
        }
    }

    fn concat_effects(async_eff: Expr, capabilities: Vec<Expr>) -> Box<Expr> {
        if capabilities.is_empty() {
            return Box::new(async_eff);
        }
        if let Expr::Pure(loc) = async_eff {
            return Box::new(Expr::Effect(loc, capabilities));
        }
        match async_eff {
            Expr::Effect(loc, mut es) => {
                es.extend(capabilities);
                Box::new(Expr::Effect(loc, es))
            }
            _ => unreachable!(),
        }
    }

    fn fn_signature(
        &mut self,
        pairs: Pairs<Rule>,
        loc: Loc,
        async_eff: Expr,
    ) -> (Tele<Expr>, Box<Expr>, Box<Expr>) {
        let mut tele = Tele::default();
        let mut untupled = UntupledParams::new(loc);
        let mut untupled_ends = None;
        let mut preds = Tele::default();
        let mut capabilities = Vec::default();
        let mut ret = Box::new(Expr::Unit(loc));

        for p in pairs {
            match p.as_rule() {
                Rule::row_id => tele.push(Self::row_param(p)),
                Rule::implicit_id => tele.push(Self::implicit_param(p)),
                Rule::hkt_param => tele.push(Self::hkt_param(p)),
                Rule::param => untupled.push(Loc::from(p.as_span()), self.param(p)),
                Rule::variadic_param => match self.variadic_param(p) {
                    VariadicParam::Named(loc, p) => untupled.push(loc, p),
                    VariadicParam::Unnamed(t) => untupled_ends = Some(t),
                },
                Rule::type_expr => ret = Box::new(self.type_expr(p)),
                Rule::pred => preds.push(self.pred(p)),
                Rule::capability => capabilities.push(Self::unresolved(p)),
                _ => unreachable!(),
            }
        }
        tele.push(untupled.param(untupled_ends));
        tele.extend(preds);

        (tele, Self::concat_effects(async_eff, capabilities), ret)
    }

    fn fn_postulate(&mut self, f: Pair<Rule>) -> Def<Expr> {
        let loc = Loc::from(f.as_span());
        let mut pairs = f.into_inner();
        let (name, eff) = self.name_maybe_async(&mut pairs);
        let (tele, eff, ret) = self.fn_signature(pairs, loc, *eff);
        Def {
            loc,
            name,
            tele,
            eff,
            ret,
            body: Body::Postulate,
        }
    }

    fn type_postulate(&mut self, t: Pair<Rule>) -> Def<Expr> {
        use Body::*;
        use Expr::*;
        let loc = Loc::from(t.as_span());
        let mut pairs = t.into_inner();
        let name = Var::from(pairs.next().unwrap());
        let mut tele = Tele::default();
        for p in pairs {
            match p.as_rule() {
                Rule::row_id => tele.push(Self::row_param(p)),
                Rule::implicit_id => tele.push(Self::implicit_param(p)),
                _ => unreachable!(),
            }
        }
        Def {
            loc,
            name,
            tele,
            eff: Box::new(Pure(loc)),
            ret: Box::new(Univ(loc)),
            body: Postulate,
        }
    }

    fn type_alias(&mut self, t: Pair<Rule>) -> Def<Expr> {
        use Body::*;
        use Expr::*;

        let loc = Loc::from(t.as_span());
        let mut pairs = t.into_inner();

        let name = Var::from(pairs.next().unwrap());
        let mut tele = Tele::default();
        let mut target = None;
        let mut implements = None;
        for p in pairs {
            match p.as_rule() {
                Rule::row_id => tele.push(Self::row_param(p)),
                Rule::implicit_id => tele.push(Self::implicit_param(p)),
                Rule::type_expr => target = Some(self.type_expr(p)),
                Rule::implements => implements = Some(Box::new(self.maybe_qualified(p))),
                _ => unreachable!(),
            }
        }

        Def {
            loc,
            name,
            tele,
            eff: Box::new(Pure(loc)),
            ret: Box::new(Univ(loc)),
            body: Alias {
                ty: Box::new(target.unwrap()),
                implements,
            },
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

    fn interface_def(&mut self, i: Pair<Rule>) -> Vec<Def<Expr>> {
        fn alias_type(loc: Loc, tele: &Tele<Expr>) -> Expr {
            Expr::pi(tele, Univ(loc))
        }

        use Body::*;
        use Expr::*;

        let loc = Loc::from(i.as_span());
        let mut pairs = i.into_inner();

        let mut is_capability = false;
        let name_pair = {
            let p = pairs.next().unwrap();
            if p.as_rule() == Rule::is_capability {
                is_capability = true;
                pairs.next().unwrap()
            } else {
                p
            }
        };
        let name_loc = Loc::from(name_pair.as_span());
        let ret = Box::new(Univ(Loc::from(name_pair.as_span())));
        let name = Var::from(name_pair);

        let mut inst_tele = Tele::default();
        let mut fns = Vec::default();
        let mut fn_defs = Vec::default();

        let mut implements_fns = Vec::default();
        let mut implements_fn_defs = Vec::default();

        for p in pairs {
            match p.as_rule() {
                Rule::row_id => inst_tele.push(Self::row_param(p)),
                Rule::implicit_id => inst_tele.push(Self::implicit_param(p)),
                _ => {
                    let is_implements_fn = match p.as_rule() {
                        Rule::interface_fn => false,
                        Rule::instance_fn => true,
                        _ => unreachable!(),
                    };
                    let mut d = if is_implements_fn {
                        self.fn_def(p, None)
                    } else {
                        self.fn_postulate(p)
                    };
                    let mut tele = vec![Param {
                        var: Var::this(),
                        info: Implicit,
                        typ: Box::new(alias_type(name_loc, &inst_tele)),
                    }];
                    tele.extend(d.tele);
                    d.tele = tele;

                    if is_implements_fn {
                        let mut implements_fn = d.clone();
                        implements_fn.body = match implements_fn.body {
                            Fn(f) => ImplementsFn {
                                name: implements_fn.name.clone(),
                                f,
                            },
                            _ => unreachable!(),
                        };
                        implements_fn.name = implements_fn.name.implements_fn(&name);
                        implements_fns.push(implements_fn.name.clone());
                        implements_fn_defs.push(implements_fn);
                    }

                    d.body = InterfaceFn(name.clone());
                    if is_capability {
                        d.eff = Self::concat_effects(
                            *d.eff,
                            vec![Unresolved(name_loc, None, name.clone())],
                        );
                    }
                    fns.push(d.name.clone());
                    fn_defs.push(d);
                }
            }
        }

        let mut defs = vec![Def {
            loc,
            name: name.clone(),
            tele: vec![Param {
                var: name,
                info: Implicit,
                typ: Box::new(alias_type(name_loc, &inst_tele)),
            }],
            eff: Box::new(Pure(loc)),
            ret,
            body: Interface {
                is_capability,
                fns,
                instances: Default::default(),
                implements: implements_fns,
            },
        }];
        defs.extend(fn_defs);
        defs.extend(implements_fn_defs);
        defs
    }

    fn instance_def(&mut self, i: Pair<Rule>) -> Vec<Def<Expr>> {
        use Body::*;
        use Expr::*;

        let loc = Loc::from(i.as_span());
        let mut pairs = i.into_inner();

        let mut defs = Vec::default();

        let i = Var::from(pairs.next().unwrap());
        let inst = Box::new({
            let p = pairs.next().unwrap();
            match p.as_rule() {
                Rule::tyref => Self::unresolved(p),
                Rule::primitive_type => self.primitive_type(p),
                _ => unreachable!(),
            }
        });

        let mut fns = HashMap::default();
        for p in pairs {
            let mut def = self.fn_def(p, None);
            let fn_name = def.name.instance_fn(&i, &inst);
            fns.insert(def.name.clone(), fn_name.clone());
            def.name = fn_name;
            def.body = match def.body {
                Fn(f) => InstanceFn(f),
                _ => unreachable!(),
            };
            defs.push(def);
        }

        defs.push(Def {
            loc,
            name: i.instance(&inst),
            tele: Default::default(),
            eff: Box::new(Pure(loc)),
            ret: Box::new(Univ(loc)),
            body: Instance(Box::new(InstanceBody { i, inst, fns })),
        });
        defs
    }

    fn const_def(&mut self, c: Pair<Rule>) -> Def<Expr> {
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
                        eff: Box::new(Pure(loc)),
                        ret,
                        body: Constant(is_annotated, Box::new(self.expr(p))),
                    };
                }
                _ => break,
            }
        }
        unreachable!()
    }

    fn class_def(&mut self, c: Pair<Rule>) -> Vec<Def<Expr>> {
        use Body::*;
        use Expr::*;

        let mut pairs = c.into_inner();

        let name_pair = pairs.next().unwrap();
        let loc = Loc::from(name_pair.as_span());
        let name = Var::from(name_pair);

        let mut tele = Tele::default();

        let mut associated = HashMap::default();
        let mut associated_defs = Vec::default();

        let mut members = Vec::default();
        let mut method_defs = Vec::default();
        let mut methods = HashMap::default();
        let mut ctor_body_obj = Vec::default();

        let mut wrapper = None;

        let mut ctor_params = UntupledParams::new(loc);

        for p in pairs {
            match p.as_rule() {
                Rule::implicit_id => tele.push(Self::implicit_param(p)),
                Rule::associated_type => {
                    let mut t = p.into_inner();

                    let typ_name = t.next().unwrap();
                    let typ_name_loc = Loc::from(typ_name.as_span());
                    let typ_var = Var::new(typ_name.as_str());
                    let typ_name = typ_var.to_string();
                    let mangled_typ_var = name.associated(typ_var);

                    let typ = self.type_expr(t.next().unwrap());

                    associated.insert(typ_name, mangled_typ_var.clone());
                    associated_defs.push(Def {
                        loc: typ_name_loc,
                        name: mangled_typ_var,
                        tele: tele.clone(),
                        eff: Box::new(Pure(typ_name_loc)),
                        ret: Box::new(Univ(typ_name_loc)),
                        body: Associated(Box::new(typ)),
                    });
                }
                Rule::class_member => {
                    let loc = Loc::from(p.as_span());
                    let mut f = p.into_inner();
                    let m = Var::from(f.next().unwrap());
                    let typ = self.type_expr(f.next().unwrap());
                    members.push((loc, m.to_string(), typ.clone()));
                    let v = match f.next() {
                        None => {
                            ctor_params.push(
                                loc,
                                Param {
                                    var: m.clone(),
                                    info: Explicit,
                                    typ: Box::new(typ),
                                },
                            );
                            Unresolved(loc, None, m.clone())
                        }
                        Some(e) => self.expr(e),
                    };
                    ctor_body_obj.push((m.to_string(), v));
                }
                Rule::class_wrapper => {
                    let ty = self.type_expr(p.into_inner().next().unwrap());
                    let var = Var::new("v");
                    wrapper = Some((var.clone(), ty.clone()));
                    ctor_params.push(
                        ty.loc(),
                        Param {
                            var,
                            info: Explicit,
                            typ: Box::new(ty),
                        },
                    )
                }
                Rule::class_method => {
                    let mut m =
                        self.fn_def(p, Some((Unresolved(loc, None, name.clone()), tele.clone())));
                    let method_name = m.name.to_string();
                    let method_var = name.method(m.name);
                    m.name = method_var.clone();
                    m.body = match m.body {
                        Fn(f) => Method {
                            class: name.clone(),
                            associated: associated.clone(),
                            f,
                        },
                        _ => unreachable!(),
                    };
                    method_defs.push(m);
                    methods.insert(method_name, method_var);
                }
                _ => unreachable!(),
            }
        }

        let ctor_loc = ctor_params.0;
        let ctor_param_vars = ctor_params.unresolved();
        let could_be_default = ctor_params.1.is_empty();
        let default_meth_name = name.default();
        if could_be_default {
            methods.insert("default".to_string(), default_meth_name.clone());
        }
        let ctor_tupled_params = ctor_params.param(None);
        let ctor_name = name.ctor();
        let ctor_fn = Box::new(Expr::wrap_tuple_binds(
            ctor_loc,
            ctor_tupled_params.var.clone(),
            ctor_param_vars,
            match &wrapper {
                Some((v, ty)) => Unresolved(ty.loc(), None, v.clone()),
                None => Obj(loc, Box::new(Fields(ctor_loc, ctor_body_obj))),
            },
        ));
        let ctor_body = Method {
            class: name.clone(),
            associated: associated.clone(),
            f: ctor_fn,
        };
        let ctor_ret = Self::wrap_implicit_apps(&tele, Unresolved(loc, None, name.clone()));
        let mut ctor_tele = tele.clone();
        let mut eff = Box::new(Pure(ctor_loc));
        if !could_be_default {
            // Constructors that could not be default should be effect-polymorphic.
            let ctor_eff_var = Var::new("^E");
            ctor_tele.push(Param {
                var: ctor_eff_var.clone(),
                info: Implicit,
                typ: Box::new(Row(ctor_loc)),
            });
            eff = Box::new(Unresolved(ctor_loc, None, ctor_eff_var));
        }
        ctor_tele.push(ctor_tupled_params);

        let mut defs = associated_defs;
        defs.push(Def {
            loc,
            name: name.clone(),
            tele: tele.clone(),
            eff: Box::new(Pure(loc)),
            ret: Box::new(Univ(loc)),
            body: Class {
                ctor: ctor_name.clone(),
                associated,
                members: match wrapper {
                    Some((_, ty)) => ClassMembers::Wrapper(Box::new(ty)),
                    None => ClassMembers::Members(members),
                },
                methods,
            },
        });
        let ctor_def = Def {
            loc,
            name: ctor_name,
            tele: ctor_tele,
            eff,
            ret: Box::new(ctor_ret),
            body: ctor_body,
        };
        if could_be_default {
            let mut default_def = ctor_def.clone();
            default_def.name = default_meth_name;
            defs.push(default_def);
        }
        defs.push(ctor_def);
        defs.extend(method_defs);
        defs
    }

    fn namespace_def(&mut self, n: Pair<Rule>) -> Vec<Def<Expr>> {
        use Body::*;
        use Expr::*;

        let mut pairs = n.into_inner();

        let name_pair = pairs.next().unwrap();
        let loc = Loc::from(name_pair.as_span());
        let name = Var::from(name_pair);
        let class_name = name.namespace_class();

        let tele = Vec::default();

        let wrapper = "v";
        let mut ctor_params = UntupledParams::new(loc);
        ctor_params.push(
            loc,
            Param {
                var: Var::new(wrapper),
                info: Explicit,
                typ: Box::new(Unit(loc)),
            },
        );

        let mut method_defs = Vec::default();
        let mut methods = HashMap::default();

        for p in pairs {
            match p.as_rule() {
                Rule::class_method => {
                    let mut m = self.fn_def(
                        p,
                        Some((
                            Unresolved(loc, None, class_name.clone()),
                            Default::default(),
                        )),
                    );
                    let method_name = m.name.to_string();
                    let method_var = class_name.method(m.name);
                    m.name = method_var.clone();
                    m.body = match m.body {
                        Fn(f) => Method {
                            class: class_name.clone(),
                            associated: Default::default(),
                            f,
                        },
                        _ => unreachable!(),
                    };
                    method_defs.push(m);
                    methods.insert(method_name, method_var);
                }
                _ => unreachable!(),
            }
        }

        let ctor_loc = ctor_params.0;
        let ctor_param_vars = ctor_params.unresolved();
        let ctor_tupled_params = ctor_params.param(None);
        let ctor_name = class_name.ctor();
        let ctor_body = Method {
            class: class_name.clone(),
            associated: Default::default(),
            f: Box::new(Expr::wrap_tuple_binds(
                ctor_loc,
                ctor_tupled_params.var.clone(),
                ctor_param_vars,
                Unresolved(loc, None, Var::new(wrapper)),
            )),
        };
        let ctor_ret = Self::wrap_implicit_apps(&tele, Unresolved(loc, None, class_name.clone()));
        let ctor_tele = vec![ctor_tupled_params];

        let mut defs = vec![
            Def {
                loc,
                name: class_name.clone(),
                tele: tele.clone(),
                eff: Box::new(Pure(loc)),
                ret: Box::new(Univ(loc)),
                body: Class {
                    ctor: ctor_name.clone(),
                    associated: Default::default(),
                    members: ClassMembers::Wrapper(Box::new(Unit(loc))),
                    methods,
                },
            },
            Def {
                loc,
                name: ctor_name.clone(),
                tele: ctor_tele,
                eff: Box::new(Pure(loc)),
                ret: Box::new(ctor_ret),
                body: ctor_body,
            },
            Def {
                loc,
                name,
                tele: Default::default(),
                eff: Box::new(Pure(loc)),
                ret: Box::new(Unresolved(loc, None, class_name)),
                body: Constant(
                    false,
                    Box::new(Self::call1(Unresolved(loc, None, ctor_name), TT(loc))),
                ),
            },
        ];
        defs.extend(method_defs);
        defs
    }

    fn type_verify(&mut self, t: Pair<Rule>) -> Def<Expr> {
        let loc = Loc::from(t.as_span());
        let mut pairs = t.into_inner();
        let target = self.maybe_qualified(pairs.next().unwrap());
        let mut tele = Tele::default();
        for p in pairs {
            match p.as_rule() {
                Rule::row_id => tele.push(Self::row_param(p)),
                Rule::implicit_id => tele.push(Self::implicit_param(p)),
                Rule::pred => tele.push(self.pred(p)),
                _ => unreachable!(),
            }
        }
        Def {
            loc,
            name: Var::unbound(),
            tele,
            eff: Box::new(Expr::Pure(loc)),
            ret: Box::new(Expr::Univ(loc)),
            body: Body::Verify(Box::new(target)),
        }
    }

    fn fn_verify(&mut self, f: Pair<Rule>) -> Def<Expr> {
        let loc = Loc::from(f.as_span());
        let mut pairs = f.into_inner();
        let (target, eff) = self.idref_maybe_async(&mut pairs);
        let (tele, eff, ret) = self.fn_signature(pairs, loc, *eff);
        Def {
            loc,
            name: Var::unbound(),
            tele,
            eff,
            ret,
            body: Body::Verify(Box::new(target)),
        }
    }

    fn type_expr(&mut self, t: Pair<Rule>) -> Expr {
        type_pratt()
            .map_primary(|p| self.primary_type_expr(p))
            .map_infix(|lhs, op, rhs| {
                let loc = Loc::from(op.as_span());
                match op.as_rule() {
                    Rule::infix_concat => Expr::Concat(loc, Box::new(lhs), Box::new(rhs)),
                    _ => unreachable!(),
                }
            })
            .parse(t.into_inner())
    }

    fn primary_type_expr(&mut self, t: Pair<Rule>) -> Expr {
        use Expr::*;

        let p = t.into_inner().next().unwrap();
        let loc = Loc::from(p.as_span());
        match p.as_rule() {
            Rule::fn_type => {
                let ps = p.into_inner();
                let mut untupled = UntupledParams::new(loc);
                let mut untupled_ends = None;
                for fp in ps {
                    match fp.as_rule() {
                        Rule::param => untupled.push(Loc::from(fp.as_span()), self.param(fp)),
                        Rule::variadic_param => match self.variadic_param(fp) {
                            VariadicParam::Named(loc, p) => untupled.push(loc, p),
                            VariadicParam::Unnamed(t) => untupled_ends = Some(t),
                        },
                        Rule::type_expr => {
                            return Pi(
                                loc,
                                untupled.param(untupled_ends),
                                Box::new(self.type_expr(fp)),
                            );
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
            Rule::object_type_refined => {
                let mut pairs = p.into_inner();
                let fields = self.fields(pairs.next().unwrap());
                let row_id = Self::unresolved(pairs.next().unwrap());
                self.predicates.push(Param::predicate(RowOrd(
                    fields.loc(),
                    Box::new(fields),
                    Box::new(row_id.clone()),
                )));
                Object(loc, Box::new(row_id))
            }
            Rule::object_type_literal => {
                Object(loc, Box::new(self.fields(p.into_inner().next().unwrap())))
            }
            Rule::enum_type_ref => Enum(
                loc,
                Box::new(Self::unresolved(p.into_inner().next().unwrap())),
            ),
            Rule::enum_type_refined => {
                let mut pairs = p.into_inner();
                let variants = self.fields(pairs.next().unwrap());
                let row_id = Self::unresolved(pairs.next().unwrap());
                self.predicates.push(Param::predicate(RowOrd(
                    variants.loc(),
                    Box::new(variants),
                    Box::new(row_id.clone()),
                )));
                Enum(loc, Box::new(row_id))
            }
            Rule::enum_type_literal => {
                Enum(loc, Box::new(self.fields(p.into_inner().next().unwrap())))
            }
            Rule::type_app => self.type_app(p),
            Rule::tyref => self.maybe_qualified(p),
            Rule::paren_type_expr => self.type_expr(p.into_inner().next().unwrap()),
            Rule::hole => Hole(loc),
            _ => unreachable!(),
        }
    }

    fn primitive_type(&mut self, p: Pair<Rule>) -> Expr {
        use Expr::*;
        let loc = Loc::from(p.as_span());
        let t = p.into_inner().next().unwrap();
        match t.as_rule() {
            Rule::string_type => String(loc),
            Rule::number_type => Number(loc),
            Rule::bigint_type => BigInt(loc),
            Rule::boolean_type => Boolean(loc),
            Rule::unit_type => Unit(loc),
            Rule::rowkey_type => Rowkey(loc),
            _ => unreachable!(),
        }
    }

    fn type_app(&mut self, a: Pair<Rule>) -> Expr {
        use Expr::*;

        let mut pairs = a.into_inner();
        let f = pairs.next().unwrap();
        let mut f = match f.as_rule() {
            Rule::type_expr => self.type_expr(f),
            Rule::tyref => self.maybe_qualified(f),
            _ => unreachable!(),
        };

        for arg in pairs {
            let loc = Loc::from(arg.as_span());
            let (i, x) = match arg.as_rule() {
                Rule::row_arg => self.row_arg(arg),
                Rule::type_arg => self.type_arg(arg),
                Rule::type_id => {
                    f = Associate(loc, Box::new(f), arg.as_str().to_string());
                    continue;
                }
                _ => unreachable!(),
            };
            f = App(loc, Box::new(f), i, Box::new(x))
        }

        f
    }

    fn pred(&mut self, pred: Pair<Rule>) -> Param<Expr> {
        use Expr::*;

        let p = pred.into_inner().next().unwrap();
        let loc = Loc::from(p.as_span());
        Param::predicate(match p.as_rule() {
            Rule::row_ord => {
                let mut p = p.into_inner();
                let lhs = self.row_expr(p.next().unwrap());
                let rhs = self.row_expr(p.next().unwrap());
                RowOrd(loc, Box::new(lhs), Box::new(rhs))
            }
            Rule::row_eq => {
                let mut p = p.into_inner();
                let lhs = self.row_expr(p.next().unwrap());
                let rhs = self.row_expr(p.next().unwrap());
                RowEq(loc, Box::new(lhs), Box::new(rhs))
            }
            Rule::instanceof => self.instanceof(loc, p),
            _ => unreachable!(),
        })
    }

    fn instanceof(&mut self, loc: Loc, i: Pair<Rule>) -> Expr {
        let mut p = i.into_inner();
        let mut xs = vec![(UnnamedImplicit, self.type_expr(p.next().unwrap()))];
        for arg in p {
            match arg.as_rule() {
                Rule::row_arg => xs.push(self.row_arg(arg)),
                Rule::type_arg => xs.push(self.type_arg(arg)),
                Rule::tyref => {
                    let mut f = self.maybe_qualified(arg);
                    for (i, x) in xs {
                        f = Expr::App(loc, Box::new(f), i, Box::new(x))
                    }
                    return Expr::Instanceof(loc, Box::new(f));
                }
                _ => unreachable!(),
            };
        }
        unreachable!()
    }

    fn row_expr(&mut self, e: Pair<Rule>) -> Expr {
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

    fn row_primary_expr(&mut self, e: Pair<Rule>) -> Expr {
        let p = e.into_inner().next().unwrap();
        match p.as_rule() {
            Rule::row_id => Self::unresolved(p),
            Rule::row_literal => self.fields(p),
            Rule::paren_row_expr => self.row_expr(p.into_inner().next().unwrap()),
            _ => unreachable!(),
        }
    }

    fn type_arg(&mut self, a: Pair<Rule>) -> (ArgInfo, Expr) {
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

    fn row_arg(&mut self, a: Pair<Rule>) -> (ArgInfo, Expr) {
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

    fn fn_body(&mut self, b: Pair<Rule>) -> Expr {
        use Expr::*;

        let p = b.into_inner().next().unwrap();
        let loc = Loc::from(p.as_span());
        match p.as_rule() {
            Rule::fn_body_const => {
                let mut pairs = p.into_inner();
                let (id, typ, tm) = self.bind(pairs.next().unwrap());
                Const(
                    loc,
                    id,
                    typ,
                    Box::new(tm),
                    Box::new(self.fn_body(pairs.next().unwrap())),
                )
            }
            Rule::fn_body_let => {
                let mut pairs = p.into_inner();
                let (id, typ, tm) = self.bind(pairs.next().unwrap());
                Let(
                    loc,
                    id,
                    typ,
                    Box::new(tm),
                    Box::new(self.fn_body(pairs.next().unwrap())),
                )
            }
            Rule::fn_body_const_variadic => {
                let mut pairs = p.into_inner();
                let stmt = pairs.next().unwrap();
                let body = self.fn_body(pairs.next().unwrap());
                self.multi_bind(stmt, body)
            }
            Rule::fn_body_unit_const => {
                let mut pairs = p.into_inner();
                UnitBind(
                    loc,
                    Box::new(self.expr_stmt(pairs.next().unwrap())),
                    Box::new(self.fn_body(pairs.next().unwrap())),
                )
            }
            Rule::fn_body_ignored => {
                let mut pairs = p.into_inner();
                Const(
                    loc,
                    Var::unbound(),
                    None,
                    Box::new(self.expr_stmt(pairs.next().unwrap())),
                    Box::new(self.fn_body(pairs.next().unwrap())),
                )
            }
            Rule::fn_body_object_update => {
                let mut pairs = p.into_inner();
                let (a_var, expr) = self.object_update_stmt(pairs.next().unwrap());
                Const(
                    loc,
                    a_var,
                    None,
                    Box::new(expr),
                    Box::new(self.fn_body(pairs.next().unwrap())),
                )
            }
            Rule::fn_body_item_update => {
                let mut pairs = p.into_inner();
                UnitBind(
                    loc,
                    Box::new(self.item_update_stmt(pairs.next().unwrap())),
                    Box::new(self.fn_body(pairs.next().unwrap())),
                )
            }
            Rule::fn_body_update => {
                let mut pairs = p.into_inner();
                let (v, expr) = self.update_stmt(pairs.next().unwrap());
                Update(
                    loc,
                    v,
                    Box::new(expr),
                    Box::new(self.fn_body(pairs.next().unwrap())),
                )
            }
            Rule::fn_body_while => {
                let mut pairs = p.into_inner();
                While(
                    loc,
                    Box::new(self.expr(pairs.next().unwrap())),
                    Box::new(self.branch(pairs.next().unwrap(), true)),
                    Box::new(self.fn_body(pairs.next().unwrap())),
                )
            }
            Rule::fn_body_fori => {
                let mut pairs = p.into_inner();
                let clause = pairs.next().unwrap();
                let body = self.branch(pairs.next().unwrap(), true);
                let rest = self.fn_body(pairs.next().unwrap());
                self.fori(clause, body, rest)
            }
            Rule::fn_body_forof => {
                let mut pairs = p.into_inner();
                let bind = pairs.next().unwrap();
                let v = pairs.next().unwrap();
                let a = pairs.next().unwrap();
                let b = self.branch(pairs.next().unwrap(), true);
                let rest = self.fn_body(pairs.next().unwrap());
                self.forof(loc, bind, v, a, b, rest)
            }
            Rule::fn_body_if => {
                let mut pairs = p.into_inner();
                let p = Box::new(self.expr(pairs.next().unwrap()));
                let b = Box::new(self.branch(pairs.next().unwrap(), false));
                let else_or_rest = pairs.next();
                let rest = pairs.next();
                let (e, r) = if let Some(p) = rest {
                    (
                        Some(Box::new(self.branch(else_or_rest.unwrap(), false))),
                        Box::new(self.fn_body(p)),
                    )
                } else {
                    (None, Box::new(self.fn_body(else_or_rest.unwrap())))
                };
                Guard(loc, p, b, e, r)
            }
            Rule::fn_body_ret => p.into_inner().next().map_or(TT(loc), |e| self.expr(e)),
            _ => unreachable!(),
        }
    }

    fn expr(&mut self, e: Pair<Rule>) -> Expr {
        expr_pratt()
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
                    Rule::infix_mul => Self::infix_app(loc, "__mul__", lhs, rhs),
                    Rule::infix_div => Self::infix_app(loc, "__div__", lhs, rhs),
                    Rule::infix_mod => Self::infix_app(loc, "__mod__", lhs, rhs),
                    Rule::infix_concat => Expr::Cat(loc, Box::new(lhs), Box::new(rhs)),
                    Rule::infix_at => Expr::At(loc, Box::new(lhs), Box::new(rhs)),
                    _ => unreachable!(),
                }
            })
            .map_prefix(|op, x| {
                let loc = Loc::from(op.as_span());
                match op.as_rule() {
                    Rule::prefix_typeof => Expr::Typeof(loc, Box::new(x)),
                    Rule::prefix_keyof => Expr::Keyof(loc, Box::new(x)),
                    Rule::prefix_not => Self::prefix_app(loc, "__not__", x),
                    Rule::prefix_neg => Self::prefix_app(loc, "__neg__", x),
                    _ => unreachable!(),
                }
            })
            .parse(e.into_inner())
    }

    fn infix_app(loc: Loc, r: &'static str, lhs: Expr, rhs: Expr) -> Expr {
        use Expr::*;
        Self::call2(Unresolved(loc, None, Var::new(r)), lhs, rhs)
    }

    fn prefix_app(loc: Loc, r: &'static str, x: Expr) -> Expr {
        use Expr::*;
        Self::call1(Unresolved(loc, None, Var::new(r)), x)
    }

    fn primary_expr(&mut self, e: Pair<Rule>) -> Expr {
        use Expr::*;

        let p = e.into_inner().next().unwrap();
        let loc = Loc::from(p.as_span());
        match p.as_rule() {
            Rule::boolean_if => {
                let mut pairs = p.into_inner();
                If(
                    loc,
                    Box::new(self.chainable_operand(pairs.next().unwrap())),
                    Box::new(self.expr(pairs.next().unwrap())),
                    Box::new(self.expr(pairs.next().unwrap())),
                )
            }
            Rule::chainable_expr => self.chainable_expr(p),
            _ => unreachable!(),
        }
    }

    fn chainable_operand(&mut self, c: Pair<Rule>) -> Expr {
        use Expr::*;
        let p = c.into_inner().next().unwrap();
        let loc = Loc::from(p.as_span());
        match p.as_rule() {
            Rule::object_cast => Downcast(loc, Box::new(self.expr(p.into_inner().next().unwrap()))),
            Rule::enum_cast => Upcast(loc, Box::new(self.expr(p.into_inner().next().unwrap()))),
            Rule::enum_switch => {
                let mut pairs = p.into_inner();
                let e = self.expr(pairs.next().unwrap().into_inner().next().unwrap());
                let mut cases = Vec::default();
                let mut default_case = None;
                for p in pairs {
                    let rule = p.as_rule();
                    let mut c = p.into_inner();
                    match rule {
                        Rule::enum_case => {
                            let n = c.next().unwrap().as_str().to_string();
                            let param_or_expr = c.next().unwrap();
                            let (v, body) = if let Some(body) = c.next() {
                                (Var::from(param_or_expr), self.expr(body))
                            } else {
                                (Var::unbound(), self.expr(param_or_expr))
                            };
                            cases.push((n, v, body));
                        }
                        Rule::enum_default_case => {
                            default_case = Some((
                                Var::from(c.next().unwrap()),
                                Box::new(self.expr(c.next().unwrap())),
                            ));
                        }
                        _ => unreachable!(),
                    }
                }
                Switch(loc, Box::new(e), cases, default_case)
            }
            Rule::try_catch => {
                let mut pairs = p.into_inner();
                let body = self.fn_body(pairs.next().unwrap());
                let mut catches = Vec::default();
                for p in pairs {
                    catches.push(self.catch(p));
                }
                TryCatch(loc, Box::new(body), catches)
            }
            Rule::await_multi_expr => {
                Self::await_executors(loc, p.into_inner().map(|e| self.expr(e)).collect())
            }
            Rule::await_lambda_expr => Self::await_executor(
                loc,
                Self::executor(loc, self.fn_body(p.into_inner().next().unwrap())),
            ),
            Rule::await_expr => Self::await_executor(
                loc,
                Self::executor_shorthand(loc, self.expr(p.into_inner().next().unwrap())),
            ),
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
                                Rule::lambda_body_block => self.fn_body(b),
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
            Rule::paren_expr => self.expr(p.into_inner().next().unwrap()),
            Rule::string | Rule::multiline_string => Str(loc, p.as_str().to_string()),
            Rule::number => Num(loc, p.into_inner().next().unwrap().as_str().to_string()),
            Rule::bigint => Big(loc, p.as_str().to_string()),
            Rule::boolean_false => False(loc),
            Rule::boolean_true => True(loc),
            Rule::object_literal => self.object_literal(p),
            Rule::enum_variant => self.enum_variant(p),
            Rule::array_literal => Self::call1(
                Unresolved(loc, None, Var::new("Array").ctor()),
                Arr(loc, p.into_inner().map(|e| self.expr(e)).collect()),
            ),
            Rule::map_literal => {
                let mut pairs = p.into_inner();
                let k = pairs.next();
                let v = pairs.next();
                let kv = match k {
                    Some(k) => {
                        let mut kv = vec![(self.chainable_operand(k), self.expr(v.unwrap()))];
                        while let Some(k) = pairs.next() {
                            kv.push((self.chainable_operand(k), self.expr(pairs.next().unwrap())))
                        }
                        kv
                    }
                    None => Default::default(),
                };
                Self::call1(Unresolved(loc, None, Var::new("Map").ctor()), Kv(loc, kv))
            }
            Rule::hole => Hole(loc),
            Rule::tt => TT(loc),
            Rule::idref => self.maybe_qualified(p),
            _ => unreachable!(),
        }
    }

    fn chainable_expr(&mut self, e: Pair<Rule>) -> Expr {
        let mut pairs = e.into_inner();
        let f = self.chainable_operand(pairs.next().unwrap());
        pairs.fold(f, |ret, p| {
            self.chainable_operator(p.into_inner().next().unwrap(), ret)
        })
    }

    fn chainable_operator(&mut self, p: Pair<Rule>, mut f: Expr) -> Expr {
        use Expr::*;
        let loc = Loc::from(p.as_span());
        match p.as_rule() {
            Rule::index => {
                f = Self::call2(
                    Unresolved(loc, None, Var::new("__getitem__")),
                    f,
                    self.expr(p.into_inner().next().unwrap()),
                );
            }
            Rule::app => {
                let mut rev_f = None;
                let mut rev_type_args = Vec::default();
                for x in p.into_inner() {
                    match x.as_rule() {
                        Rule::idref => rev_f = Some(self.maybe_qualified(x)),
                        Rule::row_arg => {
                            let (i, e) = self.row_arg(x);
                            if rev_f.is_none() {
                                f = App(loc, Box::new(f), i, Box::new(e));
                                continue;
                            }
                            rev_type_args.push(e);
                        }
                        Rule::type_arg => {
                            let (i, e) = self.type_arg(x);
                            if rev_f.is_none() {
                                f = App(loc, Box::new(f), i, Box::new(e));
                                continue;
                            }
                            rev_type_args.push(e);
                        }
                        Rule::args => {
                            let mut args = self.tupled_args(x);
                            if let Some(rev_f) = rev_f.clone() {
                                args = Tuple(loc, Box::new(f), Box::new(args));
                                f = RevApp(
                                    loc,
                                    Box::new(rev_f),
                                    rev_type_args.clone(),
                                    Box::new(args),
                                );
                            } else {
                                f = App(loc, Box::new(f), UnnamedExplicit, Box::new(args));
                            }
                        }
                        _ => unreachable!(),
                    };
                }
            }
            Rule::access => {
                let n = p.into_inner().next().unwrap().as_str().to_string();
                f = App(loc, Box::new(Access(loc, n)), UnnamedExplicit, Box::new(f));
            }
            _ => unreachable!(),
        }
        f
    }

    fn new_expr(&mut self, e: Pair<Rule>) -> Expr {
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

    fn branch(&mut self, b: Pair<Rule>, inside_loop: bool) -> Expr {
        use Expr::*;

        let p = b.into_inner().next().unwrap();
        let loc = Loc::from(p.as_span());
        match p.as_rule() {
            Rule::branch_const | Rule::loop_branch_const => {
                let mut pairs = p.into_inner();
                let (id, typ, tm) = self.bind(pairs.next().unwrap());
                Const(
                    loc,
                    id,
                    typ,
                    Box::new(tm),
                    Box::new(self.branch(pairs.next().unwrap(), inside_loop)),
                )
            }
            Rule::branch_let | Rule::loop_branch_let => {
                let mut pairs = p.into_inner();
                let (id, typ, tm) = self.bind(pairs.next().unwrap());
                Let(
                    loc,
                    id,
                    typ,
                    Box::new(tm),
                    Box::new(self.branch(pairs.next().unwrap(), inside_loop)),
                )
            }
            Rule::branch_const_variadic | Rule::loop_branch_const_variadic => {
                let mut pairs = p.into_inner();
                let stmt = pairs.next().unwrap();
                let branch = self.branch(pairs.next().unwrap(), inside_loop);
                self.multi_bind(stmt, branch)
            }
            Rule::branch_unit_const | Rule::loop_branch_unit_const => {
                let mut pairs = p.into_inner();
                UnitBind(
                    loc,
                    Box::new(self.expr_stmt(pairs.next().unwrap())),
                    Box::new(self.branch(pairs.next().unwrap(), inside_loop)),
                )
            }
            Rule::branch_ignored | Rule::loop_branch_ignored => {
                let mut pairs = p.into_inner();
                Const(
                    loc,
                    Var::unbound(),
                    None,
                    Box::new(self.expr_stmt(pairs.next().unwrap())),
                    Box::new(self.branch(pairs.next().unwrap(), inside_loop)),
                )
            }
            Rule::branch_object_update | Rule::loop_branch_object_update => {
                let mut pairs = p.into_inner();
                let (a_var, expr) = self.object_update_stmt(pairs.next().unwrap());
                Const(
                    loc,
                    a_var,
                    None,
                    Box::new(expr),
                    Box::new(self.branch(pairs.next().unwrap(), inside_loop)),
                )
            }
            Rule::branch_item_update | Rule::loop_branch_item_update => {
                let mut pairs = p.into_inner();
                UnitBind(
                    loc,
                    Box::new(self.item_update_stmt(pairs.next().unwrap())),
                    Box::new(self.branch(pairs.next().unwrap(), inside_loop)),
                )
            }
            Rule::branch_update | Rule::loop_branch_update => {
                let mut pairs = p.into_inner();
                let (v, expr) = self.update_stmt(pairs.next().unwrap());
                Update(
                    loc,
                    v,
                    Box::new(expr),
                    Box::new(self.branch(pairs.next().unwrap(), inside_loop)),
                )
            }
            Rule::branch_while | Rule::loop_branch_while => {
                let mut pairs = p.into_inner();
                While(
                    loc,
                    Box::new(self.expr(pairs.next().unwrap())),
                    Box::new(self.branch(pairs.next().unwrap(), true)),
                    Box::new(self.branch(pairs.next().unwrap(), inside_loop)),
                )
            }
            Rule::branch_fori | Rule::loop_branch_fori => {
                let mut pairs = p.into_inner();
                let clause = pairs.next().unwrap();
                let body = self.branch(pairs.next().unwrap(), true);
                let rest = self.branch(pairs.next().unwrap(), inside_loop);
                self.fori(clause, body, rest)
            }
            Rule::branch_forof | Rule::loop_branch_forof => {
                let mut pairs = p.into_inner();
                let bind = pairs.next().unwrap();
                let v = pairs.next().unwrap();
                let a = pairs.next().unwrap();
                let b = self.branch(pairs.next().unwrap(), true);
                let rest = self.branch(pairs.next().unwrap(), inside_loop);
                self.forof(loc, bind, v, a, b, rest)
            }
            Rule::branch_if | Rule::loop_branch_if => {
                let mut pairs = p.into_inner();
                let p = Box::new(self.expr(pairs.next().unwrap()));
                let b = Box::new(self.branch(pairs.next().unwrap(), inside_loop));
                let else_or_rest = pairs.next();
                let rest = pairs.next();
                let (e, r) = if let Some(p) = rest {
                    (
                        Some(Box::new(self.branch(else_or_rest.unwrap(), inside_loop))),
                        Box::new(self.branch(p, inside_loop)),
                    )
                } else {
                    (
                        None,
                        Box::new(self.branch(else_or_rest.unwrap(), inside_loop)),
                    )
                };
                Guard(loc, p, b, e, r)
            }
            Rule::ctl_return => Return(
                loc,
                Box::new(p.into_inner().next().map_or(TT(loc), |e| self.expr(e))),
            ),
            Rule::ctl_continue if inside_loop => Continue(loc),
            Rule::ctl_break if inside_loop => Break(loc),
            Rule::ctl_expr => p.into_inner().next().map_or(TT(loc), |p| self.expr(p)),
            _ => unreachable!(),
        }
    }

    fn bind(&mut self, s: Pair<Rule>) -> (Var, Option<Box<Expr>>, Expr) {
        let mut pairs = s.into_inner();
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

    /// From:
    ///
    /// ```ts
    /// const (a, b, c, d) = expr;
    /// rest
    /// ```
    ///
    /// Into:
    ///
    /// ```ts
    /// const (a, __untupled_a) = expr;
    /// const (b, __untupled_b) = __untupled_a;
    /// const (c, d) = untupled_b;
    /// rest
    /// ```
    fn multi_bind(&mut self, s: Pair<Rule>, rest: Expr) -> Expr {
        let pairs = s.into_inner();
        let mut ids = Vec::default();
        let mut expr = None;
        for p in pairs {
            match p.as_rule() {
                Rule::bind_id => ids.push(self.maybe_qualified(p)),
                Rule::expr => expr = Some(self.expr(p)),
                _ => unreachable!(),
            }
        }
        Expr::wrap_expr_tuple_binds(expr.unwrap(), ids, rest)
    }

    fn expr_stmt(&mut self, s: Pair<Rule>) -> Expr {
        self.expr(s.into_inner().next().unwrap())
    }

    fn object_update_stmt(&mut self, s: Pair<Rule>) -> (Var, Expr) {
        use Expr::*;
        let mut pairs = s.into_inner();
        let a = pairs.next().unwrap();
        let a_loc = Loc::from(a.as_span());
        let a_var = Var::from(a);
        let n = pairs.next().unwrap();
        let n_loc = Loc::from(n.as_span());
        let fields = vec![(n.as_str().to_string(), self.expr(pairs.next().unwrap()))];
        let expr = Cat(
            a_loc,
            Box::new(Unresolved(a_loc, None, a_var.clone())),
            Box::new(Obj(n_loc, Box::new(Fields(n_loc, fields)))),
        );
        (a_var, expr)
    }

    fn item_update_stmt(&mut self, s: Pair<Rule>) -> Expr {
        let mut pairs = s.into_inner();
        let a = self.maybe_qualified(pairs.next().unwrap());
        let k = self.expr(pairs.next().unwrap());
        let v = self.expr(pairs.next().unwrap());
        let f = Expr::Unresolved(a.loc(), None, Var::new("__setitem__"));
        Self::call3(f, a, k, v)
    }

    fn update_stmt(&mut self, s: Pair<Rule>) -> (Var, Expr) {
        let mut pairs = s.into_inner();
        (
            Var::from(pairs.next().unwrap()),
            self.expr(pairs.next().unwrap()),
        )
    }

    fn fori(&mut self, clause: Pair<Rule>, body: Expr, rest: Expr) -> Expr {
        use Expr::*;

        let clause_loc = Loc::from(clause.as_span());
        let mut pairs = clause.into_inner();
        let init = pairs.next();
        let pred = pairs.next();
        let step = pairs.next();
        let body = Box::new(body);

        let body = Box::new(match step {
            None => UnitBind(clause_loc, Box::new(TT(clause_loc)), body),
            Some(p) => {
                let p = p.into_inner().next().unwrap();
                let loc = Loc::from(p.as_span());
                match p.as_rule() {
                    Rule::unit_const_stmt => UnitBind(loc, Box::new(self.expr_stmt(p)), body),
                    Rule::item_update_stmt => {
                        UnitBind(loc, Box::new(self.item_update_stmt(p)), body)
                    }
                    Rule::update_stmt => {
                        let (v, expr) = self.update_stmt(p);
                        Update(loc, v, Box::new(expr), body)
                    }
                    _ => unreachable!(),
                }
            }
        });

        let body = Box::new(match pred {
            None => Let(
                clause_loc,
                Var::unbound(),
                Some(Box::new(Boolean(clause_loc))),
                Box::new(True(clause_loc)),
                body,
            ),
            Some(p) => {
                let loc = Loc::from(p.as_span());
                Let(
                    loc,
                    Var::unbound(),
                    Some(Box::new(Boolean(loc))),
                    Box::new(self.expr(p)),
                    body,
                )
            }
        });

        let body = match init {
            None => UnitBind(clause_loc, Box::new(TT(clause_loc)), body),
            Some(p) => {
                let p = p.into_inner().next().unwrap();
                let loc = Loc::from(p.as_span());
                match p.as_rule() {
                    Rule::const_stmt => {
                        let (id, typ, tm) = self.bind(p);
                        Const(loc, id, typ, Box::new(tm), body)
                    }
                    Rule::let_stmt => {
                        let (id, typ, tm) = self.bind(p);
                        Let(loc, id, typ, Box::new(tm), body)
                    }
                    Rule::unit_const_stmt => UnitBind(loc, Box::new(self.expr_stmt(p)), body),
                    Rule::item_update_stmt => {
                        UnitBind(loc, Box::new(self.item_update_stmt(p)), body)
                    }
                    Rule::update_stmt => {
                        let (v, expr) = self.update_stmt(p);
                        Update(loc, v, Box::new(expr), body)
                    }
                    _ => unreachable!(),
                }
            }
        };

        Fori(clause_loc, Box::new(body), Box::new(rest))
    }

    /// From:
    ///
    /// ```ts
    /// for (const /* or let */ v of a) {
    ///     /* b */
    /// }
    /// /* rest */
    /// ```
    ///
    /// Into:
    ///
    /// ```ts
    /// const __it = (expr).iter();
    /// for (let __r = __it.next(); __r.isOk(); __r = __it.next()) {
    ///     const /* or let */ v = __r.unwrap();
    ///     /* b */
    /// }
    /// /* rest */
    /// ```
    fn forof(
        &mut self,
        loc: Loc,
        l: Pair<Rule>,
        v: Pair<Rule>,
        a: Pair<Rule>,
        b: Expr,
        rest: Expr,
    ) -> Expr {
        use Expr::*;

        let v_loc = Loc::from(v.as_span());
        let a_loc = Loc::from(a.as_span());

        let it = Var::iterator();
        let it_ret = Var::iteration_result();

        let it_init = Box::new(Self::rev_call1(
            Unresolved(a_loc, None, Var::new("iter")),
            self.expr(a),
        ));
        let init = Box::new(Self::rev_call1(
            Unresolved(a_loc, None, Var::new("next")),
            Unresolved(a_loc, None, it.clone()),
        ));
        let pred = Box::new(Self::rev_call1(
            Unresolved(a_loc, None, Var::new("isOk")),
            Unresolved(a_loc, None, it_ret.clone()),
        ));
        let step = Box::new(Self::rev_call1(
            Unresolved(a_loc, None, Var::new("next")),
            Unresolved(a_loc, None, it.clone()),
        ));

        let bind = Box::new({
            let v = Var::from(v);
            let value = Box::new(Self::rev_call1(
                Unresolved(a_loc, None, Var::new("unwrap")),
                Unresolved(a_loc, None, it_ret.clone()),
            ));
            let b = Box::new(b);
            match l.as_rule() {
                Rule::forof_const => Const(v_loc, v, None, value, b),
                Rule::forof_let => Let(v_loc, v, None, value, b),
                _ => unreachable!(),
            }
        });
        let step = Box::new(Update(a_loc, it_ret.clone(), step, bind));
        let pred = Box::new(Let(
            a_loc,
            Var::unbound(),
            Some(Box::new(Boolean(a_loc))),
            pred,
            step,
        ));
        let init = Box::new(Let(a_loc, it_ret, None, init, pred));

        Const(
            a_loc,
            it,
            None,
            it_init,
            Box::new(Fori(loc, init, Box::new(rest))),
        )
    }

    fn maybe_qualified(&mut self, p: Pair<Rule>) -> Expr {
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

    fn qualifier(&mut self, q: Pair<Rule>) -> ModuleID {
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

    fn variadic_param(&mut self, p: Pair<Rule>) -> VariadicParam {
        use Expr::*;
        let loc = Loc::from(p.as_span());
        let mut pairs = p.into_inner();
        let id = pairs.next().unwrap();
        match pairs.next() {
            Some(p) => VariadicParam::Named(
                loc,
                Param {
                    var: Var::from(id),
                    info: Explicit,
                    typ: Box::new(Varargs(loc, Box::new(self.type_expr(p)))),
                },
            ),
            None => VariadicParam::Unnamed(AnonVarargs(loc, Box::new(self.type_expr(id)))),
        }
    }

    fn param(&mut self, p: Pair<Rule>) -> Param<Expr> {
        let mut pairs = p.into_inner();
        Param {
            var: Var::from(pairs.next().unwrap()),
            info: Explicit,
            typ: Box::new(self.type_expr(pairs.next().unwrap())),
        }
    }

    fn fields(&mut self, p: Pair<Rule>) -> Expr {
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

    fn label(&mut self, l: Pair<Rule>) -> (String, Expr) {
        let mut p = l.into_inner();
        (
            p.next().unwrap().as_str().to_string(),
            self.expr(p.next().unwrap()),
        )
    }

    fn object_literal(&mut self, l: Pair<Rule>) -> Expr {
        use Expr::*;
        let loc = Loc::from(l.as_span());
        Obj(
            loc,
            Box::new(Fields(loc, l.into_inner().map(|e| self.label(e)).collect())),
        )
    }

    fn enum_variant(&mut self, v: Pair<Rule>) -> Expr {
        use Expr::*;
        let loc = Loc::from(v.as_span());
        let mut pairs = v.into_inner();
        let n = pairs.next().unwrap().as_str().to_string();
        let a = pairs
            .next()
            .map_or(TT(loc), |p| self.expr(p.into_inner().next().unwrap()));
        Variant(loc, n, Box::new(a))
    }

    fn tupled_args(&mut self, a: Pair<Rule>) -> Expr {
        use Expr::*;
        let mut ends = TT(Loc::from(a.as_span()));
        let mut args = Vec::default();
        for pair in a.into_inner() {
            let loc = Loc::from(pair.as_span());
            match pair.as_rule() {
                Rule::expr => args.push((loc, self.expr(pair))),
                Rule::spread_arg => match pair.into_inner().next() {
                    Some(p) => args.push((loc, Spread(loc, Box::new(self.expr(p))))),
                    None => ends = AnonSpread(loc),
                },
                _ => unreachable!(),
            }
        }
        for (loc, x) in args.into_iter().rev() {
            ends = Tuple(loc, Box::new(x), Box::new(ends))
        }
        ends
    }

    fn catch(&mut self, c: Pair<Rule>) -> Catch {
        let mut pairs = c.into_inner();
        let i = self.maybe_qualified(pairs.next().unwrap());
        let inst_ty = self.type_expr(pairs.next().unwrap());
        let mut inst_fns = Vec::default();
        for p in pairs {
            let mut def = self.fn_def(p, None);
            let name = def.name.to_string();
            def.name = def.name.catch_fn();
            def.body = match def.body {
                Body::Fn(f) => Body::InstanceFn(f),
                _ => unreachable!(),
            };
            inst_fns.push((name, def));
        }
        Catch {
            i,
            inst_ty,
            inst_fns,
        }
    }

    fn call1(f: Expr, x: Expr) -> Expr {
        use Expr::*;
        let tt = Box::new(TT(x.loc()));
        App(
            f.loc(),
            Box::new(f),
            UnnamedExplicit,
            Box::new(Tuple(x.loc(), Box::new(x), tt)),
        )
    }

    fn call2(f: Expr, x: Expr, y: Expr) -> Expr {
        use Expr::*;
        let tt = Box::new(TT(y.loc()));
        App(
            f.loc(),
            Box::new(f),
            UnnamedExplicit,
            Box::new(Tuple(
                x.loc(),
                Box::new(x),
                Box::new(Tuple(y.loc(), Box::new(y), tt)),
            )),
        )
    }

    fn call3(f: Expr, x: Expr, y: Expr, z: Expr) -> Expr {
        use Expr::*;
        let tt = Box::new(TT(z.loc()));
        App(
            f.loc(),
            Box::new(f),
            UnnamedExplicit,
            Box::new(Tuple(
                x.loc(),
                Box::new(x),
                Box::new(Tuple(
                    y.loc(),
                    Box::new(y),
                    Box::new(Tuple(z.loc(), Box::new(z), tt)),
                )),
            )),
        )
    }

    fn rev_call1(f: Expr, a0: Expr) -> Expr {
        use Expr::*;
        let tt = Box::new(TT(a0.loc()));
        RevApp(
            f.loc(),
            Box::new(f),
            Default::default(),
            Box::new(Tuple(a0.loc(), Box::new(a0), tt)),
        )
    }

    fn await_executor(loc: Loc, e: Expr) -> Expr {
        use Expr::*;
        EmitAsync(
            loc,
            Box::new(Self::call1(Unresolved(loc, None, Var::await_one()), e)),
        )
    }

    fn await_executors(loc: Loc, e: Vec<Expr>) -> Expr {
        use Expr::*;
        EmitAsync(
            loc,
            Box::new(App(
                loc,
                Box::new(Unresolved(loc, None, Var::await_mul())),
                UnnamedExplicit,
                Box::new(
                    e.into_iter()
                        .rev()
                        .rfold(TT(loc), |ret, e| Tuple(loc, Box::new(e), Box::new(ret))),
                ),
            )),
        )
    }

    /// From:
    ///
    /// ```ts
    /// expr
    /// ```
    ///
    /// Into:
    ///
    /// ```ts
    /// (resolve) => { resolve(expr) }
    /// ```
    fn executor_shorthand(loc: Loc, e: Expr) -> Expr {
        Self::executor(
            loc,
            Self::call1(Expr::Unresolved(loc, None, Var::new("resolve")), e),
        )
    }

    /// From:
    ///
    /// ```ts
    /// { expr }
    /// ```
    ///
    /// Into:
    ///
    /// ```ts
    /// (resolve) => { expr }
    /// ```
    fn executor(loc: Loc, e: Expr) -> Expr {
        Expr::TupledLam(
            loc,
            vec![Expr::Unresolved(loc, None, Var::new("resolve"))],
            Box::new(e),
        )
    }
}

struct UntupledParams(Loc, Vec<(Loc, Param<Expr>)>);

impl UntupledParams {
    fn new(loc: Loc) -> Self {
        Self(loc, Default::default())
    }

    fn push(&mut self, loc: Loc, p: Param<Expr>) {
        self.1.push((loc, p))
    }

    fn unresolved(&mut self) -> Vec<Expr> {
        use Expr::*;
        self.1
            .iter()
            .map(|(loc, p)| Unresolved(*loc, None, p.var.clone()))
            .collect()
    }

    fn param(self, ends: Option<Expr>) -> Param<Expr> {
        use Expr::*;
        let UntupledParams(loc, ps) = self;
        let mut ret = ends.unwrap_or(Unit(loc));
        for (loc, p) in ps.into_iter().rev() {
            ret = Sigma(loc, p, Box::new(ret));
        }
        Param {
            var: Var::tupled(),
            info: Explicit,
            typ: Box::new(ret),
        }
    }
}

enum VariadicParam {
    Named(Loc, Param<Expr>),
    Unnamed(Expr),
}
