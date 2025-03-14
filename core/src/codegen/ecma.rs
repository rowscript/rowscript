use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::str::FromStr;

use log::debug;
use num_bigint::BigInt as BigIntValue;
use swc_atoms::atom;
use swc_common::{BytePos, DUMMY_SP, SourceMap, Span};
use swc_ecma_ast::{
    ArrayLit, ArrayPat, ArrowExpr, AssignExpr, AssignOp, AssignTarget, AwaitExpr,
    BigInt as JsBigInt, BinExpr, BinaryOp, BindingIdent, BlockStmt, BlockStmtOrExpr, Bool,
    BreakStmt, CallExpr, Callee, ComputedPropName, CondExpr, ContinueStmt, Decl, ExportDecl, Expr,
    ExprOrSpread, ExprStmt, FnDecl, ForStmt, Function, Ident, IdentName, IfStmt, ImportDecl,
    ImportNamedSpecifier, ImportSpecifier, ImportStarAsSpecifier, KeyValueProp, Lit, MemberExpr,
    MemberProp, MethodProp, Module, ModuleDecl, ModuleItem, NewExpr, Number as JsNumber, Number,
    ObjectLit, Param as JsParam, ParenExpr, Pat, Prop, PropName, PropOrSpread, RestPat, ReturnStmt,
    SimpleAssignTarget, SpreadElement, Stmt, Str, ThrowStmt, UnaryExpr, UnaryOp, VarDecl,
    VarDeclKind, VarDeclOrExpr, VarDeclarator, WhileStmt,
};
use swc_ecma_codegen::Emitter;
use swc_ecma_codegen::text_writer::JsWriter;

use crate::Error::{NonErasable, UnsolvedMeta};
use crate::codegen::Target;
use crate::theory::ParamInfo::Explicit;
use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Body, Def, Sigma};
use crate::theory::conc::data::ArgInfo;
use crate::theory::conc::data::ArgInfo::{UnnamedExplicit, UnnamedImplicit};
use crate::theory::conc::load::{Import, ImportedDefs, ImportedPkg, ModuleID};
use crate::theory::{
    AWAIT, AWAIT_ALL, AWAIT_ANY, AWAIT_MUL, Loc, Param, THIS, TUPLED, Tele, UNTUPLED_ENDS,
    UNTUPLED_RHS_PREFIX, Var,
};
use crate::{Error, File, Src};

impl From<Loc> for Span {
    fn from(loc: Loc) -> Self {
        Self {
            lo: BytePos(loc.start as u32),
            hi: BytePos(loc.end as u32),
        }
    }
}

const JS_LIB: &str = "__lib";
const JS_LIB_PREFIX: &str = "__lib$";
const JS_ESCAPED_THIS: &str = "__this";

#[derive(Default, Clone)]
pub struct Ecma {
    not_escaping_this: bool,
}

impl Ecma {
    fn solution<'a>(sigma: &'a Sigma, m: &'a Var) -> &'a Option<Box<Term>> {
        use Body::*;
        match &sigma.get(m).unwrap().body {
            Meta(_, s) => s,
            _ => unreachable!(),
        }
    }

    fn special_ident(s: &str) -> Ident {
        Ident {
            span: DUMMY_SP,
            ctxt: Default::default(),
            sym: s.into(),
            optional: false,
        }
    }

    fn str_ident(loc: Loc, s: &str) -> Ident {
        Ident {
            span: loc.into(),
            ctxt: Default::default(),
            sym: match s {
                THIS => JS_ESCAPED_THIS,
                s => s,
            }
            .into(),
            optional: false,
        }
    }

    fn ident(loc: Loc, v: &Var) -> Ident {
        Self::str_ident(loc, if v.is_unbound() { "_" } else { v.as_str() })
    }

    fn asis_ident(loc: Loc, v: &Var) -> Ident {
        Ident {
            span: loc.into(),
            ctxt: Default::default(),
            sym: v.as_str().into(),
            optional: false,
        }
    }

    fn ident_pat(loc: Loc, v: &Var) -> Pat {
        Pat::Ident(BindingIdent {
            id: Self::ident(loc, v),
            type_ann: None,
        })
    }

    fn str_ident_pat(loc: Loc, s: &str) -> Pat {
        Pat::Ident(BindingIdent {
            id: Self::str_ident(loc, s),
            type_ann: None,
        })
    }

    fn undefined() -> Expr {
        Expr::Ident(Self::special_ident("undefined"))
    }

    fn null() -> Expr {
        Expr::Ident(Self::special_ident("null"))
    }

    fn lib() -> Ident {
        Self::special_ident(JS_LIB)
    }

    fn js_raw_str(loc: Loc, s: &str) -> Str {
        Str {
            span: loc.into(),
            value: atom!(""),
            raw: Some(s.into()),
        }
    }

    fn js_str(loc: Loc, s: &str) -> Str {
        Str {
            span: loc.into(),
            value: s.into(),
            raw: None,
        }
    }

    fn js_path(pb: PathBuf) -> Str {
        Self::js_str(
            Default::default(),
            pb.iter()
                .map(|item| item.to_string_lossy())
                .collect::<Vec<_>>()
                .join("/")
                .as_str(),
        )
    }

    fn paren(loc: Loc, e: Expr) -> Expr {
        Expr::Paren(ParenExpr {
            span: loc.into(),
            expr: Box::new(e),
        })
    }

    fn call(loc: Loc, f: Expr, args: Vec<ExprOrSpread>) -> Expr {
        Expr::Call(CallExpr {
            span: loc.into(),
            ctxt: Default::default(),
            callee: Callee::Expr(Box::new(f)),
            args,
            type_args: None,
        })
    }

    fn paren_call(loc: Loc, f: Expr, args: Vec<ExprOrSpread>) -> Expr {
        Self::call(loc, Self::paren(loc, f), args)
    }

    fn paren_call1(loc: Loc, f: Expr, e: Expr) -> Expr {
        Self::call(loc, Self::paren(loc, f), vec![Self::non_spread(e)])
    }

    fn variant(loc: Loc, tag: &str, v: Expr) -> Expr {
        Expr::Object(ObjectLit {
            span: loc.into(),
            props: vec![PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                key: PropName::Str(Self::js_str(loc, tag)),
                value: Box::new(v),
            })))],
        })
    }

    fn ok(loc: Loc, v: Expr) -> Expr {
        Self::variant(loc, "Ok", v)
    }

    fn none(loc: Loc) -> Expr {
        Self::variant(loc, "None", Self::undefined())
    }

    fn index(loc: Loc, e: Expr, value: f64) -> Expr {
        Expr::Member(MemberExpr {
            span: loc.into(),
            obj: Box::new(e.clone()),
            prop: MemberProp::Computed(ComputedPropName {
                span: loc.into(),
                expr: Box::new(Expr::Lit(Lit::Num(Number {
                    span: loc.into(),
                    value,
                    raw: None,
                }))),
            }),
        })
    }

    fn entry(loc: Loc, k: Expr, v: Expr) -> Expr {
        Expr::Object(ObjectLit {
            span: loc.into(),
            props: vec![
                PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                    key: PropName::Ident(IdentName::from(Self::str_ident(loc, "key"))),
                    value: Box::new(k),
                }))),
                PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                    key: PropName::Ident(IdentName::from(Self::str_ident(loc, "value"))),
                    value: Box::new(v),
                }))),
            ],
        })
    }

    fn tuple(loc: Loc, fst: Expr, snd: Expr) -> Expr {
        Expr::Array(ArrayLit {
            span: loc.into(),
            elems: vec![Some(Self::non_spread(fst)), Some(Self::non_spread(snd))],
        })
    }

    fn short_arrow(loc: Loc, params: Vec<Pat>, e: Expr) -> Expr {
        Expr::Arrow(ArrowExpr {
            span: loc.into(),
            ctxt: Default::default(),
            params,
            body: Box::new(BlockStmtOrExpr::Expr(Box::new(e))),
            is_async: false,
            is_generator: false,
            type_params: None,
            return_type: None,
        })
    }

    fn block_arrow(loc: Loc, params: Vec<Pat>, block: BlockStmt, is_async: bool) -> Expr {
        Expr::Arrow(ArrowExpr {
            span: loc.into(),
            ctxt: Default::default(),
            params,
            body: Box::new(BlockStmtOrExpr::BlockStmt(block)),
            is_async,
            is_generator: false,
            type_params: None,
            return_type: None,
        })
    }

    /// ```ts
    /// ((x) => x.done ? None : Ok({key: x.value[0], value: x.value[1]}))(e)
    /// ```
    fn entryify_iteration_result(loc: Loc, e: Expr) -> Expr {
        let item = Self::access(loc, Expr::Ident(Self::str_ident(loc, "x")), "value");
        let k = Self::index(loc, item.clone(), 0.0);
        let v = Self::index(loc, item, 1.0);
        Self::paren_call1(
            loc,
            Self::short_arrow(
                loc,
                vec![Self::str_ident_pat(loc, "x")],
                Expr::Cond(CondExpr {
                    span: loc.into(),
                    test: Box::new(Self::access(
                        loc,
                        Expr::Ident(Self::str_ident(loc, "x")),
                        "done",
                    )),
                    cons: Box::new(Self::none(loc)),
                    alt: Box::new(Self::ok(loc, Self::entry(loc, k, v))),
                }),
            ),
            e,
        )
    }

    fn access(loc: Loc, a: Expr, n: &str) -> Expr {
        Expr::Member(MemberExpr {
            span: loc.into(),
            obj: Box::new(Self::paren(loc, a)),
            prop: MemberProp::Ident(IdentName::from(Self::str_ident(loc, n))),
        })
    }

    fn prototype<const N: usize>(loc: Loc, a: Expr, m: &str, args: [Expr; N]) -> Expr {
        Self::call(
            loc,
            Self::access(loc, a, m),
            args.into_iter().map(Self::non_spread).collect(),
        )
    }

    fn well_known_symbol(
        &mut self,
        sigma: &Sigma,
        loc: Loc,
        v: &Term,
        sym: &str,
    ) -> Result<Expr, Error> {
        Ok(Expr::Member(MemberExpr {
            span: loc.into(),
            obj: Box::new(Self::paren(loc, self.expr(sigma, loc, v)?)),
            prop: MemberProp::Computed(ComputedPropName {
                span: loc.into(),
                expr: Box::new(Expr::Member(MemberExpr {
                    span: loc.into(),
                    obj: Box::new(Expr::Ident(Self::special_ident("Symbol"))),
                    prop: MemberProp::Ident(IdentName::from(Self::special_ident(sym))),
                })),
            }),
        }))
    }

    fn well_known_symbol_call(
        &mut self,
        sigma: &Sigma,
        loc: Loc,
        v: &Term,
        sym: &str,
    ) -> Result<Expr, Error> {
        Ok(Self::call(
            loc,
            self.well_known_symbol(sigma, loc, v, sym)?,
            Default::default(),
        ))
    }

    /// ```ts
    /// ((x) => x.done ? None : Ok(x.value))(e)
    /// ```
    fn optionify_iteration_result(loc: Loc, e: Expr) -> Expr {
        Self::paren_call1(
            loc,
            Self::short_arrow(
                loc,
                vec![Self::str_ident_pat(loc, "x")],
                Expr::Cond(CondExpr {
                    span: loc.into(),
                    test: Box::new(Self::access(
                        loc,
                        Expr::Ident(Self::str_ident(loc, "x")),
                        "done",
                    )),
                    cons: Box::new(Self::none(loc)),
                    alt: Box::new(Self::ok(
                        loc,
                        Self::access(loc, Expr::Ident(Self::str_ident(loc, "x")), "value"),
                    )),
                }),
            ),
            e,
        )
    }

    /// ```ts
    /// ((x) => x == null ? None : Ok(x))(e)
    /// ```
    fn optionify(loc: Loc, e: Expr) -> Expr {
        Self::paren_call1(
            loc,
            Self::short_arrow(
                loc,
                vec![Self::str_ident_pat(loc, "x")],
                Expr::Cond(CondExpr {
                    span: loc.into(),
                    test: Box::new(Expr::Bin(BinExpr {
                        span: loc.into(),
                        op: BinaryOp::EqEq,
                        left: Box::new(Expr::Ident(Self::str_ident(loc, "x"))),
                        right: Box::new(Self::null()),
                    })),
                    cons: Box::new(Self::none(loc)),
                    alt: Box::new(Self::ok(loc, Expr::Ident(Self::str_ident(loc, "x")))),
                }),
            ),
            e,
        )
    }

    fn new_promise(loc: Loc, args: Vec<ExprOrSpread>) -> Expr {
        Expr::New(NewExpr {
            span: loc.into(),
            ctxt: Default::default(),
            callee: Box::new(Expr::Ident(Self::special_ident("Promise"))),
            args: Some(args),
            type_args: None,
        })
    }

    fn await_executor(loc: Loc, args: Vec<ExprOrSpread>) -> Expr {
        Expr::Await(AwaitExpr {
            span: loc.into(),
            arg: Box::new(Self::new_promise(loc, args)),
        })
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
    /// expr.map(e => new Promise(e))
    /// ```
    fn executors_to_promises(loc: Loc, args: Vec<ExprOrSpread>) -> Expr {
        let executors = args.into_iter().next().unwrap();
        Self::prototype(
            loc,
            *executors.expr,
            "map",
            [Self::short_arrow(
                loc,
                vec![Self::str_ident_pat(loc, "e")],
                Self::new_promise(
                    loc,
                    vec![Self::non_spread(Expr::Ident(Self::str_ident(loc, "e")))],
                ),
            )],
        )
    }

    /// From:
    ///
    /// ```ts
    /// (a, b, c)
    /// ```
    ///
    /// Into:
    ///
    /// ```ts
    /// (
    ///   [
    ///     (resolve) => resolve(a),
    ///     (resolve) => resolve(b),
    ///     (resolve) => resolve(c),
    ///   ]
    /// )
    /// ```
    fn args_to_promises(loc: Loc, args: Vec<ExprOrSpread>) -> Vec<ExprOrSpread> {
        vec![Self::non_spread(Expr::Array(ArrayLit {
            span: loc.into(),
            elems: args
                .into_iter()
                .map(|e| {
                    Some(Self::non_spread(Self::short_arrow(
                        loc,
                        vec![Self::str_ident_pat(loc, "resolve")],
                        Self::paren_call1(
                            loc,
                            Expr::Ident(Self::str_ident(loc, "resolve")),
                            *e.expr,
                        ),
                    )))
                })
                .collect(),
        }))]
    }

    fn await_executors(loc: Loc, awaiter: &str, executors: Vec<ExprOrSpread>) -> Expr {
        Expr::Await(AwaitExpr {
            span: loc.into(),
            arg: Box::new(Self::paren_call1(
                loc,
                Expr::Ident(Self::special_ident(awaiter)),
                Self::executors_to_promises(loc, executors),
            )),
        })
    }

    fn app(
        &mut self,
        sigma: &Sigma,
        loc: Loc,
        mut f: &Term,
        i: &ArgInfo,
        x: &Term,
    ) -> Result<Expr, Error> {
        use Term::*;

        // Try erasing the trailing predicate proofs.
        match (i, x) {
            (UnnamedImplicit, arg) => {
                let mut ans = arg.clone();
                if let MetaRef(_, v, _) = arg {
                    let v = match &sigma.get(v).unwrap().body {
                        Body::Meta(_, v) => v,
                        _ => unreachable!(),
                    };
                    ans = match v {
                        Some(v) => *v.clone(),
                        _ => unreachable!(),
                    };
                }
                match ans {
                    RowSat | RowRefl | InstanceofSat => return self.expr(sigma, loc, f),
                    _ => unreachable!(),
                }
            }
            (UnnamedExplicit, _) => {}
            _ => unreachable!(),
        }

        // Try erasing the implicit type arguments.
        loop {
            if let App(func, ai, _) = f {
                if !matches!(ai, UnnamedExplicit) {
                    f = func;
                    continue;
                }
            }
            break;
        }

        let args = self.untuple_args(sigma, loc, x)?;

        // Try transforming await expressions.
        if let Find { interface_fn, .. } = f {
            return Ok(match interface_fn.as_str() {
                AWAIT => Self::await_executor(loc, args),
                AWAIT_MUL => {
                    Self::await_executors(loc, "Promise.all", Self::args_to_promises(loc, args))
                }
                AWAIT_ALL => Self::await_executors(loc, "Promise.all", args),
                AWAIT_ANY => Self::await_executors(loc, "Promise.any", args),
                _ => return Err(NonErasable(Ref(interface_fn.clone()), loc)),
            });
        }

        Ok(Self::paren_call(loc, self.expr(sigma, loc, f)?, args))
    }

    fn bin_expr(
        &mut self,
        sigma: &Sigma,
        loc: Loc,
        op: BinaryOp,
        a: &Term,
        b: &Term,
    ) -> Result<Expr, Error> {
        Ok(Expr::Bin(BinExpr {
            span: loc.into(),
            op,
            left: Box::new(self.expr(sigma, loc, a)?),
            right: Box::new(self.expr(sigma, loc, b)?),
        }))
    }

    fn unary_expr(
        &mut self,
        sigma: &Sigma,
        loc: Loc,
        op: UnaryOp,
        a: &Term,
    ) -> Result<Expr, Error> {
        Ok(Expr::Unary(UnaryExpr {
            span: loc.into(),
            op,
            arg: Box::new(self.expr(sigma, loc, a)?),
        }))
    }

    fn is_async(def: &Def<Term>) -> bool {
        match def.eff.as_ref() {
            Term::Effect(m) => {
                for x in m {
                    if x.as_str() == "Async" {
                        return true;
                    }
                }
                false
            }
            _ => false,
        }
    }

    fn func(&mut self, sigma: &Sigma, def: &Def<Term>, body: &Term) -> Result<Function, Error> {
        Ok(Function {
            params: Self::type_erased_params(def.loc, &def.tele, body),
            decorators: Default::default(),
            span: def.loc.into(),
            ctxt: Default::default(),
            body: Some(self.block(sigma, def.loc, body, true)?),
            is_generator: false,
            is_async: Self::is_async(def),
            type_params: None,
            return_type: None,
        })
    }

    fn type_erased_pats(loc: Loc, tele: Option<&Tele<Term>>, tm: &Term) -> Vec<Pat> {
        let mut ret = Vec::default();

        // Try retrieving the function parameters from the function body, which sounds wack.
        let mut body = tm;
        let mut is_first = true;
        loop {
            if let Term::TupleBind(p, q, a, b) = body {
                // Only retrieve those from destructuring the tupled parameter.
                if is_first {
                    match a.as_ref() {
                        Term::Ref(v) if v.as_str() == TUPLED => {}
                        _ => break,
                    }
                }
                is_first = false;

                let rhs = q.var.as_str();
                if rhs.starts_with(UNTUPLED_RHS_PREFIX) {
                    ret.push(Self::ident_pat(loc, &p.var));
                    body = b.as_ref();
                    // Stop at here otherwise we would retrieve some wrong ones (e.g. other tupled lets).
                    if rhs != UNTUPLED_ENDS {
                        continue;
                    }
                }
            }
            break;
        }

        // Try adding the variadic parameter from the explicit parameters.
        if let Some(tele) = tele {
            let mut param_typ = tele
                .iter()
                .find(|p| p.info == Explicit)
                .unwrap()
                .typ
                .as_ref();
            let mut is_first = true;
            loop {
                match param_typ {
                    Term::Sigma(.., b) => {
                        param_typ = b.as_ref();
                        is_first = false;
                    }
                    Term::Unit => break,
                    _ => {
                        let arg = Box::new(Self::str_ident_pat(
                            loc,
                            if is_first { TUPLED } else { UNTUPLED_ENDS },
                        ));
                        ret.push(Pat::Rest(RestPat {
                            span: loc.into(),
                            dot3_token: loc.into(),
                            arg,
                            type_ann: None,
                        }));
                        break;
                    }
                }
            }
        }

        ret
    }

    fn type_erased_params(loc: Loc, tele: &Tele<Term>, tm: &Term) -> Vec<JsParam> {
        Self::type_erased_pats(loc, Some(tele), tm)
            .into_iter()
            .map(|pat| JsParam {
                span: loc.into(),
                decorators: Default::default(),
                pat,
            })
            .collect()
    }

    fn untuple_args(
        &mut self,
        sigma: &Sigma,
        loc: Loc,
        mut tm: &Term,
    ) -> Result<Vec<ExprOrSpread>, Error> {
        use Term::*;

        let mut ret = Vec::default();
        loop {
            match tm {
                Tuple(a, b) => {
                    ret.push(Self::non_spread(self.expr(sigma, loc, a)?));
                    tm = b
                }
                TT => break,
                Ref(v) if v.as_str() == TUPLED || v.as_str() == UNTUPLED_ENDS => {
                    ret.push(Self::spread(loc, self.expr(sigma, loc, tm)?));
                    break;
                }
                _ => unreachable!(),
            }
        }
        Ok(ret)
    }

    fn lambda_encoded_let(
        &mut self,
        sigma: &Sigma,
        loc: Loc,
        v: Option<&Var>,
        a: &Term,
        b: &Term,
    ) -> Result<Expr, Error> {
        Ok(Self::paren_call1(
            loc,
            Self::block_arrow(
                loc,
                v.map_or_else(Default::default, |v| vec![Self::ident_pat(loc, v)]),
                self.block(sigma, loc, b, true)?,
                false,
            ),
            self.expr(sigma, loc, a)?,
        ))
    }

    fn tuple_binds_to_pats<'a>(
        loc: Loc,
        p: &Param<Term>,
        q: &Param<Term>,
        mut body: &'a Term,
    ) -> (Vec<Option<Pat>>, &'a Term) {
        let mut elems = vec![Some(Self::ident_pat(loc, &p.var))];
        loop {
            if let Term::TupleBind(p_next, _, _, b) = body {
                elems.push(Some(Self::ident_pat(loc, &p_next.var)));
                body = b;
                continue;
            }
            break;
        }
        if q.var.as_str() == UNTUPLED_ENDS {
            elems.push(Some(Self::ident_pat(loc, &q.var)));
        }
        (elems, body)
    }

    fn enum_case_consequent(
        &mut self,
        sigma: &Sigma,
        loc: Loc,
        tag: Option<&str>,
        v: &Var,
        tm: &Term,
    ) -> Result<Stmt, Error> {
        let mut x = Expr::Ident(Self::str_ident(loc, "x"));
        if let Some(tag) = tag {
            x = Expr::Member(MemberExpr {
                span: loc.into(),
                obj: Box::new(x),
                prop: MemberProp::Computed(ComputedPropName {
                    span: loc.into(),
                    expr: Box::new(Expr::Lit(Lit::Str(Self::js_str(loc, tag)))),
                }),
            });
        }
        Ok(Stmt::Return(ReturnStmt {
            span: loc.into(),
            arg: Some(Box::new(Self::paren_call1(
                loc,
                Self::block_arrow(
                    loc,
                    vec![Self::ident_pat(loc, v)],
                    self.block(sigma, loc, tm, true)?,
                    false,
                ),
                x,
            ))),
        }))
    }

    fn bind_decl(&mut self, sigma: &Sigma, loc: Loc, v: &Var, tm: &Term) -> Result<VarDecl, Error> {
        Ok(VarDecl {
            span: loc.into(),
            ctxt: Default::default(),
            kind: VarDeclKind::Var,
            declare: false,
            decls: vec![VarDeclarator {
                span: loc.into(),
                name: Self::ident_pat(loc, v),
                init: Some(Box::new(self.expr(sigma, loc, tm)?)),
                definite: false,
            }],
        })
    }

    fn update(&mut self, sigma: &Sigma, loc: Loc, v: &Var, tm: &Term) -> Result<Expr, Error> {
        Ok(Expr::Assign(AssignExpr {
            span: loc.into(),
            op: AssignOp::Assign,
            left: AssignTarget::Simple(SimpleAssignTarget::Ident(BindingIdent {
                id: Self::ident(loc, v),
                type_ann: None,
            })),
            right: Box::new(self.expr(sigma, loc, tm)?),
        }))
    }

    fn iife(loc: Loc, b: BlockStmt, is_async: bool) -> Expr {
        Self::paren_call(
            loc,
            Self::paren(loc, Self::block_arrow(loc, Default::default(), b, is_async)),
            Default::default(),
        )
    }

    fn while_stmt(&mut self, sigma: &Sigma, loc: Loc, p: &Term, b: &Term) -> Result<Stmt, Error> {
        Ok(Stmt::While(WhileStmt {
            span: loc.into(),
            test: Box::new(self.expr(sigma, loc, p)?),
            body: Box::new(Stmt::Block(self.block(sigma, loc, b, false)?)),
        }))
    }

    fn fori_stmt(&mut self, sigma: &Sigma, loc: Loc, body: &Term) -> Result<Stmt, Error> {
        use Term::*;

        let (init, body) = match body {
            Const(p, a, b) | Let(p, a, b) => (
                Some(VarDeclOrExpr::VarDecl(Box::new(
                    self.bind_decl(sigma, loc, &p.var, a)?,
                ))),
                b,
            ),
            Update(v, a, b) => (
                Some(VarDeclOrExpr::Expr(Box::new(
                    self.update(sigma, loc, v, a)?,
                ))),
                b,
            ),
            UnitBind(a, b) => (
                Some(VarDeclOrExpr::Expr(Box::new(self.expr(sigma, loc, a)?))),
                b,
            ),
            _ => unreachable!(),
        };

        let (test, body) = match body.as_ref() {
            Let(_, a, b) => (Some(Box::new(self.expr(sigma, loc, a)?)), b),
            _ => unreachable!(),
        };

        let (update, body) = match body.as_ref() {
            Update(v, a, b) => (Some(Box::new(self.update(sigma, loc, v, a)?)), b),
            UnitBind(a, b) => (Some(Box::new(self.expr(sigma, loc, a)?)), b),
            _ => unreachable!(),
        };

        Ok(Stmt::For(ForStmt {
            span: loc.into(),
            init,
            test,
            update,
            body: Box::new(Stmt::Block(self.block(sigma, loc, body, false)?)),
        }))
    }

    fn guard_stmt(
        &mut self,
        sigma: &Sigma,
        loc: Loc,
        p: &Term,
        e: &Option<Box<Term>>,
        b: &Term,
    ) -> Result<Stmt, Error> {
        Ok(Stmt::If(IfStmt {
            span: loc.into(),
            test: Box::new(self.expr(sigma, loc, p)?),
            cons: Box::new(Stmt::Block(self.block(sigma, loc, b, false)?)),
            alt: if let Some(e) = e {
                Some(Box::new(Stmt::Block(self.block(sigma, loc, e, false)?)))
            } else {
                None
            },
        }))
    }

    fn block(
        &mut self,
        sigma: &Sigma,
        loc: Loc,
        body: &Term,
        returns: bool,
    ) -> Result<BlockStmt, Error> {
        fn strip_untupled_lets(mut tm: &Term) -> &Term {
            use Term::*;

            // Only strip the tupled lets from the parameters.
            if let TupleBind(_, _, a, _) = tm {
                if !matches!(a.as_ref(), Ref(v) if v.as_str() == TUPLED) {
                    return tm;
                }
            }

            loop {
                if let TupleBind(_, q, _, b) = tm {
                    let rhs = q.var.as_str();
                    if rhs.starts_with(UNTUPLED_RHS_PREFIX) {
                        tm = b;
                        if rhs != UNTUPLED_ENDS {
                            continue;
                        }
                    }
                }
                return tm;
            }
        }

        use Term::*;

        let mut stmts = Vec::default();
        let span = loc.into();

        let mut tm = strip_untupled_lets(body);
        loop {
            match tm {
                Const(p, a, b) | Let(p, a, b) => {
                    stmts.push(Stmt::Decl(Decl::Var(Box::new(
                        self.bind_decl(sigma, loc, &p.var, a)?,
                    ))));
                    tm = b
                }
                Update(v, a, b) => {
                    stmts.push(Stmt::Expr(ExprStmt {
                        span,
                        expr: Box::new(self.update(sigma, loc, v, a)?),
                    }));
                    tm = b;
                }
                While(p, b, r) => {
                    stmts.push(self.while_stmt(sigma, loc, p, b)?);
                    tm = r
                }
                Fori(b, r) => {
                    stmts.push(self.fori_stmt(sigma, loc, b)?);
                    tm = r
                }
                Guard(p, b, e, r) => {
                    stmts.push(self.guard_stmt(sigma, loc, p, e, b)?);
                    tm = r
                }
                Return(a) => {
                    stmts.push(Stmt::Return(ReturnStmt {
                        span,
                        arg: Some(Box::new(self.expr(sigma, loc, a)?)),
                    }));
                    tm = &TT
                }
                Continue => {
                    stmts.push(Stmt::Continue(ContinueStmt { span, label: None }));
                    tm = &TT
                }
                Break => {
                    stmts.push(Stmt::Break(BreakStmt { span, label: None }));
                    tm = &TT
                }
                // Only valid on syntax like `const (a, b, c, d) = expr`.
                TupleBind(p, q, a, b) => {
                    // Collect all tupled lets to form `const [a, b, c, d] = expr` in JS.
                    let (elems, body) = Self::tuple_binds_to_pats(loc, p, q, b);
                    stmts.push(Stmt::Decl(Decl::Var(Box::new(VarDecl {
                        span,
                        ctxt: Default::default(),
                        kind: VarDeclKind::Var,
                        declare: false,
                        decls: vec![VarDeclarator {
                            span,
                            name: Pat::Array(ArrayPat {
                                span,
                                elems,
                                optional: false,
                                type_ann: None,
                            }),
                            init: Some(Box::new(self.expr(sigma, loc, a)?)),
                            definite: false,
                        }],
                    }))));
                    tm = body;
                }
                UnitBind(a, b) => {
                    stmts.extend(self.block(sigma, loc, a, false)?.stmts);
                    tm = b
                }
                _ => {
                    if matches!(tm, TT) && !returns {
                        // Remove the unnecessary tailing blank statement.
                        break;
                    }

                    let expr = Box::new(self.expr(sigma, loc, tm)?);
                    stmts.push(if returns {
                        Stmt::Return(ReturnStmt {
                            span,
                            arg: Some(expr),
                        })
                    } else {
                        Stmt::Expr(ExprStmt { span, expr })
                    });
                    break;
                }
            }
        }
        Ok(BlockStmt {
            span,
            ctxt: Default::default(),
            stmts,
        })
    }

    fn non_spread(e: Expr) -> ExprOrSpread {
        ExprOrSpread {
            spread: None,
            expr: Box::new(e),
        }
    }

    fn spread(loc: Loc, e: Expr) -> ExprOrSpread {
        ExprOrSpread {
            spread: Some(loc.into()),
            expr: Box::new(e),
        }
    }

    fn expr(&mut self, sigma: &Sigma, loc: Loc, tm: &Term) -> Result<Expr, Error> {
        use Term::*;
        Ok(match tm {
            MetaRef(k, r, sp) => match Self::solution(sigma, r) {
                None => return Err(UnsolvedMeta(MetaRef(k.clone(), r.clone(), sp.clone()), loc)),
                Some(_) => unreachable!(),
            },

            Const(p, a, b) | Let(p, a, b) => {
                self.lambda_encoded_let(sigma, loc, Some(&p.var), a, b)?
            }
            UnitBind(a, b) => self.lambda_encoded_let(sigma, loc, None, a, b)?,

            // Tuple here should only be used as anonymous variadic arguments.
            Tuple(a, b) => {
                let mut elems = vec![Some(Self::non_spread(self.expr(sigma, loc, a)?))];
                let mut body = b.as_ref();
                loop {
                    match body {
                        Tuple(arg, b) => {
                            body = b.as_ref();
                            elems.push(Some(Self::non_spread(self.expr(sigma, loc, arg)?)));
                        }
                        TT => break,
                        _ => unreachable!(),
                    }
                }
                Expr::Array(ArrayLit {
                    span: loc.into(),
                    elems,
                })
            }
            // Ditto.
            //
            // Transform into `((a, b, c, d) => stripped_body)(a)`.
            TupleBind(p, q, a, b) => {
                let (elems, body) = Self::tuple_binds_to_pats(loc, p, q, b);
                Self::paren_call1(
                    loc,
                    Self::block_arrow(
                        loc,
                        vec![Pat::Array(ArrayPat {
                            span: loc.into(),
                            elems,
                            optional: false,
                            type_ann: None,
                        })],
                        self.block(sigma, loc, body, true)?,
                        false,
                    ),
                    self.expr(sigma, loc, a)?,
                )
            }

            Ref(r) if self.not_escaping_this => Expr::Ident(Self::asis_ident(loc, r)),
            Ref(r) | Undef(r) => Expr::Ident(Self::ident(loc, r)),
            Extern(r) => Expr::Member(MemberExpr {
                span: loc.into(),
                obj: Box::new(Expr::Ident(Self::lib())),
                prop: MemberProp::Ident(IdentName::from(Self::ident(loc, r))),
            }),
            Qualified(m, r) => Expr::Member(MemberExpr {
                span: loc.into(),
                obj: Box::new(Expr::Ident(Self::str_ident(loc, self.to_qualifier(m)))),
                prop: MemberProp::Ident(IdentName::from(Self::ident(loc, r))),
            }),
            Lam(p, b) => match p.info {
                Explicit => Self::block_arrow(
                    loc,
                    Self::type_erased_pats(loc, None, b),
                    self.block(sigma, loc, b, true)?,
                    false,
                ),
                _ => self.expr(sigma, loc, b)?,
            },

            App(f, i, x) => self.app(sigma, loc, f, i, x)?,
            TT => Self::undefined(),
            False => Expr::Lit(Lit::Bool(Bool {
                span: loc.into(),
                value: false,
            })),
            True => Expr::Lit(Lit::Bool(Bool {
                span: loc.into(),
                value: true,
            })),
            If(p, t, e) => Expr::Cond(CondExpr {
                span: loc.into(),
                test: Box::new(self.expr(sigma, loc, p)?),
                cons: Box::new(self.expr(sigma, loc, t)?),
                alt: Box::new(self.expr(sigma, loc, e)?),
            }),
            BoolOr(a, b) => self.bin_expr(sigma, loc, BinaryOp::LogicalOr, a, b)?,
            BoolAnd(a, b) => self.bin_expr(sigma, loc, BinaryOp::LogicalAnd, a, b)?,
            BoolNot(a) => self.unary_expr(sigma, loc, UnaryOp::Bang, a)?,
            BoolEq(a, b) => self.bin_expr(sigma, loc, BinaryOp::EqEqEq, a, b)?,
            BoolNeq(a, b) => self.bin_expr(sigma, loc, BinaryOp::NotEqEq, a, b)?,
            Str(s) => Expr::Lit(Lit::Str(Self::js_raw_str(loc, s))),
            StrAdd(a, b) => self.bin_expr(sigma, loc, BinaryOp::Add, a, b)?,
            StrEq(a, b) => self.bin_expr(sigma, loc, BinaryOp::EqEqEq, a, b)?,
            StrNeq(a, b) => self.bin_expr(sigma, loc, BinaryOp::NotEqEq, a, b)?,
            StrToLowerCase(a) => Self::prototype(loc, self.expr(sigma, loc, a)?, "toLowerCase", []),
            Num(v) => Expr::Lit(Lit::Num(JsNumber {
                span: loc.into(),
                value: *v,
                raw: None,
            })),
            NumAdd(a, b) => self.bin_expr(sigma, loc, BinaryOp::Add, a, b)?,
            NumSub(a, b) => self.bin_expr(sigma, loc, BinaryOp::Sub, a, b)?,
            NumMul(a, b) => self.bin_expr(sigma, loc, BinaryOp::Mul, a, b)?,
            NumDiv(a, b) => self.bin_expr(sigma, loc, BinaryOp::Div, a, b)?,
            NumMod(a, b) => self.bin_expr(sigma, loc, BinaryOp::Mod, a, b)?,
            NumEq(a, b) => self.bin_expr(sigma, loc, BinaryOp::EqEqEq, a, b)?,
            NumNeq(a, b) => self.bin_expr(sigma, loc, BinaryOp::NotEqEq, a, b)?,
            NumLe(a, b) => self.bin_expr(sigma, loc, BinaryOp::LtEq, a, b)?,
            NumGe(a, b) => self.bin_expr(sigma, loc, BinaryOp::GtEq, a, b)?,
            NumLt(a, b) => self.bin_expr(sigma, loc, BinaryOp::Lt, a, b)?,
            NumGt(a, b) => self.bin_expr(sigma, loc, BinaryOp::Gt, a, b)?,
            NumNeg(a) => self.unary_expr(sigma, loc, UnaryOp::Minus, a)?,
            NumToStr(a) | BigintToStr(a) => {
                Self::prototype(loc, self.expr(sigma, loc, a)?, "toString", [])
            }
            Big(v) => Expr::Lit(Lit::BigInt(JsBigInt {
                span: loc.into(),
                value: Box::new(BigIntValue::from_str(v).unwrap()),
                raw: None,
            })),
            ArrIterNext(it) => Self::optionify_iteration_result(
                loc,
                Self::prototype(loc, self.expr(sigma, loc, it)?, "next", []),
            ),
            Arr(xs) => {
                let mut elems = Vec::default();
                for x in xs {
                    elems.push(Some(Self::non_spread(self.expr(sigma, loc, x)?)));
                }
                Expr::Array(ArrayLit {
                    span: loc.into(),
                    elems,
                })
            }
            ArrLength(a) => Self::access(loc, self.expr(sigma, loc, a)?, "length"),
            ArrPush(a, v) => {
                let v = self.expr(sigma, loc, v)?;
                Self::prototype(loc, self.expr(sigma, loc, a)?, "push", [v])
            }
            ArrForeach(a, f) => {
                let f = self.expr(sigma, loc, f)?;
                Self::prototype(loc, self.expr(sigma, loc, a)?, "forEach", [f])
            }
            ArrAt(a, i) => {
                let i = self.expr(sigma, loc, i)?;
                let ret = Self::prototype(loc, self.expr(sigma, loc, a)?, "at", [i]);
                Self::optionify(loc, ret)
            }
            // void (a[i] = v)
            ArrInsert(a, i, v) => Expr::Unary(UnaryExpr {
                span: loc.into(),
                op: UnaryOp::Void,
                arg: Box::new(Self::paren(
                    loc,
                    Expr::Assign(AssignExpr {
                        span: loc.into(),
                        op: AssignOp::Assign,
                        left: AssignTarget::Simple(SimpleAssignTarget::Member(MemberExpr {
                            span: loc.into(),
                            obj: Box::new(self.expr(sigma, loc, a)?),
                            prop: MemberProp::Computed(ComputedPropName {
                                span: loc.into(),
                                expr: Box::new(self.expr(sigma, loc, i)?),
                            }),
                        })),
                        right: Box::new(self.expr(sigma, loc, v)?),
                    }),
                )),
            }),
            ArrIter(a) => self.well_known_symbol_call(sigma, loc, a, "iterator")?,
            MapIterNext(it) => Self::entryify_iteration_result(
                loc,
                Self::prototype(loc, self.expr(sigma, loc, it)?, "next", []),
            ),
            Kv(xs) => {
                let mut elems = Vec::default();
                for (k, v) in xs {
                    elems.push(Some(Self::non_spread(Self::tuple(
                        loc,
                        self.expr(sigma, loc, k)?,
                        self.expr(sigma, loc, v)?,
                    ))));
                }
                Expr::New(NewExpr {
                    span: loc.into(),
                    ctxt: Default::default(),
                    callee: Box::new(Expr::Ident(Self::special_ident("Map"))),
                    args: Some(vec![Self::non_spread(Expr::Array(ArrayLit {
                        span: loc.into(),
                        elems,
                    }))]),
                    type_args: None,
                })
            }
            MapHas(m, k) => {
                let k = self.expr(sigma, loc, k)?;
                Self::prototype(loc, self.expr(sigma, loc, m)?, "has", [k])
            }
            MapGet(m, k) => {
                let k = self.expr(sigma, loc, k)?;
                Self::prototype(loc, self.expr(sigma, loc, m)?, "get", [k])
            }
            MapSet(m, k, v) => {
                let k = self.expr(sigma, loc, k)?;
                let v = self.expr(sigma, loc, v)?;
                Self::prototype(loc, self.expr(sigma, loc, m)?, "set", [k, v])
            }
            MapDelete(m, k) => {
                let k = self.expr(sigma, loc, k)?;
                Self::prototype(loc, self.expr(sigma, loc, m)?, "delete", [k])
            }
            MapIter(m) => self.well_known_symbol_call(sigma, loc, m, "iterator")?,
            MapClear(m) => Self::prototype(loc, self.expr(sigma, loc, m)?, "clear", []),
            Obj(f) => match f.as_ref() {
                Fields(fields) => {
                    let mut props = Vec::default();
                    for (name, tm) in fields {
                        props.push(PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                            key: PropName::Ident(IdentName::from(Self::str_ident(loc, name))),
                            value: Box::new(self.expr(sigma, loc, &tm.clone())?),
                        }))));
                    }
                    Self::paren(
                        loc,
                        Expr::Object(ObjectLit {
                            span: loc.into(),
                            props,
                        }),
                    )
                }
                _ => unreachable!(),
            },
            Cat(a, b) => Expr::Object(ObjectLit {
                span: loc.into(),
                props: vec![
                    PropOrSpread::Spread(SpreadElement {
                        dot3_token: loc.into(),
                        expr: Box::new(self.expr(sigma, loc, a)?),
                    }),
                    PropOrSpread::Spread(SpreadElement {
                        dot3_token: loc.into(),
                        expr: Box::new(self.expr(sigma, loc, b)?),
                    }),
                ],
            }),
            Access(a, n) => Self::access(loc, self.expr(sigma, loc, a)?, n),
            Down(a, to) => {
                // ((x) => {a: x.a, b: x.b})(n)
                let x = Self::str_ident(loc, "x");

                let fields = match to.as_ref() {
                    Fields(fields) => fields,
                    MetaRef(k, m, sp) => match Self::solution(sigma, m) {
                        None => {
                            return Err(UnsolvedMeta(
                                MetaRef(k.clone(), m.clone(), sp.clone()),
                                loc,
                            ));
                        }
                        Some(fields) => match fields.as_ref() {
                            Fields(fields) => fields,
                            _ => unreachable!(),
                        },
                    },
                    _ => unreachable!(),
                };
                let mut props = Vec::default();
                for name in fields.keys() {
                    props.push(PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                        key: PropName::Ident(IdentName::from(Self::str_ident(loc, name))),
                        value: Box::new(Expr::Member(MemberExpr {
                            span: loc.into(),
                            obj: Box::new(Self::paren(loc, Expr::Ident(x.clone()))),
                            prop: MemberProp::Ident(IdentName::from(Self::str_ident(loc, name))),
                        })),
                    }))))
                }

                let body = Self::paren(
                    loc,
                    Expr::Object(ObjectLit {
                        span: loc.into(),
                        props,
                    }),
                );

                Self::paren_call1(
                    loc,
                    Self::short_arrow(
                        loc,
                        vec![Pat::Ident(BindingIdent {
                            id: x,
                            type_ann: None,
                        })],
                        body,
                    ),
                    self.expr(sigma, loc, a)?,
                )
            }
            Variant(f) => match f.as_ref() {
                Fields(fields) => {
                    let (name, tm) = fields.iter().next().unwrap();
                    Self::variant(loc, name, self.expr(sigma, loc, tm)?)
                }
                _ => unreachable!(),
            },
            Up(a, _, _) => self.expr(sigma, loc, a)?,
            Switch(a, cs, d) => {
                // ((x) => {
                //      if ("Ok" in x) {
                //          return ((a) => { return a + 1; })(x["Ok"]);
                //      }
                //      if ("None" in x) {
                //          return ((_) => { return undefined; })(x["None"]);
                //      }
                //      return ((d) => { return d; })(x)
                // })(x)

                let mut stmts = Vec::default();
                for (x, (v, tm)) in cs {
                    stmts.push(Stmt::If(IfStmt {
                        span: loc.into(),
                        test: Box::new(Expr::Bin(BinExpr {
                            span: loc.into(),
                            op: BinaryOp::In,
                            left: Box::new(Expr::Lit(Lit::Str(Self::js_str(loc, x)))),
                            right: Box::new(Expr::Ident(Self::str_ident(loc, "x"))),
                        })),
                        cons: Box::new(self.enum_case_consequent(sigma, loc, Some(x), v, tm)?),
                        alt: None,
                    }));
                }
                if let Some((v, tm)) = d {
                    stmts.push(self.enum_case_consequent(sigma, loc, None, v, tm)?)
                }

                Self::paren_call1(
                    loc,
                    Self::block_arrow(
                        loc,
                        vec![Self::str_ident_pat(loc, "x")],
                        BlockStmt {
                            span: loc.into(),
                            ctxt: Default::default(),
                            stmts,
                        },
                        false,
                    ),
                    self.expr(sigma, loc, a)?,
                )
            }
            // Object.values(a)[0]
            Unionify(a) => Self::index(
                loc,
                Self::prototype(
                    loc,
                    Expr::Ident(Self::special_ident("Object")),
                    "values",
                    [self.expr(sigma, loc, a)?],
                ),
                0.0,
            ),
            Panic(a) => Self::iife(
                loc,
                BlockStmt {
                    span: loc.into(),
                    ctxt: Default::default(),
                    stmts: vec![Stmt::Throw(ThrowStmt {
                        span: loc.into(),
                        arg: Box::new(Self::paren_call1(
                            loc,
                            Expr::Ident(Self::special_ident("Error")),
                            self.expr(sigma, loc, a)?,
                        )),
                    })],
                },
                false,
            ),
            ConsoleLog(m) => Self::call(
                loc,
                Expr::Member(MemberExpr {
                    span: loc.into(),
                    obj: Box::new(Expr::Ident(Self::special_ident("console"))),
                    prop: MemberProp::Ident(IdentName::from(Self::special_ident("log"))),
                }),
                match m.as_ref() {
                    Tuple(..) => self.untuple_args(sigma, loc, m)?,
                    TT => Default::default(),
                    m => vec![Self::non_spread(self.expr(sigma, loc, m)?)],
                },
            ),
            SetTimeout(f, d, x) => {
                let mut args = vec![
                    Self::non_spread(self.expr(sigma, loc, f)?),
                    Self::non_spread(self.expr(sigma, loc, d)?),
                ];
                args.extend(self.untuple_args(sigma, loc, x)?);
                Self::call(loc, Expr::Ident(Self::special_ident("setTimeout")), args)
            }
            JSONStringify(a) => Self::call(
                loc,
                Expr::Member(MemberExpr {
                    span: loc.into(),
                    obj: Box::new(Expr::Ident(Self::special_ident("JSON"))),
                    prop: MemberProp::Ident(IdentName::from(Self::special_ident("stringify"))),
                }),
                vec![Self::non_spread(self.expr(sigma, loc, a)?)],
            ),
            HtmlElementAddEventListener(n, e, l) => Self::prototype(
                loc,
                Self::paren(loc, self.expr(sigma, loc, n)?),
                "addEventListener",
                [self.expr(sigma, loc, e)?, self.expr(sigma, loc, l)?],
            ),
            DocumentGetElementById(a) => Self::optionify(
                loc,
                Self::call(
                    loc,
                    Expr::Member(MemberExpr {
                        span: loc.into(),
                        obj: Box::new(Expr::Ident(Self::special_ident("document"))),
                        prop: MemberProp::Ident(IdentName::from(Self::special_ident(
                            "getElementById",
                        ))),
                    }),
                    vec![Self::non_spread(self.expr(sigma, loc, a)?)],
                ),
            ),
            EmitAsync(a) => self.expr(sigma, loc, a)?,

            tm if matches!(tm, Fori(..) | While(..) | Guard(..)) => {
                Self::iife(loc, self.block(sigma, loc, tm, true)?, false)
            }

            Rk(..) | RkToStr(..) | At(..) | Typeof(..) | Keyof(..) | Discriminants(..) => {
                return Err(NonErasable(tm.clone(), loc));
            }

            _ => unreachable!(),
        })
    }

    fn imports(&self, imports: Box<[Import]>) -> Result<Vec<ModuleItem>, Error> {
        use ImportedDefs::*;
        let mut items = Vec::default();
        for i in imports {
            let mut specifiers = Vec::default();
            match i.defs {
                Unqualified(defs) => {
                    for (loc, d) in defs {
                        specifiers.push(ImportSpecifier::Named(ImportNamedSpecifier {
                            span: loc.into(),
                            local: Self::str_ident(loc, d),
                            imported: None,
                            is_type_only: false,
                        }))
                    }
                }
                Qualified => {
                    specifiers.push(ImportSpecifier::Namespace(ImportStarAsSpecifier {
                        span: i.loc.into(),
                        local: Self::str_ident(i.loc, self.to_qualifier(&i.module)),
                    }));
                }
                Loaded => {}
            }
            items.push(ModuleItem::ModuleDecl(ModuleDecl::Import(ImportDecl {
                span: DUMMY_SP,
                specifiers,
                src: Box::new(Self::js_path(
                    i.module.to_generated_path().join(self.filename()),
                )),
                type_only: false,
                with: None,
                phase: Default::default(),
            })))
        }
        Ok(items)
    }

    fn includes(&mut self, includes: &[Box<Path>]) -> Result<Vec<ModuleItem>, Error> {
        let mut items = Vec::default();
        let mut props = Vec::default();
        for i in includes {
            let src = Path::new(".").join(i.file_name().unwrap());
            let ns = format!(
                "{JS_LIB_PREFIX}{}",
                i.file_stem().unwrap().to_string_lossy()
            ); // avoid naming conflicts
            items.push(ModuleItem::ModuleDecl(ModuleDecl::Import(ImportDecl {
                span: DUMMY_SP,
                specifiers: vec![ImportSpecifier::Namespace(ImportStarAsSpecifier {
                    span: DUMMY_SP,
                    local: Ident {
                        span: DUMMY_SP,
                        ctxt: Default::default(),
                        sym: ns.clone().into(),
                        optional: false,
                    },
                })],
                src: Box::new(Self::js_path(src)),
                type_only: false,
                with: None,
                phase: Default::default(),
            })));
            props.push(PropOrSpread::Spread(SpreadElement {
                dot3_token: DUMMY_SP,
                expr: Box::new(Expr::Ident(Ident {
                    span: DUMMY_SP,
                    ctxt: Default::default(),
                    sym: ns.into(),
                    optional: false,
                })),
            }));
        }
        if !props.is_empty() {
            items.push(ModuleItem::Stmt(Stmt::Decl(Decl::Var(Box::new(VarDecl {
                span: DUMMY_SP,
                ctxt: Default::default(),
                kind: VarDeclKind::Const,
                declare: false,
                decls: vec![VarDeclarator {
                    span: DUMMY_SP,
                    name: Pat::Ident(BindingIdent {
                        id: Self::lib(),
                        type_ann: None,
                    }),
                    init: Some(Box::new(Expr::Object(ObjectLit {
                        span: DUMMY_SP,
                        props,
                    }))),
                    definite: false,
                }],
            })))))
        }
        Ok(items)
    }

    fn defs(&mut self, sigma: &Sigma, defs: Box<[Def<Term>]>) -> Result<Vec<ModuleItem>, Error> {
        use Body::*;
        let mut items = Vec::default();
        for def in defs {
            debug!(target: "codegen", "generating definition: {def}");
            match match &def.body {
                Fn(f) | Method { f, .. } => self.func_decl(&mut items, sigma, &def, f),
                Postulate => self.postulate_decl(&mut items, &def),
                Constant(_, f) => self.const_decl(&mut items, sigma, &def, f),
                Class { ctor, methods, .. } => {
                    self.not_escaping_this = true;
                    let ret = self.ctor_helper_decl(&mut items, sigma, &def.name, ctor, methods);
                    self.not_escaping_this = false;
                    ret
                }
                Undefined => match sigma.get(&def.name).unwrap().clone().body {
                    Fn(f) => self.func_decl(&mut items, sigma, &def, &f),
                    _ => unreachable!(),
                },
                _ => continue,
            } {
                Ok(..) => continue,
                Err(NonErasable(..)) => {
                    debug!(target: "codegen", "skipping non-erasable definition: {}", def.name);
                    continue;
                }
                Err(e) => return Err(e),
            };
        }
        Ok(items)
    }

    fn try_export_decl(def: &Def<Term>, decl: Decl) -> ModuleItem {
        if !def.is_public {
            ModuleItem::Stmt(Stmt::Decl(decl))
        } else {
            ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
                span: def.loc.into(),
                decl,
            }))
        }
    }

    fn func_decl(
        &mut self,
        items: &mut Vec<ModuleItem>,
        sigma: &Sigma,
        def: &Def<Term>,
        body: &Term,
    ) -> Result<(), Error> {
        items.push(Self::try_export_decl(
            def,
            Decl::Fn(FnDecl {
                ident: Self::ident(def.loc, &def.name),
                declare: false,
                function: Box::new(self.func(sigma, def, body)?),
            }),
        ));
        Ok(())
    }

    fn postulate_decl(&self, items: &mut Vec<ModuleItem>, def: &Def<Term>) -> Result<(), Error> {
        if !def.is_public {
            return Ok(());
        }
        if matches!(def.ret.as_ref(), Term::Univ) {
            return Ok(());
        }
        items.push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
            span: def.loc.into(),
            decl: Decl::Var(Box::new(VarDecl {
                span: def.loc.into(),
                ctxt: Default::default(),
                kind: VarDeclKind::Const,
                declare: false,
                decls: vec![VarDeclarator {
                    span: def.loc.into(),
                    name: Self::ident_pat(def.loc, &def.name),
                    init: Some(Box::new(Expr::Member(MemberExpr {
                        span: def.loc.into(),
                        obj: Box::new(Expr::Ident(Self::special_ident(JS_LIB))),
                        prop: MemberProp::Ident(IdentName::from(Self::ident(def.loc, &def.name))),
                    }))),
                    definite: false,
                }],
            })),
        })));
        Ok(())
    }

    fn const_decl(
        &mut self,
        items: &mut Vec<ModuleItem>,
        sigma: &Sigma,
        def: &Def<Term>,
        f: &Term,
    ) -> Result<(), Error> {
        let is_async = Self::is_async(def);
        let expr = Box::new(if f.is_binder() {
            Self::iife(def.loc, self.block(sigma, def.loc, f, true)?, is_async)
        } else {
            self.expr(sigma, def.loc, f)?
        });
        items.push(if def.name.is_unbound() {
            ModuleItem::Stmt(Stmt::Expr(ExprStmt {
                span: def.loc.into(),
                expr,
            }))
        } else {
            Self::try_export_decl(
                def,
                Decl::Var(Box::new(VarDecl {
                    span: def.loc.into(),
                    ctxt: Default::default(),
                    kind: VarDeclKind::Const,
                    declare: false,
                    decls: vec![VarDeclarator {
                        span: def.loc.into(),
                        name: Self::ident_pat(def.loc, &def.name),
                        init: Some(expr),
                        definite: false,
                    }],
                })),
            )
        });
        Ok(())
    }

    fn ctor_helper_decl(
        &mut self,
        items: &mut Vec<ModuleItem>,
        sigma: &Sigma,
        name: &Var,
        ctor: &Var,
        methods: &HashMap<Src, Var>,
    ) -> Result<(), Error> {
        let ctor_def = sigma.get(ctor).unwrap();
        let mut ctor_func = match &ctor_def.body {
            Body::Method { f, .. } => self.func(sigma, ctor_def, f)?,
            _ => unreachable!(),
        };

        let mut meths = Vec::default();
        for (short, m) in methods {
            let meth_def = sigma.get(m).unwrap();
            let meth = match &meth_def.body {
                Body::Method { f, .. } => f,
                _ => unreachable!(),
            };

            let mut params = Self::type_erased_params(meth_def.loc, &meth_def.tele, meth);
            if params.is_empty() {
                continue; // looks like a static method
            }
            params.remove(0); // strips `this`

            let mut args = vec![Self::non_spread(Expr::Ident(Self::special_ident(THIS)))];
            for x in &params {
                args.push(Self::non_spread(Expr::Ident(match &x.pat {
                    Pat::Ident(binding) => binding.id.clone(),
                    _ => unreachable!(),
                })));
            }

            // Simply a proxy call.
            meths.push(Prop::Method(MethodProp {
                key: PropName::Ident(IdentName::from(Self::str_ident(meth_def.loc, short))),
                function: Box::new(Function {
                    params,
                    decorators: Default::default(),
                    span: meth_def.loc.into(),
                    ctxt: Default::default(),
                    body: Some(BlockStmt {
                        span: meth_def.loc.into(),
                        ctxt: Default::default(),
                        stmts: vec![Stmt::Return(ReturnStmt {
                            span: meth_def.loc.into(),
                            arg: Some(Box::new(Expr::Call(CallExpr {
                                span: meth_def.loc.into(),
                                ctxt: Default::default(),
                                callee: Callee::Expr(Box::new(Expr::Ident(Self::ident(
                                    meth_def.loc,
                                    m,
                                )))),
                                args,
                                type_args: None,
                            }))),
                        })],
                    }),
                    is_generator: false,
                    is_async: false,
                    type_params: None,
                    return_type: None,
                }),
            }))
        }

        ctor_func.body = Some(BlockStmt {
            span: ctor_def.loc.into(),
            ctxt: Default::default(),
            stmts: {
                let mut stmts = Vec::default();
                for stmt in ctor_func.body.unwrap().stmts {
                    let (span, obj) = match stmt {
                        Stmt::Return(ReturnStmt { span, arg }) => (span, *arg.unwrap()),
                        stmt => {
                            stmts.push(stmt);
                            continue;
                        }
                    };
                    let obj = match obj {
                        Expr::Paren(ParenExpr { expr, .. }) => *expr,
                        e => e,
                    };
                    let arg = Some(Box::new(match obj {
                        Expr::Object(ObjectLit { span, mut props }) => {
                            for prop in meths {
                                props.push(PropOrSpread::Prop(Box::new(prop)));
                            }
                            Expr::Object(ObjectLit { span, props })
                        }
                        e => e,
                    }));
                    stmts.push(Stmt::Return(ReturnStmt { span, arg }));
                    break;
                }
                stmts
            },
        });

        items.push(Self::try_export_decl(
            ctor_def,
            Decl::Fn(FnDecl {
                ident: Self::ident(ctor_def.loc, name),
                declare: false,
                function: Box::new(ctor_func),
            }),
        ));
        Ok(())
    }
}

pub const OUT_FILE: &str = "index.mjs";
pub const QUALIFIER_SEP: &str = "$";

impl Target for Ecma {
    fn filename(&self) -> &'static str {
        OUT_FILE
    }

    fn to_qualifier(&self, module: &ModuleID) -> Src {
        use ImportedPkg::*;
        let mut ret = match &module.pkg {
            Std(p) => vec![*p],
            Vendor(o, p) => vec![o.strip_prefix('@').unwrap(), p],
            Root => vec![QUALIFIER_SEP],
        };
        for m in &module.modules {
            ret.push(m.to_str().unwrap());
        }
        ret.join(QUALIFIER_SEP).leak()
    }

    fn should_include(&self, path: &Path) -> bool {
        match path.file_name() {
            None => false,
            Some(f) if f == OUT_FILE => false,
            _ => matches!(path.extension(), Some(ext) if ext == "js" || ext == "mjs"),
        }
    }

    fn module(
        &mut self,
        buf: &mut Vec<u8>,
        sigma: &Sigma,
        includes: &[Box<Path>],
        file: File<Term>,
        is_first_file: bool,
    ) -> Result<(), Error> {
        let mut body = Vec::default();
        if is_first_file {
            body.push(ModuleItem::Stmt(Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Lit(Lit::Str(Self::js_str(
                    Default::default(),
                    "use strict",
                )))),
            })));
        }
        body.extend(self.imports(file.imports)?);
        body.extend(self.includes(includes)?);
        body.extend(self.defs(sigma, file.defs)?);

        let m = Module {
            span: DUMMY_SP,
            body,
            shebang: None,
        };
        let cm = Rc::<SourceMap>::default();
        Emitter {
            cfg: Default::default(),
            cm: cm.clone(),
            comments: None,
            wr: JsWriter::new(cm, "\n", buf, None),
        }
        .emit_module(&m)
        .map_err(|e| Error::IO(file.path, e))?;

        Ok(())
    }
}
