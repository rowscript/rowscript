use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::str::FromStr;

use log::debug;
use num_bigint::BigInt as BigIntValue;
use swc_atoms::js_word;
use swc_common::{BytePos, SourceMap, Span, DUMMY_SP};
use swc_ecma_ast::{
    ArrayLit, ArrowExpr, AssignExpr, AssignOp, AssignTarget, BigInt as JsBigInt, BinExpr, BinaryOp,
    BindingIdent, BlockStmt, BlockStmtOrExpr, Bool, BreakStmt, CallExpr, Callee, ComputedPropName,
    CondExpr, ContinueStmt, Decl, ExportDecl, Expr, ExprOrSpread, ExprStmt, FnDecl, ForStmt,
    Function, Ident, IfStmt, ImportDecl, ImportNamedSpecifier, ImportSpecifier,
    ImportStarAsSpecifier, KeyValueProp, Lit, MemberExpr, MemberProp, Module, ModuleDecl,
    ModuleItem, NewExpr, Number as JsNumber, Number, ObjectLit, Param as JsParam, ParenExpr, Pat,
    Prop, PropName, PropOrSpread, ReturnStmt, SimpleAssignTarget, SpreadElement, Stmt, Str,
    SwitchCase, SwitchStmt, ThrowStmt, UnaryExpr, UnaryOp, VarDecl, VarDeclKind, VarDeclOrExpr,
    VarDeclarator, WhileStmt,
};
use swc_ecma_codegen::text_writer::JsWriter;
use swc_ecma_codegen::Emitter;

use crate::codegen::Target;
use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Body, Def, Sigma};
use crate::theory::conc::data::ArgInfo;
use crate::theory::conc::data::ArgInfo::{UnnamedExplicit, UnnamedImplicit};
use crate::theory::conc::load::{Import, ImportedDefs, ImportedPkg, ModuleID};
use crate::theory::ParamInfo::Explicit;
use crate::theory::{Loc, Param, Tele, Var, THIS, TUPLED, UNBOUND, UNTUPLED_RHS_PREFIX};
use crate::Error::{NonErasable, UnsolvedMeta};
use crate::{Error, ModuleFile};

impl From<Loc> for Span {
    fn from(loc: Loc) -> Self {
        Self {
            lo: BytePos(loc.start as u32),
            hi: BytePos(loc.end as u32),
            ctxt: Default::default(),
        }
    }
}

const JS_LIB: &str = "__lib";
const JS_LIB_PREFIX: &str = "__lib__";
const JS_ESCAPED_THIS: &str = "__this";
const JS_ENUM_TAG: &str = "__enumT";
const JS_ENUM_VAL: &str = "__enumV";

#[derive(Default)]
pub struct Ecma {}

impl Ecma {
    fn solution<'a>(sigma: &'a Sigma, m: &'a Var) -> Option<&'a Term> {
        use Body::*;
        match &sigma.get(m).unwrap().body {
            Meta(_, s) => s.as_ref(),
            _ => unreachable!(),
        }
    }

    fn special_ident(s: &str) -> Ident {
        Ident {
            span: DUMMY_SP,
            sym: s.into(),
            optional: false,
        }
    }

    fn str_ident(loc: Loc, s: &str) -> Ident {
        Ident {
            span: loc.into(),
            sym: match s {
                THIS => JS_ESCAPED_THIS,
                s => s,
            }
            .into(),
            optional: false,
        }
    }

    fn ident(loc: Loc, v: &Var) -> Ident {
        Self::str_ident(loc, v.as_str())
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

    fn lib() -> Ident {
        Self::special_ident(JS_LIB)
    }

    fn js_raw_str(loc: Loc, s: &str) -> Str {
        Str {
            span: loc.into(),
            value: js_word!(""),
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

    fn paren_call(loc: Loc, f: Expr, e: Expr) -> Expr {
        Expr::Call(CallExpr {
            span: loc.into(),
            callee: Callee::Expr(Box::new(Expr::Paren(ParenExpr {
                span: loc.into(),
                expr: Box::new(f),
            }))),
            args: vec![ExprOrSpread {
                spread: None,
                expr: Box::new(e),
            }],
            type_args: None,
        })
    }

    fn variant(loc: Loc, tag: &str, v: Expr) -> Expr {
        Expr::Object(ObjectLit {
            span: loc.into(),
            props: vec![
                PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                    key: PropName::Str(Self::js_raw_str(loc, JS_ENUM_TAG)),
                    value: Box::new(Expr::Lit(Lit::Str(Self::js_str(loc, tag)))),
                }))),
                PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                    key: PropName::Str(Self::js_raw_str(loc, JS_ENUM_VAL)),
                    value: Box::new(v),
                }))),
            ],
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
                    key: PropName::Ident(Self::str_ident(loc, "key")),
                    value: Box::new(k),
                }))),
                PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                    key: PropName::Ident(Self::str_ident(loc, "value")),
                    value: Box::new(v),
                }))),
            ],
        })
    }

    /// ```ts
    /// ((x) => x.done ? None : Ok({key: x.value[0], value: x.value[1]}))(e)
    /// ```
    fn entryify_iteration_result(loc: Loc, e: Expr) -> Expr {
        let item = Self::access(loc, Expr::Ident(Self::str_ident(loc, "x")), "value");
        let k = Self::index(loc, item.clone(), 0.0);
        let v = Self::index(loc, item, 1.0);
        Self::paren_call(
            loc,
            Expr::Arrow(ArrowExpr {
                span: loc.into(),
                params: vec![Self::str_ident_pat(loc, "x")],
                body: Box::new(BlockStmtOrExpr::Expr(Box::new(Expr::Cond(CondExpr {
                    span: loc.into(),
                    test: Box::new(Self::access(
                        loc,
                        Expr::Ident(Self::str_ident(loc, "x")),
                        "done",
                    )),
                    cons: Box::new(Self::none(loc)),
                    alt: Box::new(Self::ok(loc, Self::entry(loc, k, v))),
                })))),
                is_async: false,
                is_generator: false,
                type_params: None,
                return_type: None,
            }),
            e,
        )
    }

    fn access(loc: Loc, a: Expr, n: &str) -> Expr {
        Expr::Member(MemberExpr {
            span: loc.into(),
            obj: Box::new(Expr::Paren(ParenExpr {
                span: loc.into(),
                expr: Box::new(a),
            })),
            prop: MemberProp::Ident(Self::str_ident(loc, n)),
        })
    }

    fn prototype<const N: usize>(
        &mut self,
        sigma: &Sigma,
        loc: Loc,
        a: &Term,
        m: &str,
        args: [Expr; N],
    ) -> Result<Expr, Error> {
        Ok(Expr::Call(CallExpr {
            span: loc.into(),
            callee: Callee::Expr(Box::new(Self::access(loc, self.expr(sigma, loc, a)?, m))),
            args: args
                .into_iter()
                .map(|e| ExprOrSpread {
                    spread: None,
                    expr: Box::new(e),
                })
                .collect(),
            type_args: None,
        }))
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
            obj: Box::new(Expr::Paren(ParenExpr {
                span: loc.into(),
                expr: Box::new(self.expr(sigma, loc, v)?),
            })),
            prop: MemberProp::Computed(ComputedPropName {
                span: loc.into(),
                expr: Box::new(Expr::Member(MemberExpr {
                    span: loc.into(),
                    obj: Box::new(Expr::Ident(Self::special_ident("Symbol"))),
                    prop: MemberProp::Ident(Self::special_ident(sym)),
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
        Ok(Expr::Call(CallExpr {
            span: loc.into(),
            callee: Callee::Expr(Box::new(self.well_known_symbol(sigma, loc, v, sym)?)),
            args: Default::default(),
            type_args: None,
        }))
    }

    /// ```ts
    /// ((x) => x.done ? None : Ok(x.value))(e)
    /// ```
    fn optionify_iteration_result(loc: Loc, e: Expr) -> Expr {
        Self::paren_call(
            loc,
            Expr::Arrow(ArrowExpr {
                span: loc.into(),
                params: vec![Self::str_ident_pat(loc, "x")],
                body: Box::new(BlockStmtOrExpr::Expr(Box::new(Expr::Cond(CondExpr {
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
                })))),
                is_async: false,
                is_generator: false,
                type_params: None,
                return_type: None,
            }),
            e,
        )
    }

    /// ```ts
    /// ((x) => x === undefined ? None : Ok(x))(e)
    /// ```
    fn optionify(loc: Loc, e: Expr) -> Expr {
        Self::paren_call(
            loc,
            Expr::Arrow(ArrowExpr {
                span: loc.into(),
                params: vec![Self::str_ident_pat(loc, "x")],
                body: Box::new(BlockStmtOrExpr::Expr(Box::new(Expr::Cond(CondExpr {
                    span: loc.into(),
                    test: Box::new(Expr::Bin(BinExpr {
                        span: loc.into(),
                        op: BinaryOp::EqEqEq,
                        left: Box::new(Expr::Ident(Self::str_ident(loc, "x"))),
                        right: Box::new(Self::undefined()),
                    })),
                    cons: Box::new(Self::none(loc)),
                    alt: Box::new(Self::ok(loc, Expr::Ident(Self::str_ident(loc, "x")))),
                })))),
                is_async: false,
                is_generator: false,
                type_params: None,
                return_type: None,
            }),
            e,
        )
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

        match (i, x) {
            (UnnamedImplicit, tm) => {
                let mut ans = tm.clone();
                if let MetaRef(_, v, _) = tm {
                    let v = match &sigma.get(v).unwrap().body {
                        Body::Meta(_, v) => v,
                        _ => unreachable!(),
                    };
                    ans = match v {
                        Some(v) => v.clone(),
                        _ => unreachable!(),
                    };
                }
                match ans {
                    RowSat | RowRefl | ImplementsSat => return self.expr(sigma, loc, f),
                    _ => unreachable!(),
                }
            }
            (UnnamedExplicit, _) => {}
            _ => unreachable!(),
        }

        loop {
            if let App(ff, ii, _) = f {
                if !matches!(ii, UnnamedExplicit) {
                    f = ff;
                    continue;
                }
            }
            break;
        }

        Ok(Expr::Call(CallExpr {
            span: loc.into(),
            callee: Callee::Expr(Box::new(Expr::Paren(ParenExpr {
                span: loc.into(),
                expr: Box::new(self.expr(sigma, loc, f)?),
            }))),
            args: self.untuple_args(sigma, loc, x)?,
            type_args: None,
        }))
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

    fn func(&mut self, sigma: &Sigma, def: &Def<Term>, body: &Term) -> Result<Function, Error> {
        Ok(Function {
            params: Self::type_erased_params(def.loc, &def.tele),
            decorators: Default::default(),
            span: def.loc.into(),
            body: Some(self.block(sigma, def.loc, body, true)?),
            is_generator: false,
            is_async: false,
            type_params: None,
            return_type: None,
        })
    }

    fn type_erased_param_pat(loc: Loc, p: &Param<Term>) -> Vec<Pat> {
        let mut pats = Vec::default();
        let mut tm = &p.typ;
        while let Term::Sigma(ref p, ref b) = **tm {
            pats.push(Self::ident_pat(loc, &p.var));
            tm = b;
        }
        pats
    }

    fn type_erased_param_pats(loc: Loc, tele: &Tele<Term>) -> Vec<Pat> {
        for p in tele {
            if p.var.as_str() == TUPLED {
                return Self::type_erased_param_pat(loc, p);
            }
        }
        unreachable!()
    }

    fn type_erased_params(loc: Loc, tele: &Tele<Term>) -> Vec<JsParam> {
        Self::type_erased_param_pats(loc, tele)
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
                    ret.push(ExprOrSpread {
                        spread: None,
                        expr: Box::new(self.expr(sigma, loc, a)?),
                    });
                    tm = b
                }
                TT => break,
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
        Ok(Self::paren_call(
            loc,
            Expr::Arrow(ArrowExpr {
                span: loc.into(),
                params: v.map_or_else(Default::default, |v| vec![Self::ident_pat(loc, v)]),
                body: Box::new(BlockStmtOrExpr::BlockStmt(self.block(sigma, loc, b, true)?)),
                is_async: false,
                is_generator: false,
                type_params: None,
                return_type: None,
            }),
            self.expr(sigma, loc, a)?,
        ))
    }

    fn enum_case_consequent(
        &mut self,
        sigma: &Sigma,
        loc: Loc,
        v: &Var,
        tm: &Term,
    ) -> Result<Vec<Stmt>, Error> {
        Ok(vec![Stmt::Return(ReturnStmt {
            span: loc.into(),
            arg: Some(Box::new(Self::paren_call(
                loc,
                Expr::Arrow(ArrowExpr {
                    span: loc.into(),
                    params: vec![Self::ident_pat(loc, v)],
                    body: Box::new(BlockStmtOrExpr::BlockStmt(
                        self.block(sigma, loc, tm, true)?,
                    )),
                    is_async: false,
                    is_generator: false,
                    type_params: None,
                    return_type: None,
                }),
                Expr::Ident(Self::str_ident(loc, "__v")),
            ))),
        })])
    }

    fn enum_introspect(loc: Loc, e: &str, v: &str, prop: &str) -> VarDeclarator {
        VarDeclarator {
            span: loc.into(),
            name: Self::str_ident_pat(loc, v),
            init: Some(Box::new(Expr::Member(MemberExpr {
                span: loc.into(),
                obj: Box::new(Expr::Ident(Self::str_ident(loc, e))),
                prop: MemberProp::Ident(Self::str_ident(loc, prop)),
            }))),
            definite: false,
        }
    }

    fn local_decl(
        &mut self,
        sigma: &Sigma,
        loc: Loc,
        kind: VarDeclKind,
        v: &Var,
        tm: &Term,
    ) -> Result<VarDecl, Error> {
        Ok(VarDecl {
            span: loc.into(),
            kind,
            declare: false,
            decls: vec![VarDeclarator {
                span: loc.into(),
                name: Self::ident_pat(loc, v),
                init: Some(Box::new(self.expr(sigma, loc, tm)?)),
                definite: false,
            }],
        })
    }

    fn local_update(&mut self, sigma: &Sigma, loc: Loc, v: &Var, tm: &Term) -> Result<Expr, Error> {
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

    fn unit_stmt(&mut self, sigma: &Sigma, loc: Loc, tm: &Term) -> Result<Stmt, Error> {
        Ok(Stmt::Expr(ExprStmt {
            span: loc.into(),
            expr: Box::new(self.expr(sigma, loc, tm)?),
        }))
    }

    fn iife(loc: Loc, b: BlockStmt) -> Expr {
        Expr::Paren(ParenExpr {
            span: loc.into(),
            expr: Box::new(Expr::Call(CallExpr {
                span: loc.into(),
                callee: Callee::Expr(Box::from(Expr::Paren(ParenExpr {
                    span: loc.into(),
                    expr: Box::new(Expr::Arrow(ArrowExpr {
                        span: loc.into(),
                        params: Default::default(),
                        body: Box::new(BlockStmtOrExpr::BlockStmt(b)),
                        is_async: false,
                        is_generator: false,
                        type_params: None,
                        return_type: None,
                    })),
                }))),
                args: Default::default(),
                type_args: None,
            })),
        })
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
            Local(p, a, b) => (
                Some(VarDeclOrExpr::VarDecl(Box::new(self.local_decl(
                    sigma,
                    loc,
                    VarDeclKind::Const,
                    &p.var,
                    a,
                )?))),
                b,
            ),
            LocalSet(p, a, b) => (
                Some(VarDeclOrExpr::VarDecl(Box::new(self.local_decl(
                    sigma,
                    loc,
                    VarDeclKind::Let,
                    &p.var,
                    a,
                )?))),
                b,
            ),
            LocalUpdate(v, a, b) => (
                Some(VarDeclOrExpr::Expr(Box::new(
                    self.local_update(sigma, loc, v, a)?,
                ))),
                b,
            ),
            UnitLocal(a, b) => (
                Some(VarDeclOrExpr::Expr(Box::new(self.expr(sigma, loc, a)?))),
                b,
            ),
            _ => unreachable!(),
        };

        let (test, body) = match body.as_ref() {
            LocalSet(_, a, b) => (Some(Box::new(self.expr(sigma, loc, a)?)), b),
            _ => unreachable!(),
        };

        let (update, body) = match body.as_ref() {
            LocalUpdate(v, a, b) => (Some(Box::new(self.local_update(sigma, loc, v, a)?)), b),
            UnitLocal(a, b) => (Some(Box::new(self.expr(sigma, loc, a)?)), b),
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

    fn guard_stmt(&mut self, sigma: &Sigma, loc: Loc, p: &Term, b: &Term) -> Result<Stmt, Error> {
        Ok(Stmt::If(IfStmt {
            span: loc.into(),
            test: Box::new(self.expr(sigma, loc, p)?),
            cons: Box::new(Stmt::Block(self.block(sigma, loc, b, false)?)),
            alt: None,
        }))
    }

    fn block(
        &mut self,
        sigma: &Sigma,
        loc: Loc,
        body: &Term,
        returns: bool,
    ) -> Result<BlockStmt, Error> {
        fn strip_untupled_lets(mut tm: &Term) -> Term {
            use Term::*;
            loop {
                match tm {
                    TupleLocal(_, q, _, b) if q.var.as_str().starts_with(UNTUPLED_RHS_PREFIX) => {
                        tm = b
                    }
                    _ => break,
                }
            }
            tm.clone()
        }

        use Term::*;

        let mut tm = &strip_untupled_lets(body);
        let mut stmts = Vec::default();
        let span = loc.into();

        loop {
            match tm {
                Local(p, a, b) => {
                    stmts.push(Stmt::Decl(Decl::Var(Box::new(self.local_decl(
                        sigma,
                        loc,
                        VarDeclKind::Const,
                        &p.var,
                        a,
                    )?))));
                    tm = b
                }
                LocalSet(p, a, b) => {
                    stmts.push(Stmt::Decl(Decl::Var(Box::new(self.local_decl(
                        sigma,
                        loc,
                        VarDeclKind::Let,
                        &p.var,
                        a,
                    )?))));
                    tm = b
                }
                LocalUpdate(v, a, b) => {
                    stmts.push(Stmt::Expr(ExprStmt {
                        span,
                        expr: Box::new(self.local_update(sigma, loc, v, a)?),
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
                Guard(p, b, r) => {
                    stmts.push(self.guard_stmt(sigma, loc, p, b)?);
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
                TupleLocal(_, _, _, _) => unreachable!(),
                UnitLocal(a, b) => {
                    stmts.push(self.unit_stmt(sigma, loc, a)?);
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
        Ok(BlockStmt { span, stmts })
    }

    fn expr(&mut self, sigma: &Sigma, loc: Loc, tm: &Term) -> Result<Expr, Error> {
        use Term::*;
        Ok(match tm {
            MetaRef(k, r, sp) => match Self::solution(sigma, r) {
                None => return Err(UnsolvedMeta(MetaRef(k.clone(), r.clone(), sp.clone()), loc)),
                Some(_) => unreachable!(),
            },

            Local(p, a, b) | LocalSet(p, a, b) => {
                self.lambda_encoded_let(sigma, loc, Some(&p.var), a, b)?
            }
            UnitLocal(a, b) => self.lambda_encoded_let(sigma, loc, None, a, b)?,

            Ref(r) | Undef(r) => Expr::Ident(Self::ident(loc, r)),
            Extern(r) => Expr::Member(MemberExpr {
                span: loc.into(),
                obj: Box::new(Expr::Ident(Self::lib())),
                prop: MemberProp::Ident(Self::ident(loc, r)),
            }),
            Qualified(m, r) => Expr::Member(MemberExpr {
                span: loc.into(),
                obj: Box::new(Expr::Ident(Self::str_ident(
                    loc,
                    self.to_qualifier(m).as_str(),
                ))),
                prop: MemberProp::Ident(Self::ident(loc, r)),
            }),
            Lam(p, b) => match p.info {
                Explicit => Expr::Arrow(ArrowExpr {
                    span: loc.into(),
                    params: Self::type_erased_param_pat(loc, p),
                    body: Box::new(BlockStmtOrExpr::BlockStmt(self.block(sigma, loc, b, true)?)),
                    is_async: false,
                    is_generator: false,
                    type_params: None,
                    return_type: None,
                }),
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
            Str(s) => Expr::Lit(Lit::Str(Self::js_raw_str(loc, s))),
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
            Big(v) => Expr::Lit(Lit::BigInt(JsBigInt {
                span: loc.into(),
                value: Box::new(BigIntValue::from_str(v).unwrap()),
                raw: None,
            })),
            ArrIterNext(it) => {
                Self::optionify_iteration_result(loc, self.prototype(sigma, loc, it, "next", [])?)
            }
            Arr(xs) => {
                let mut elems = Vec::default();
                for x in xs {
                    elems.push(Some(ExprOrSpread {
                        spread: None,
                        expr: Box::new(self.expr(sigma, loc, x)?),
                    }));
                }
                Expr::Array(ArrayLit {
                    span: loc.into(),
                    elems,
                })
            }
            ArrLength(a) => Self::access(loc, self.expr(sigma, loc, a)?, "length"),
            ArrPush(a, v) => {
                let v = self.expr(sigma, loc, v)?;
                self.prototype(sigma, loc, a, "push", [v])?
            }
            ArrForeach(a, f) => {
                let f = self.expr(sigma, loc, f)?;
                self.prototype(sigma, loc, a, "forEach", [f])?
            }
            ArrAt(a, i) => {
                let i = self.expr(sigma, loc, i)?;
                let ret = self.prototype(sigma, loc, a, "at", [i])?;
                Self::optionify(loc, ret)
            }
            // void (a[i] = v)
            ArrInsert(a, i, v) => Expr::Unary(UnaryExpr {
                span: loc.into(),
                op: UnaryOp::Void,
                arg: Box::new(Expr::Paren(ParenExpr {
                    span: loc.into(),
                    expr: Box::new(Expr::Assign(AssignExpr {
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
                    })),
                })),
            }),
            ArrIter(a) => self.well_known_symbol_call(sigma, loc, a, "iterator")?,
            MapIterNext(it) => {
                Self::entryify_iteration_result(loc, self.prototype(sigma, loc, it, "next", [])?)
            }
            Kv(xs) => {
                let mut elems = Vec::default();
                for (k, v) in xs {
                    elems.push(Some(ExprOrSpread {
                        spread: None,
                        expr: Box::new(Expr::Array(ArrayLit {
                            span: loc.into(),
                            elems: vec![
                                Some(ExprOrSpread {
                                    spread: None,
                                    expr: Box::new(self.expr(sigma, loc, k)?),
                                }),
                                Some(ExprOrSpread {
                                    spread: None,
                                    expr: Box::new(self.expr(sigma, loc, v)?),
                                }),
                            ],
                        })),
                    }));
                }
                Expr::New(NewExpr {
                    span: loc.into(),
                    callee: Box::new(Expr::Ident(Self::special_ident("Map"))),
                    args: Some(vec![ExprOrSpread {
                        spread: None,
                        expr: Box::new(Expr::Array(ArrayLit {
                            span: loc.into(),
                            elems,
                        })),
                    }]),
                    type_args: None,
                })
            }
            MapHas(m, k) => {
                let k = self.expr(sigma, loc, k)?;
                self.prototype(sigma, loc, m, "has", [k])?
            }
            MapGet(m, k) => {
                let k = self.expr(sigma, loc, k)?;
                self.prototype(sigma, loc, m, "get", [k])?
            }
            MapSet(m, k, v) => {
                let k = self.expr(sigma, loc, k)?;
                let v = self.expr(sigma, loc, v)?;
                self.prototype(sigma, loc, m, "set", [k, v])?
            }
            MapDelete(m, k) => {
                let k = self.expr(sigma, loc, k)?;
                self.prototype(sigma, loc, m, "delete", [k])?
            }
            MapIter(m) => self.well_known_symbol_call(sigma, loc, m, "iterator")?,
            MapClear(m) => self.prototype(sigma, loc, m, "clear", [])?,
            Obj(f) => match f.as_ref() {
                Fields(fields) => {
                    let mut props = Vec::default();
                    for (name, tm) in fields {
                        props.push(PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                            key: PropName::Ident(Self::str_ident(loc, name.as_str())),
                            value: Box::new(self.expr(sigma, loc, &tm.clone())?),
                        }))));
                    }
                    Expr::Paren(ParenExpr {
                        span: loc.into(),
                        expr: Box::new(Expr::Object(ObjectLit {
                            span: loc.into(),
                            props,
                        })),
                    })
                }
                _ => unreachable!(),
            },
            Concat(a, b) => Expr::Object(ObjectLit {
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
                        Some(fields) => match fields {
                            Fields(fields) => fields,
                            _ => unreachable!(),
                        },
                    },
                    _ => unreachable!(),
                };
                let mut props = Vec::default();
                for name in fields.keys() {
                    props.push(PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                        key: PropName::Ident(Self::str_ident(loc, name)),
                        value: Box::new(Expr::Member(MemberExpr {
                            span: loc.into(),
                            obj: Box::new(Expr::Paren(ParenExpr {
                                span: loc.into(),
                                expr: Box::new(Expr::Ident(x.clone())),
                            })),
                            prop: MemberProp::Ident(Self::str_ident(loc, name)),
                        })),
                    }))))
                }

                let body = BlockStmtOrExpr::Expr(Box::new(Expr::Paren(ParenExpr {
                    span: loc.into(),
                    expr: Box::new(Expr::Object(ObjectLit {
                        span: loc.into(),
                        props,
                    })),
                })));

                Self::paren_call(
                    loc,
                    Expr::Arrow(ArrowExpr {
                        span: loc.into(),
                        params: vec![Pat::Ident(BindingIdent {
                            id: x,
                            type_ann: None,
                        })],
                        body: Box::new(body),
                        is_async: false,
                        is_generator: false,
                        type_params: None,
                        return_type: None,
                    }),
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
                //      const __t = x.__enumT, __v = x.__enumV;
                //      switch (__t) {
                //      case "Ok": return ((a) => { return a + 1; })(__v)
                //      case "None: return ((_) => { return undefined; })(__v)
                //      default: return ((d) => { return d; })(__v)
                //      }
                // })(x)

                let mut cases = Vec::default();
                for (x, (v, tm)) in cs {
                    cases.push(SwitchCase {
                        span: loc.into(),
                        test: Some(Box::new(Expr::Lit(Lit::Str(Self::js_str(loc, x))))),
                        cons: self.enum_case_consequent(sigma, loc, v, tm)?,
                    });
                }
                if let Some((v, tm)) = d {
                    cases.push(SwitchCase {
                        span: loc.into(),
                        test: None,
                        cons: self.enum_case_consequent(sigma, loc, v, tm)?,
                    })
                }
                let matcher = Stmt::Switch(SwitchStmt {
                    span: loc.into(),
                    discriminant: Box::new(Expr::Ident(Self::str_ident(loc, "__t"))),
                    cases,
                });

                Self::paren_call(
                    loc,
                    Expr::Arrow(ArrowExpr {
                        span: loc.into(),
                        params: vec![Self::str_ident_pat(loc, "x")],
                        body: Box::new(BlockStmtOrExpr::BlockStmt(BlockStmt {
                            span: loc.into(),
                            stmts: vec![
                                Stmt::Decl(Decl::Var(Box::new(VarDecl {
                                    span: loc.into(),
                                    kind: VarDeclKind::Const,
                                    declare: false,
                                    decls: vec![
                                        Self::enum_introspect(loc, "x", "__t", JS_ENUM_TAG),
                                        Self::enum_introspect(loc, "x", "__v", JS_ENUM_VAL),
                                    ],
                                }))),
                                matcher,
                            ],
                        })),
                        is_async: false,
                        is_generator: false,
                        type_params: None,
                        return_type: None,
                    }),
                    self.expr(sigma, loc, a)?,
                )
            }
            Unionify(a) => Expr::Member(MemberExpr {
                span: loc.into(),
                obj: Box::new(self.expr(sigma, loc, a)?),
                prop: MemberProp::Ident(Self::special_ident(JS_ENUM_VAL)),
            }),
            ErrorThrow(a) => Self::iife(
                loc,
                BlockStmt {
                    span: loc.into(),
                    stmts: vec![Stmt::Throw(ThrowStmt {
                        span: loc.into(),
                        arg: Box::new(Self::paren_call(
                            loc,
                            Expr::Ident(Self::special_ident("Error")),
                            self.expr(sigma, loc, a)?,
                        )),
                    })],
                },
            ),
            ConsoleLog(m) => Expr::Call(CallExpr {
                span: Default::default(),
                callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                    span: loc.into(),
                    obj: Box::new(Expr::Ident(Self::special_ident("console"))),
                    prop: MemberProp::Ident(Self::special_ident("log")),
                }))),
                args: vec![ExprOrSpread {
                    spread: None,
                    expr: Box::new(self.expr(sigma, loc, m)?),
                }],
                type_args: None,
            }),

            Find(_, _, f) => return Err(NonErasable(Ref(f.clone()), loc)),

            _ => unreachable!(),
        })
    }

    fn imports(&self, imports: Vec<Import>) -> Result<Vec<ModuleItem>, Error> {
        use ImportedDefs::*;
        let mut items = Vec::default();
        for i in imports {
            let mut specifiers = Vec::default();
            match i.defs {
                Unqualified(defs) => {
                    for (loc, d) in defs {
                        specifiers.push(ImportSpecifier::Named(ImportNamedSpecifier {
                            span: loc.into(),
                            local: Self::str_ident(loc, d.as_str()),
                            imported: None,
                            is_type_only: false,
                        }))
                    }
                }
                Qualified => {
                    specifiers.push(ImportSpecifier::Namespace(ImportStarAsSpecifier {
                        span: i.loc.into(),
                        local: Self::str_ident(i.loc, self.to_qualifier(&i.module).as_str()),
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

    fn includes(&mut self, includes: &[PathBuf]) -> Result<Vec<ModuleItem>, Error> {
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
                    sym: ns.into(),
                    optional: false,
                })),
            }));
        }
        if !props.is_empty() {
            items.push(ModuleItem::Stmt(Stmt::Decl(Decl::Var(Box::new(VarDecl {
                span: DUMMY_SP,
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

    fn decls(&mut self, sigma: &Sigma, defs: Vec<Def<Term>>) -> Result<Vec<ModuleItem>, Error> {
        use Body::*;
        let mut items = Vec::default();
        for def in defs {
            debug!(target: "codegen", "generating definition: {def}");
            match match &def.body {
                Fn(f) => self.func_decl(&mut items, sigma, &def, f),
                Postulate => self.postulate_decl(&mut items, &def),
                Const(_, f) => self.const_decl(&mut items, sigma, &def, f),
                Method { f, .. } => self.func_decl(&mut items, sigma, &def, f),
                Undefined => unreachable!(),
                _ => continue,
            } {
                Ok(_) | Err(NonErasable(_, _)) => continue,
                Err(e) => return Err(e),
            };
        }
        Ok(items)
    }

    fn try_export_decl(def: &Def<Term>, decl: Decl) -> ModuleItem {
        if def.is_private() {
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
        if def.is_private() {
            return Ok(());
        }
        items.push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
            span: def.loc.into(),
            decl: Decl::Var(Box::new(VarDecl {
                span: def.loc.into(),
                kind: VarDeclKind::Const,
                declare: false,
                decls: vec![VarDeclarator {
                    span: def.loc.into(),
                    name: Self::ident_pat(def.loc, &def.name),
                    init: Some(Box::new(Expr::Member(MemberExpr {
                        span: def.loc.into(),
                        obj: Box::new(Expr::Ident(Self::special_ident(JS_LIB))),
                        prop: MemberProp::Ident(Self::ident(def.loc, &def.name)),
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
        items.push(match def.name.as_str() {
            UNBOUND => ModuleItem::Stmt(Stmt::Expr(ExprStmt {
                span: def.loc.into(),
                expr: Box::new(Self::iife(def.loc, self.block(sigma, def.loc, f, false)?)),
            })),
            _ => Self::try_export_decl(
                def,
                Decl::Var(Box::new(VarDecl {
                    span: def.loc.into(),
                    kind: VarDeclKind::Const,
                    declare: false,
                    decls: vec![VarDeclarator {
                        span: def.loc.into(),
                        name: Self::ident_pat(def.loc, &def.name),
                        init: Some(Box::new(Self::iife(
                            def.loc,
                            self.block(sigma, def.loc, f, true)?,
                        ))),
                        definite: false,
                    }],
                })),
            ),
        });
        Ok(())
    }
}

pub const OUT_FILE: &str = "index.mjs";
pub const QUALIFIER_SEP: &str = "$";

impl Target for Ecma {
    fn filename(&self) -> &'static str {
        OUT_FILE
    }

    fn to_qualifier(&self, module: &ModuleID) -> String {
        use ImportedPkg::*;
        let mut ret = match &module.pkg {
            Std(p) => vec![p.clone()],
            Vendor(o, p) => vec![o.strip_prefix('@').unwrap().to_string(), p.clone()],
            Root => vec![QUALIFIER_SEP.to_string()],
        };
        for m in &module.modules {
            ret.push(m.to_str().unwrap().to_string());
        }
        ret.join(QUALIFIER_SEP)
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
        includes: &[PathBuf],
        file: ModuleFile,
    ) -> Result<(), Error> {
        let mut body = self.imports(file.imports)?;
        body.extend(self.includes(includes)?);
        body.extend(self.decls(sigma, file.defs)?);

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
        .map_err(|e| Error::IO(file.file, e))?;

        Ok(())
    }
}
