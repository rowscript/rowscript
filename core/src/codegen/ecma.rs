use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::str::FromStr;

use num_bigint::BigInt as BigIntValue;
use swc_common::{BytePos, SourceMap, Span, DUMMY_SP};
use swc_ecma_ast::{
    ArrowExpr, AssignExpr, AssignOp, BigInt as JsBigInt, BinExpr, BinaryOp, BindingIdent,
    BlockStmt, BlockStmtOrExpr, Bool, CallExpr, Callee, ComputedPropName, CondExpr, Decl,
    ExportDecl, Expr, ExprOrSpread, ExprStmt, FnDecl, Function, Ident, ImportDecl,
    ImportNamedSpecifier, ImportSpecifier, ImportStarAsSpecifier, KeyValueProp, Lit, MemberExpr,
    MemberProp, Module, ModuleDecl, ModuleItem, Number as JsNumber, ObjectLit, Param as JsParam,
    ParenExpr, Pat, PatOrExpr, Prop, PropName, PropOrSpread, ReturnStmt, SpreadElement, Stmt,
    Str as JsStr, VarDecl, VarDeclKind, VarDeclarator,
};
use swc_ecma_codegen::text_writer::JsWriter;
use swc_ecma_codegen::Emitter;

use crate::codegen::{mangle_hkt, Target};
use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Body, Def, Sigma};
use crate::theory::conc::data::ArgInfo::UnnamedExplicit;
use crate::theory::conc::load::{Import, ImportedDefs, ImportedPkg, ModuleID};
use crate::theory::ParamInfo::Explicit;
use crate::theory::{Loc, Param, Tele, Var, THIS, TUPLED, UNTUPLED_RHS};
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
const JS_ESCAPED_THIS: &str = "_this";
const JS_ENUM_TAG: &str = "__enumT";
const JS_ENUM_VAL: &str = "__enumV";
const JS_VTBL: &str = "__vtbl";

type Vtbl = HashMap<String, Vec<(String, Var)>>;

#[derive(Default)]
pub struct Ecma {
    vtbl: Vtbl,
}

impl Ecma {
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

    fn undefined() -> Ident {
        Self::special_ident("undefined")
    }

    fn lib() -> Ident {
        Self::special_ident(JS_LIB)
    }

    fn global_this() -> Ident {
        Self::special_ident("globalThis")
    }

    fn global_vtbl() -> Expr {
        Expr::Member(MemberExpr {
            span: DUMMY_SP,
            obj: Box::new(Expr::Ident(Self::global_this())),
            prop: MemberProp::Ident(Self::special_ident(JS_VTBL)),
        })
    }

    fn access(&mut self, sigma: &Sigma, loc: Loc, a: &Term, n: &str) -> Result<Expr, Error> {
        Ok(Expr::Member(MemberExpr {
            span: loc.into(),
            obj: Box::new(Expr::Paren(ParenExpr {
                span: loc.into(),
                expr: Box::new(self.expr(sigma, loc, a)?),
            })),
            prop: MemberProp::Ident(Self::str_ident(loc, n)),
        }))
    }

    fn func(&mut self, sigma: &Sigma, def: &Def<Term>, body: &Term) -> Result<Function, Error> {
        Ok(Function {
            params: Self::type_erased_params(def.loc, &def.tele),
            decorators: Default::default(),
            span: def.loc.into(),
            body: Some(self.block(sigma, def.loc, body)?),
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
        f: &Term,
        mut tm: &Term,
    ) -> Result<Vec<ExprOrSpread>, Error> {
        use Term::*;

        let mut ret = Vec::default();
        loop {
            match tm {
                Tuple(a, b) => {
                    ret.push(ExprOrSpread {
                        spread: None,
                        expr: Box::new(match (f, &**a) {
                            (Extern(_), Variant(fields)) => match &**fields {
                                Fields(fm) => self.expr(sigma, loc, fm.iter().next().unwrap().1)?,
                                _ => self.untag_variant(sigma, loc, a)?,
                            },
                            (Extern(_), b) => self.untag_variant(sigma, loc, b)?,
                            _ => self.expr(sigma, loc, a)?,
                        }),
                    });
                    tm = b
                }
                TT => break,
                _ => unreachable!(),
            }
        }
        Ok(ret)
    }

    fn untag_variant(&mut self, sigma: &Sigma, loc: Loc, tm: &Term) -> Result<Expr, Error> {
        Ok(Expr::Member(MemberExpr {
            span: loc.into(),
            obj: Box::new(self.expr(sigma, loc, tm)?),
            prop: MemberProp::Ident(Self::special_ident(JS_ENUM_VAL)),
        }))
    }

    fn lambda_encoded_let(
        &mut self,
        sigma: &Sigma,
        loc: Loc,
        v: Option<&Var>,
        a: &Term,
        b: &Term,
    ) -> Result<Expr, Error> {
        Ok(Expr::Call(CallExpr {
            span: loc.into(),
            callee: Callee::Expr(Box::new(Expr::Paren(ParenExpr {
                span: loc.into(),
                expr: Box::new(Expr::Arrow(ArrowExpr {
                    span: loc.into(),
                    params: v.map_or_else(Default::default, |v| vec![Self::ident_pat(loc, v)]),
                    body: Box::new(BlockStmtOrExpr::Expr(Box::new(self.expr(sigma, loc, b)?))),
                    is_async: false,
                    is_generator: false,
                    type_params: None,
                    return_type: None,
                })),
            }))),
            args: vec![ExprOrSpread {
                spread: None,
                expr: Box::new(self.expr(sigma, loc, a)?),
            }],
            type_args: None,
        }))
    }

    fn const_decl_stmt(
        &mut self,
        sigma: &Sigma,
        loc: Loc,
        v: &Var,
        tm: &Term,
    ) -> Result<Stmt, Error> {
        Ok(Stmt::Decl(Decl::Var(Box::new(VarDecl {
            span: loc.into(),
            kind: VarDeclKind::Const,
            declare: false,
            decls: vec![VarDeclarator {
                span: loc.into(),
                name: Self::ident_pat(loc, v),
                init: Some(Box::new(self.expr(sigma, loc, tm)?)),
                definite: false,
            }],
        }))))
    }

    fn block(&mut self, sigma: &Sigma, loc: Loc, body: &Term) -> Result<BlockStmt, Error> {
        fn strip_untupled_lets(mut tm: &Term) -> Term {
            use Term::*;
            loop {
                match tm {
                    TupleLet(_, q, _, b) if q.var.as_str().starts_with(UNTUPLED_RHS) => tm = b,
                    _ => break,
                }
            }
            tm.clone()
        }

        use Term::*;

        let mut tm = &strip_untupled_lets(body);
        let mut stmts = Vec::default();

        loop {
            match tm {
                Let(p, a, b) => {
                    stmts.push(self.const_decl_stmt(sigma, loc, &p.var, a)?);
                    tm = b
                }
                TupleLet(_, _, _, _) => unreachable!(),
                UnitLet(a, b) => {
                    stmts.push(self.const_decl_stmt(sigma, loc, &Var::unbound(), a)?);
                    tm = b
                }
                _ => {
                    stmts.push(Stmt::Return(ReturnStmt {
                        span: loc.into(),
                        arg: Some(Box::new(self.expr(sigma, loc, tm)?)),
                    }));
                    break;
                }
            }
        }
        Ok(BlockStmt {
            span: loc.into(),
            stmts,
        })
    }

    fn expr(&mut self, sigma: &Sigma, loc: Loc, tm: &Term) -> Result<Expr, Error> {
        use Body::*;
        use Term::*;
        Ok(match tm {
            MetaRef(k, r, sp) => match &sigma.get(r).unwrap().body {
                Meta(_, tm) => match tm {
                    None => {
                        return Err(UnsolvedMeta(MetaRef(k.clone(), r.clone(), sp.clone()), loc))
                    }
                    Some(_) => unreachable!(),
                },
                _ => unreachable!(),
            },

            Let(p, a, b) => self.lambda_encoded_let(sigma, loc, Some(&p.var), a, b)?,
            UnitLet(a, b) => self.lambda_encoded_let(sigma, loc, None, a, b)?,

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
                    body: Box::new(BlockStmtOrExpr::BlockStmt(self.block(sigma, loc, b)?)),
                    is_async: false,
                    is_generator: false,
                    type_params: None,
                    return_type: None,
                }),
                _ => self.expr(sigma, loc, b)?,
            },

            App(f, i, x) => match i {
                UnnamedExplicit => Expr::Call(CallExpr {
                    span: loc.into(),
                    callee: Callee::Expr(Box::new(self.expr(sigma, loc, f)?)),
                    args: self.untuple_args(sigma, loc, f, x)?,
                    type_args: None,
                }),
                _ => self.expr(sigma, loc, f)?,
            },
            TT => Expr::Ident(Self::undefined()),
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
            Str(s) => Expr::Lit(Lit::Str(JsStr {
                span: loc.into(),
                value: s.as_str().into(),
                raw: None,
            })),
            Num(v) => Expr::Lit(Lit::Num(JsNumber {
                span: loc.into(),
                value: *v,
                raw: None,
            })),
            NumAdd(a, b) => Expr::Bin(BinExpr {
                span: loc.into(),
                op: BinaryOp::Add,
                left: Box::new(self.expr(sigma, loc, a)?),
                right: Box::new(self.expr(sigma, loc, b)?),
            }),
            Big(v) => Expr::Lit(Lit::BigInt(JsBigInt {
                span: loc.into(),
                value: Box::new(BigIntValue::from_str(v).unwrap()),
                raw: None,
            })),
            Obj(f) => match &**f {
                Fields(fields) => {
                    let mut props = Vec::default();
                    for (name, tm) in fields {
                        props.push(PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                            key: PropName::Ident(Self::str_ident(loc, name.as_str())),
                            value: Box::new(self.expr(sigma, loc, &tm.clone())?),
                        }))));
                    }
                    Expr::Object(ObjectLit {
                        span: loc.into(),
                        props,
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
            Access(a, n) => self.access(sigma, loc, a, n)?,
            Downcast(a, f) => match &**f {
                Fields(fields) => {
                    let mut props = Vec::default();
                    for name in fields.keys() {
                        props.push(PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                            key: PropName::Ident(Self::str_ident(loc, name)),
                            value: Box::new(self.access(sigma, loc, a, name)?),
                        }))))
                    }
                    Expr::Object(ObjectLit {
                        span: loc.into(),
                        props,
                    })
                }
                _ => unreachable!(),
            },
            Variant(f) => match &**f {
                Fields(fields) => {
                    let (name, tm) = fields.iter().next().unwrap();
                    Expr::Object(ObjectLit {
                        span: loc.into(),
                        props: vec![
                            PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                                key: PropName::Ident(Self::str_ident(loc, JS_ENUM_TAG)),
                                value: Box::new(Expr::Lit(Lit::Str(JsStr {
                                    span: loc.into(),
                                    value: name.as_str().into(),
                                    raw: None,
                                }))),
                            }))),
                            PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                                key: PropName::Ident(Self::str_ident(loc, JS_ENUM_VAL)),
                                value: Box::new(self.expr(sigma, loc, &tm.clone())?),
                            }))),
                        ],
                    })
                }
                _ => unreachable!(),
            },
            Upcast(a, _) => self.expr(sigma, loc, a)?,
            Switch(a, cs) => {
                // ({Some: a => a + 1, None: () => undefined}[a.__rowsT])(a.__rowsV)
                let mut props = Vec::default();
                for (n, (v, tm)) in cs {
                    props.push(PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                        key: PropName::Ident(Self::str_ident(loc, n.as_str())),
                        value: Box::new(Expr::Arrow(ArrowExpr {
                            span: loc.into(),
                            params: vec![Self::ident_pat(loc, v)],
                            body: Box::new(BlockStmtOrExpr::BlockStmt(self.block(
                                sigma,
                                loc,
                                &tm.clone(),
                            )?)),
                            is_async: false,
                            is_generator: false,
                            type_params: None,
                            return_type: None,
                        })),
                    }))))
                }
                let branches = Box::new(Expr::Object(ObjectLit {
                    span: loc.into(),
                    props,
                }));
                let obj = Box::new(self.expr(sigma, loc, a)?);
                let tag = Box::new(Expr::Member(MemberExpr {
                    span: loc.into(),
                    obj: obj.clone(),
                    prop: MemberProp::Ident(Self::str_ident(loc, JS_ENUM_TAG)),
                }));
                let arg = Box::new(Expr::Member(MemberExpr {
                    span: loc.into(),
                    obj,
                    prop: MemberProp::Ident(Self::str_ident(loc, JS_ENUM_VAL)),
                }));
                let branch = Box::new(Expr::Member(MemberExpr {
                    span: loc.into(),
                    obj: branches,
                    prop: MemberProp::Computed(ComputedPropName {
                        span: loc.into(),
                        expr: tag,
                    }),
                }));
                Expr::Call(CallExpr {
                    span: loc.into(),
                    callee: Callee::Expr(Box::new(Expr::Paren(ParenExpr {
                        span: loc.into(),
                        expr: branch,
                    }))),
                    args: vec![ExprOrSpread {
                        spread: None,
                        expr: arg,
                    }],
                    type_args: None,
                })
            }
            Vp(r, ts) => Expr::Lit(Lit::Str(JsStr {
                span: loc.into(),
                value: mangle_hkt(loc, r, ts)?.as_str().into(),
                raw: None,
            })),
            Lookup(a) => {
                match &**a {
                    Vp(r, ts) if !ts.is_empty() => {
                        let meths = self.vtbl.get(r).unwrap().clone();
                        self.vtbl.insert(mangle_hkt(loc, r, ts)?, meths);
                    }
                    _ => {}
                }
                Expr::Member(MemberExpr {
                    span: loc.into(),
                    obj: Box::new(Self::global_vtbl()),
                    prop: MemberProp::Computed(ComputedPropName {
                        span: loc.into(),
                        expr: Box::new(self.expr(sigma, loc, a)?),
                    }),
                })
            }
            Find(_, _, f) => return Err(NonErasable(Ref(f.clone()), loc)),

            _ => unreachable!(),
        })
    }

    fn imports(&self, items: &mut Vec<ModuleItem>, imports: Vec<Import>) -> Result<(), Error> {
        use ImportedDefs::*;
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
                src: Box::new(JsStr {
                    span: DUMMY_SP,
                    value: i
                        .module
                        .to_relative_path()
                        .join(self.filename())
                        .to_string_lossy()
                        .into(),
                    raw: None,
                }),
                type_only: false,
                asserts: None,
            })))
        }
        Ok(())
    }

    fn includes(&mut self, items: &mut Vec<ModuleItem>, includes: &[PathBuf]) -> Result<(), Error> {
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
                src: Box::new(JsStr {
                    span: DUMMY_SP,
                    value: src.to_string_lossy().into(),
                    raw: None,
                }),
                type_only: false,
                asserts: None,
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
        Ok(())
    }

    fn decls(
        &mut self,
        items: &mut Vec<ModuleItem>,
        sigma: &Sigma,
        defs: Vec<Def<Term>>,
    ) -> Result<(), Error> {
        use Body::*;
        for def in defs {
            match match &def.body {
                Fn(f) => self.func_decl(items, sigma, &def, f),
                Class(body) => self.class_decls(items, sigma, &def.name, &body.ctor, &body.methods),
                Postulate => self.postulate_decl(items, &def),
                Undefined => unreachable!(),
                _ => continue,
            } {
                Ok(_) | Err(NonErasable(_, _)) => continue,
                Err(e) => return Err(e),
            };
        }
        Ok(())
    }

    fn func_decl(
        &mut self,
        items: &mut Vec<ModuleItem>,
        sigma: &Sigma,
        def: &Def<Term>,
        body: &Term,
    ) -> Result<(), Error> {
        let f = Decl::Fn(FnDecl {
            ident: Self::ident(def.loc, &def.name),
            declare: false,
            function: Box::new(self.func(sigma, def, body)?),
        });
        items.push(if def.is_private() {
            ModuleItem::Stmt(Stmt::Decl(f))
        } else {
            ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
                span: def.loc.into(),
                decl: f,
            }))
        });
        Ok(())
    }

    fn class_decls(
        &mut self,
        items: &mut Vec<ModuleItem>,
        sigma: &Sigma,
        name: &Var,
        ctor: &Var,
        meths: &Vec<(String, Var)>,
    ) -> Result<(), Error> {
        use Body::*;

        for (_, m) in meths {
            let meth_def = sigma.get(m).unwrap();
            self.func_decl(
                items,
                sigma,
                meth_def,
                match &meth_def.body {
                    Method(f) => f,
                    _ => unreachable!(),
                },
            )?;
        }
        self.vtbl.insert(name.to_string(), meths.clone());

        let ctor_def = sigma.get(ctor).unwrap();
        self.func_decl(
            items,
            sigma,
            ctor_def,
            match &ctor_def.body {
                Ctor(f) => f,
                _ => unreachable!(),
            },
        )?;

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

    fn vtbl_decl(&self, items: &mut Vec<ModuleItem>) -> Result<(), Error> {
        let mut props = Vec::default();
        for (cls, meths) in &self.vtbl {
            let mut meth_props = Vec::default();
            for (name, m) in meths {
                meth_props.push(PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                    key: PropName::Ident(Self::special_ident(name.as_str())),
                    value: Box::new(Expr::Ident(Self::special_ident(m.as_str()))),
                }))))
            }
            props.push(PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                key: PropName::Str(JsStr {
                    span: DUMMY_SP,
                    value: cls.as_str().into(),
                    raw: None,
                }),
                value: Box::new(Expr::Object(ObjectLit {
                    span: DUMMY_SP,
                    props: meth_props,
                })),
            }))))
        }
        items.push(ModuleItem::Stmt(Stmt::Expr(ExprStmt {
            span: DUMMY_SP,
            expr: Box::new(Expr::Assign(AssignExpr {
                span: DUMMY_SP,
                op: AssignOp::Assign,
                left: PatOrExpr::Expr(Box::new(Self::global_vtbl())),
                right: Box::new(Expr::Object(ObjectLit {
                    span: DUMMY_SP,
                    props: vec![
                        PropOrSpread::Spread(SpreadElement {
                            dot3_token: DUMMY_SP,
                            expr: Box::new(Self::global_vtbl()),
                        }),
                        PropOrSpread::Spread(SpreadElement {
                            dot3_token: DUMMY_SP,
                            expr: Box::new(Expr::Object(ObjectLit {
                                span: DUMMY_SP,
                                props,
                            })),
                        }),
                    ],
                })),
            })),
        })));
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
        let mut body = Vec::default();

        self.vtbl.clear();
        self.imports(&mut body, file.imports)?;
        self.includes(&mut body, includes)?;
        self.decls(&mut body, sigma, file.defs)?;
        self.vtbl_decl(&mut body)?;

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
        .emit_module(&m)?;

        Ok(())
    }
}
