use std::rc::Rc;
use std::str::FromStr;

use num_bigint::BigInt as BigIntValue;
use swc_atoms::js_word;
use swc_common::{BytePos, SourceMap, Span, DUMMY_SP};
use swc_ecma_ast::{
    ArrowExpr, BigInt as JsBigInt, BindingIdent, BlockStmt, BlockStmtOrExpr, Bool, CallExpr,
    Callee, ComputedPropName, CondExpr, Decl, Expr, ExprOrSpread, FnDecl, Function, Ident,
    KeyValueProp, Lit, MemberExpr, MemberProp, Module, ModuleItem, Number as JsNumber, ObjectLit,
    Param as JsParam, ParenExpr, Pat, Prop, PropName, PropOrSpread, ReturnStmt, SpreadElement,
    Stmt, Str as JsStr, VarDecl, VarDeclKind, VarDeclarator,
};
use swc_ecma_codegen::text_writer::JsWriter;
use swc_ecma_codegen::Emitter;

use crate::codegen::Target;
use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Body, Def, Sigma};
use crate::theory::conc::data::ArgInfo::UnnamedExplicit;
use crate::theory::ParamInfo::Explicit;
use crate::theory::{Loc, Param, Tele, Var, THIS, TUPLED, UNTUPLED_RHS};
use crate::Error;
use crate::Error::{NonErasable, UnsolvedMeta};

impl Into<Span> for Loc {
    fn into(self) -> Span {
        Span {
            lo: BytePos(self.start as u32),
            hi: BytePos(self.end as u32),
            ctxt: Default::default(),
        }
    }
}

const JS_ESCAPED_THIS: &str = "_this";
const JS_ENUM_TAG: &str = "__enumT";
const JS_ENUM_VAL: &str = "__enumV";

#[derive(Default)]
pub struct Ecma;

impl Ecma {
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

    fn undefined() -> Expr {
        Expr::Ident(Ident {
            span: DUMMY_SP,
            sym: js_word!("undefined"),
            optional: false,
        })
    }

    fn access(loc: Loc, a: &Box<Term>, n: &String) -> Result<Box<Expr>, Error> {
        Ok(Box::new(Expr::Member(MemberExpr {
            span: loc.into(),
            obj: Box::new(Expr::Paren(ParenExpr {
                span: loc.into(),
                expr: Self::expr(loc, a)?,
            })),
            prop: MemberProp::Ident(Self::str_ident(loc, n.as_str())),
        })))
    }

    fn func(def: &Def<Term>, body: &Box<Term>) -> Result<ModuleItem, Error> {
        Ok(ModuleItem::Stmt(Stmt::Decl(Decl::Fn(FnDecl {
            ident: Self::ident(def.loc, &def.name),
            declare: false,
            function: Box::new(Function {
                params: Self::type_erased_params(def.loc, &def.tele),
                decorators: Default::default(),
                span: def.loc.into(),
                body: Some(Self::block(def.loc, body)?),
                is_generator: false,
                is_async: false,
                type_params: None,
                return_type: None,
            }),
        }))))
    }

    fn class(
        def: &Def<Term>,
        object: &Box<Term>,
        ctor: &Def<Term>,
        meths: Vec<&Def<Term>>,
    ) -> Result<Vec<ModuleItem>, Error> {
        use Body::*;

        let mut decls = Vec::default();
        for m in meths {
            decls.push(Self::func(
                m,
                match &m.body {
                    Method(f) => f,
                    _ => unreachable!(),
                },
            )?);
        }
        Ok(decls)
    }

    fn type_erased_param_pat(loc: Loc, p: &Param<Term>) -> Vec<Pat> {
        let mut pats = Vec::default();
        let mut tm = &p.typ;
        loop {
            match &**tm {
                Term::Sigma(p, b) => {
                    pats.push(Self::ident_pat(loc, &p.var));
                    tm = b;
                }
                _ => break,
            }
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

    fn untuple_args(loc: Loc, mut tm: &Box<Term>) -> Result<Vec<ExprOrSpread>, Error> {
        use Term::*;
        let mut ret = Vec::default();
        loop {
            match &**tm {
                Tuple(a, b) => {
                    ret.push(ExprOrSpread {
                        spread: None,
                        expr: Self::expr(loc, a)?,
                    });
                    tm = b
                }
                TT => break,
                // _ => unreachable!(),
                e => {
                    dbg!(e);
                    unreachable!()
                }
            }
        }
        Ok(ret)
    }

    fn lambda_encoded_let(
        loc: Loc,
        v: Option<&Var>,
        a: &Box<Term>,
        b: &Box<Term>,
    ) -> Result<Box<Expr>, Error> {
        Ok(Box::new(Expr::Call(CallExpr {
            span: loc.into(),
            callee: Callee::Expr(Box::new(Expr::Paren(ParenExpr {
                span: loc.into(),
                expr: Box::new(Expr::Arrow(ArrowExpr {
                    span: loc.into(),
                    params: v.map_or_else(|| Default::default(), |v| vec![Self::ident_pat(loc, v)]),
                    body: Box::new(BlockStmtOrExpr::Expr(Self::expr(loc, b)?)),
                    is_async: false,
                    is_generator: false,
                    type_params: None,
                    return_type: None,
                })),
            }))),
            args: vec![ExprOrSpread {
                spread: None,
                expr: Self::expr(loc, a)?,
            }],
            type_args: None,
        })))
    }

    fn const_decl_stmt(loc: Loc, v: &Var, tm: &Box<Term>) -> Result<Stmt, Error> {
        Ok(Stmt::Decl(Decl::Var(Box::new(VarDecl {
            span: loc.into(),
            kind: VarDeclKind::Const,
            declare: false,
            decls: vec![VarDeclarator {
                span: loc.into(),
                name: Self::ident_pat(loc, v),
                init: Some(Self::expr(loc, tm)?),
                definite: false,
            }],
        }))))
    }

    fn block(loc: Loc, body: &Box<Term>) -> Result<BlockStmt, Error> {
        fn strip_untupled_lets(mut tm: &Box<Term>) -> Box<Term> {
            use Term::*;
            loop {
                match &**tm {
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
            match &**tm {
                Let(p, a, b) => {
                    stmts.push(Self::const_decl_stmt(loc, &p.var, a)?);
                    tm = b
                }
                TupleLet(_, _, _, _) => unreachable!(),
                UnitLet(a, b) => {
                    stmts.push(Self::const_decl_stmt(loc, &Var::unbound(), a)?);
                    tm = b
                }
                _ => {
                    stmts.push(Stmt::Return(ReturnStmt {
                        span: loc.into(),
                        arg: Some(Self::expr(loc, tm)?),
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

    fn expr(loc: Loc, tm: &Box<Term>) -> Result<Box<Expr>, Error> {
        use Term::*;
        Ok(match &**tm {
            MetaRef(_, _, _) => return Err(UnsolvedMeta(tm.clone(), loc)),

            Let(p, a, b) => Self::lambda_encoded_let(loc, Some(&p.var), a, b)?,
            UnitLet(a, b) => Self::lambda_encoded_let(loc, None, a, b)?,

            Ref(r) | Undef(r) => Box::new(Expr::Ident(Self::ident(loc, r))),
            Lam(p, b) => match p.info {
                Explicit => Box::new(Expr::Arrow(ArrowExpr {
                    span: loc.into(),
                    params: Self::type_erased_param_pat(loc, p),
                    body: Box::new(BlockStmtOrExpr::BlockStmt(Self::block(loc, b)?)),
                    is_async: false,
                    is_generator: false,
                    type_params: None,
                    return_type: None,
                })),
                _ => Self::expr(loc, b)?,
            },
            App(f, i, x) => match i {
                UnnamedExplicit => Box::new(Expr::Call(CallExpr {
                    span: loc.into(),
                    callee: Callee::Expr(Self::expr(loc, f)?),
                    args: Self::untuple_args(loc, x)?,
                    type_args: None,
                })),
                _ => Self::expr(loc, f)?,
            },
            TT => Box::new(Self::undefined()),
            False => Box::new(Expr::Lit(Lit::Bool(Bool {
                span: loc.into(),
                value: false,
            }))),
            True => Box::new(Expr::Lit(Lit::Bool(Bool {
                span: loc.into(),
                value: true,
            }))),
            If(p, t, e) => Box::new(Expr::Cond(CondExpr {
                span: loc.into(),
                test: Self::expr(loc, p)?,
                cons: Self::expr(loc, t)?,
                alt: Self::expr(loc, e)?,
            })),
            Str(s) => Box::new(Expr::Lit(Lit::Str(JsStr {
                span: loc.into(),
                value: s.as_str().into(),
                raw: None,
            }))),
            Num(_, v) => Box::new(Expr::Lit(Lit::Num(JsNumber {
                span: loc.into(),
                value: v.clone(),
                raw: None,
            }))),
            Big(v) => Box::new(Expr::Lit(Lit::BigInt(JsBigInt {
                span: loc.into(),
                value: Box::new(BigIntValue::from_str(v).unwrap()),
                raw: None,
            }))),
            Obj(f) => match &**f {
                Fields(fields) => {
                    let mut props = Vec::default();
                    for (name, tm) in fields {
                        props.push(PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                            key: PropName::Ident(Self::str_ident(loc, name.as_str())),
                            value: Self::expr(loc, &Box::new(tm.clone()))?,
                        }))));
                    }
                    Box::new(Expr::Object(ObjectLit {
                        span: loc.into(),
                        props,
                    }))
                }
                _ => unreachable!(),
            },
            Concat(a, b) => Box::new(Expr::Object(ObjectLit {
                span: loc.into(),
                props: vec![
                    PropOrSpread::Spread(SpreadElement {
                        dot3_token: loc.into(),
                        expr: Self::expr(loc, a)?,
                    }),
                    PropOrSpread::Spread(SpreadElement {
                        dot3_token: loc.into(),
                        expr: Self::expr(loc, b)?,
                    }),
                ],
            })),
            Access(a, n) => Self::access(loc, a, n)?,
            Downcast(a, f) => match &**f {
                Fields(fields) => {
                    let mut props = Vec::default();
                    for (name, _) in fields {
                        props.push(PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                            key: PropName::Ident(Self::str_ident(loc, name)),
                            value: Self::access(loc, a, name)?,
                        }))))
                    }
                    Box::new(Expr::Object(ObjectLit {
                        span: loc.into(),
                        props,
                    }))
                }
                _ => unreachable!(),
            },
            Variant(f) => match &**f {
                Fields(fields) => {
                    let (name, tm) = fields.iter().nth(0).unwrap();
                    Box::new(Expr::Object(ObjectLit {
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
                                value: Self::expr(loc, &Box::new(tm.clone()))?,
                            }))),
                        ],
                    }))
                }
                _ => unreachable!(),
            },
            Upcast(a, _) => Self::expr(loc, a)?,
            Switch(a, cs) => {
                // ({Some: a => a + 1, None: () => undefined}[a.__rowsT])(a.__rowsV)
                let mut props = Vec::default();
                for (n, (v, tm)) in cs {
                    props.push(PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                        key: PropName::Ident(Self::str_ident(loc, n.as_str())),
                        value: Box::new(Expr::Arrow(ArrowExpr {
                            span: loc.into(),
                            params: vec![Self::ident_pat(loc, v)],
                            body: Box::new(BlockStmtOrExpr::BlockStmt(Self::block(
                                loc,
                                &Box::new(tm.clone()),
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
                let obj = Self::expr(loc, a)?;
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
                Box::new(Expr::Call(CallExpr {
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
                }))
            }
            Find(_, _, f) => return Err(NonErasable(Box::new(Ref(f.clone())), loc)),

            // _ => unreachable!(),
            e => {
                println!("{e}");
                unreachable!()
            }
        })
    }
}

impl Target for Ecma {
    fn filename(&self) -> &'static str {
        "index.js"
    }

    fn module(&self, buf: &mut Vec<u8>, sigma: &Sigma, defs: Vec<Def<Term>>) -> Result<(), Error> {
        use Body::*;

        let mut body = Vec::<ModuleItem>::default();

        for def in defs {
            match &def.body {
                Fn(f) => match Self::func(&def, f) {
                    Ok(decl) => body.push(decl),
                    Err(NonErasable(_, _)) => continue,
                    Err(e) => return Err(e),
                },
                Class {
                    object,
                    ctor,
                    methods,
                    ..
                } => body.extend(Self::class(
                    &def,
                    object,
                    sigma.get(ctor).unwrap(),
                    methods.iter().map(|n| sigma.get(n).unwrap()).collect(),
                )?),
                Undefined => unreachable!(),
                _ => continue,
            }
        }

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
