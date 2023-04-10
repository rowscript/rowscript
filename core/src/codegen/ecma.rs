use std::rc::Rc;
use std::str::FromStr;

use num_bigint::BigInt as BigIntValue;
use swc_atoms::js_word;
use swc_common::{BytePos, SourceMap, Span, DUMMY_SP};
use swc_ecma_ast::{
    ArrowExpr, BigInt as JsBigInt, BindingIdent, BlockStmt, BlockStmtOrExpr, Bool, CallExpr,
    Callee, CondExpr, Decl, Expr, ExprOrSpread, FnDecl, Function, Ident, Lit, Module, ModuleItem,
    Number as JsNumber, Param as JsParam, Pat, ReturnStmt, Stmt, Str as JsStr, VarDecl,
    VarDeclKind, VarDeclarator,
};
use swc_ecma_codegen::text_writer::JsWriter;
use swc_ecma_codegen::Emitter;

use crate::codegen::Target;
use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Body, Def, Sigma};
use crate::theory::conc::data::ArgInfo::UnnamedExplicit;
use crate::theory::ParamInfo::Explicit;
use crate::theory::{Loc, Param, Tele, Var, TUPLED, UNTUPLED_RHS};
use crate::Error;
use crate::Error::UnsolvedMeta;

#[derive(Default)]
pub struct Ecma;

impl Into<Span> for Loc {
    fn into(self) -> Span {
        Span {
            lo: BytePos(self.start as u32),
            hi: BytePos(self.end as u32),
            ctxt: Default::default(),
        }
    }
}

impl Ecma {
    fn ident(loc: Loc, v: &Var) -> Ident {
        Ident {
            span: loc.into(),
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

    fn undefined() -> Expr {
        Expr::Ident(Ident {
            span: DUMMY_SP,
            sym: js_word!("undefined"),
            optional: false,
        })
    }

    fn func(sigma: &Sigma, def: &Def<Term>, body: &Box<Term>) -> Result<Decl, Error> {
        Ok(Decl::Fn(FnDecl {
            ident: Self::ident(def.loc, &def.name),
            declare: false,
            function: Box::new(Function {
                params: Self::type_erased_params(def.loc, &def.tele),
                decorators: Default::default(),
                span: def.loc.into(),
                body: Some(Self::block(sigma, def.loc, body)?),
                is_generator: false,
                is_async: false,
                type_params: None,
                return_type: None,
            }),
        }))
    }

    fn class(
        sigma: &Sigma,
        def: &Def<Term>,
        object: &Box<Term>,
        ctor: &Def<Term>,
        meths: Vec<&Def<Term>>,
    ) -> Result<Decl, Error> {
        todo!()
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

    fn untuple_args(
        sigma: &Sigma,
        loc: Loc,
        mut tm: &Box<Term>,
    ) -> Result<Vec<ExprOrSpread>, Error> {
        use Term::*;
        let mut ret = Vec::default();
        loop {
            match &**tm {
                Tuple(a, b) => {
                    ret.push(ExprOrSpread {
                        spread: None,
                        expr: Self::expr(sigma, loc, a)?,
                    });
                    tm = b
                }
                TT => break,
                _ => unreachable!(),
            }
        }
        Ok(ret)
    }

    fn const_decl_stmt(sigma: &Sigma, loc: Loc, v: &Var, tm: &Box<Term>) -> Result<Stmt, Error> {
        Ok(Stmt::Decl(Decl::Var(Box::new(VarDecl {
            span: loc.into(),
            kind: VarDeclKind::Const,
            declare: false,
            decls: vec![VarDeclarator {
                span: loc.into(),
                name: Self::ident_pat(loc, v),
                init: Some(Self::expr(sigma, loc, tm)?),
                definite: false,
            }],
        }))))
    }

    fn block(sigma: &Sigma, loc: Loc, body: &Box<Term>) -> Result<BlockStmt, Error> {
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
                    stmts.push(Self::const_decl_stmt(sigma, loc, &p.var, a)?);
                    tm = b
                }
                TupleLet(_, _, _, _) => todo!(),
                UnitLet(a, b) => {
                    stmts.push(Self::const_decl_stmt(sigma, loc, &Var::unbound(), a)?);
                    tm = b
                }
                _ => {
                    stmts.push(Stmt::Return(ReturnStmt {
                        span: loc.into(),
                        arg: Some(Self::expr(sigma, loc, tm)?),
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

    fn expr(sigma: &Sigma, loc: Loc, tm: &Box<Term>) -> Result<Box<Expr>, Error> {
        use Term::*;
        Ok(match &**tm {
            MetaRef(_, _, _) => return Err(UnsolvedMeta(tm.clone(), loc)),

            Ref(r) => Box::new(Expr::Ident(Self::ident(loc, r))),
            Lam(p, b) => match p.info {
                Explicit => Box::new(Expr::Arrow(ArrowExpr {
                    span: loc.into(),
                    params: Self::type_erased_param_pat(loc, p),
                    body: Box::new(BlockStmtOrExpr::BlockStmt(Self::block(sigma, loc, b)?)),
                    is_async: false,
                    is_generator: false,
                    type_params: None,
                    return_type: None,
                })),
                _ => Self::expr(sigma, loc, b)?,
            },
            App(f, i, x) => match i {
                UnnamedExplicit => Box::new(Expr::Call(CallExpr {
                    span: loc.into(),
                    callee: Callee::Expr(Self::expr(sigma, loc, f)?),
                    args: Self::untuple_args(sigma, loc, x)?,
                    type_args: None,
                })),
                _ => Self::expr(sigma, loc, f)?,
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
                test: Self::expr(sigma, loc, p)?,
                cons: Self::expr(sigma, loc, t)?,
                alt: Self::expr(sigma, loc, e)?,
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
            Obj(_) => todo!("build internal fields into object literals"),
            Concat(_, _) => todo!("object literals in-place updates"),
            Access(_, _) => todo!("object access"),
            Downcast(_, _) => todo!("delete a field from object literals"),
            Variant(_) => todo!("single-field object literal"),
            Upcast(a, _) => Self::expr(sigma, loc, a)?,
            Switch(_, _) => todo!("switch on the object literal's sole field"),

            _ => unreachable!(),
        })
    }
}

impl Target for Ecma {
    fn filename(&self) -> &'static str {
        "index.js"
    }

    fn package(&self, buf: &mut Vec<u8>, sigma: &Sigma, defs: Vec<Def<Term>>) -> Result<(), Error> {
        use Body::*;

        let mut body = Vec::<ModuleItem>::default();

        for def in defs {
            body.push(ModuleItem::Stmt(Stmt::Decl(match &def.body {
                Fn(body) => Self::func(sigma, &def, body)?,
                Class {
                    object,
                    ctor,
                    methods,
                    ..
                } => continue,
                // TODO
                // } => Self::class(
                //     sigma,
                //     &def,
                //     object,
                //     sigma.get(ctor).unwrap(),
                //     methods.iter().map(|n| sigma.get(n).unwrap()).collect(),
                // )?,
                Undefined => unreachable!(),
                _ => continue,
            })))
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
