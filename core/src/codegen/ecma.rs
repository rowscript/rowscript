use std::rc::Rc;

use swc_common::{BytePos, SourceMap, Span, DUMMY_SP};
use swc_ecma_ast::{
    BindingIdent, BlockStmt, Decl, Expr, FnDecl, Function, Ident, Lit, Module, ModuleItem, Number,
    Param, Pat, ReturnStmt, Stmt, VarDecl, VarDeclKind, VarDeclarator,
};
use swc_ecma_codegen::text_writer::JsWriter;
use swc_ecma_codegen::Emitter;

use crate::codegen::Target;
use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Body, Def, Sigma};
use crate::theory::{Loc, Tele, Var, TUPLED, UNTUPLED_RHS};
use crate::Error;

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

    fn func(sigma: &Sigma, def: &Def<Term>, body: &Box<Term>) -> Result<Decl, Error> {
        Ok(Decl::Fn(FnDecl {
            ident: Self::ident(def.loc, &def.name),
            declare: false,
            function: Box::new(Function {
                params: Self::params(def.loc, &def.tele),
                decorators: Default::default(),
                span: def.loc.into(),
                body: Some(BlockStmt {
                    span: def.loc.into(),
                    stmts: Self::block(sigma, def.loc, &Self::strip_untupled_lets(body))?,
                }),
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

    fn params(loc: Loc, tele: &Tele<Term>) -> Vec<Param> {
        let mut params = Vec::default();
        for p in tele {
            if p.var.as_str() != TUPLED {
                continue;
            }
            let mut tm = &p.typ;
            loop {
                match &**tm {
                    Term::Sigma(p, b) => {
                        params.push(Param {
                            span: loc.into(),
                            decorators: Default::default(),
                            pat: Self::ident_pat(loc, &p.var),
                        });
                        tm = b;
                    }
                    _ => break,
                }
            }
        }
        params
    }

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

    fn const_decl_stmt(sigma: &Sigma, loc: Loc, v: &Var, tm: &Box<Term>) -> Result<Stmt, Error> {
        Ok(Stmt::Decl(Decl::Var(Box::new(VarDecl {
            span: loc.into(),
            kind: VarDeclKind::Const,
            declare: false,
            decls: vec![VarDeclarator {
                span: loc.into(),
                name: Self::ident_pat(loc, v),
                init: Self::expr(sigma, loc, tm)?,
                definite: false,
            }],
        }))))
    }

    fn block(sigma: &Sigma, loc: Loc, mut tm: &Box<Term>) -> Result<Vec<Stmt>, Error> {
        use Term::*;
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
                        arg: Self::expr(sigma, loc, tm)?,
                    }));
                    break;
                }
            }
        }
        Ok(stmts)
    }

    fn expr(sigma: &Sigma, loc: Loc, tm: &Box<Term>) -> Result<Option<Box<Expr>>, Error> {
        // TODO
        Ok(Some(Box::new(Expr::Lit(Lit::Num(Number {
            span: loc.into(),
            value: 42.0,
            raw: None,
        })))))
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
