use std::rc::Rc;

use swc_common::{BytePos, SourceMap, Span, DUMMY_SP};
use swc_ecma_ast::{
    BindingIdent, BlockStmt, Decl, FnDecl, Function, Ident, Module, ModuleItem, Param, Pat, Stmt,
};
use swc_ecma_codegen::text_writer::JsWriter;
use swc_ecma_codegen::Emitter;

use crate::codegen::Target;
use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Body, Def, Sigma};
use crate::theory::{Loc, Tele, Var, TUPLED};
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

    fn func(sigma: &Sigma, def: &Def<Term>, body: &Box<Term>) -> Result<Decl, Error> {
        Ok(Decl::Fn(FnDecl {
            ident: Self::ident(def.loc, &def.name),
            declare: false,
            function: Box::new(Function {
                params: Self::params(def.loc, &def.tele),
                decorators: Default::default(),
                span: def.loc.into(),
                // TODO
                body: Some(BlockStmt {
                    span: def.loc.into(),
                    stmts: Default::default(),
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
                            pat: Pat::Ident(BindingIdent {
                                id: Self::ident(loc, &p.var),
                                type_ann: None,
                            }),
                        });
                        tm = b;
                    }
                    _ => break,
                }
            }
        }
        params
    }

    fn term(sigma: &Sigma, tm: &Box<Term>) -> Result<(), Error> {
        todo!()
    }
}

impl Target for Ecma {
    fn filename(&self) -> &'static str {
        "index.js"
    }

    fn defs(&self, buf: &mut Vec<u8>, sigma: &Sigma, defs: Vec<Def<Term>>) -> Result<(), Error> {
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
