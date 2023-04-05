use std::rc::Rc;

use swc_common::{BytePos, SourceMap, Span, DUMMY_SP};
use swc_ecma_ast::{BlockStmt, Decl, FnDecl, Function, Ident, Module, ModuleItem, Stmt};
use swc_ecma_codegen::text_writer::JsWriter;
use swc_ecma_codegen::Emitter;

use crate::codegen::Target;
use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Body, Def, Sigma};
use crate::theory::{Loc, Var};
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

    fn func(&self, sigma: &Sigma, def: &Def<Term>, body: &Box<Term>) -> Result<Decl, Error> {
        // TODO
        Ok(Decl::Fn(FnDecl {
            ident: Self::ident(def.loc, &def.name),
            declare: false,
            function: Box::new(Function {
                params: Default::default(),
                decorators: Default::default(),
                span: def.loc.into(),
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
        &self,
        sigma: &Sigma,
        def: &Def<Term>,
        object: &Box<Term>,
        ctor: &Def<Term>,
        meths: Vec<&Def<Term>>,
    ) -> Result<Decl, Error> {
        todo!()
    }

    fn term(&self, sigma: &Sigma, tm: &Box<Term>) -> Result<(), Error> {
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
                Fn(body) => self.func(sigma, &def, body)?,
                Class {
                    object,
                    ctor,
                    methods,
                    ..
                } => continue,
                // TODO
                // } => self.class(
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
