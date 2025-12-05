use std::str::FromStr;

use ustr::{Ustr, UstrMap, UstrSet};

use crate::semantics::builtin::Builtin;
use crate::syntax::{Branch, Def, Expr, File, FuncSig, Id, Ident, Object, Param, Sig, Stmt};
use crate::{Error, Out, Span, Spanned};

#[derive(Default)]
pub(crate) struct Resolver {
    globals: UstrMap<Id>,
    locals: Vec<Ustr>,
    names: Names,
}

impl Resolver {
    pub(crate) fn file(&mut self, file: &mut File) -> Out<()> {
        file.decls.iter_mut().try_for_each(|decl| {
            let name = match &mut decl.item.sig {
                Sig::Func(sig) => {
                    self.func_sig(sig)?;
                    Some(sig.name.clone())
                }
                Sig::Static { name, typ } => {
                    self.expr(typ.span, &mut typ.item)?;
                    Some(name.clone())
                }
                Sig::Struct { name, members } => {
                    let mut names = Names::default();
                    members.iter_mut().try_for_each(|m| {
                        names.ensure_unique(m.span, m.item.name, true)?;
                        self.expr(m.item.typ.span, &mut m.item.typ.item)
                    })?;
                    Some(name.clone())
                }
                Sig::Extends { target, methods } => {
                    self.name(decl.span, target)?;
                    let mut names = Names::default();
                    methods.iter_mut().try_for_each(|m| {
                        names.ensure_unique(m.span, m.item.sig.name.raw(), true)?;
                        self.func_sig(&mut m.item.sig)
                    })?;
                    None
                }
            };
            if let Some(name) = name {
                self.names.ensure_unique(decl.span, name.raw(), false)?;
                self.globals.insert(name.raw(), name);
            }
            Ok(())
        })?;
        file.decls
            .iter_mut()
            .try_for_each(|decl| match &mut decl.item.def {
                Def::Func { body } => {
                    let Sig::Func(sig) = &mut decl.item.sig else {
                        unreachable!()
                    };
                    let mut local = Block::local();
                    sig.params
                        .iter_mut()
                        .for_each(|p| self.insert(&mut local, &mut p.item.name));
                    self.block(local, body)
                }
                Def::Static { rhs } => self.expr(rhs.span, &mut rhs.item),
                Def::Struct => Ok(()),
                Def::Extends { bodies } => {
                    let Sig::Extends { methods, .. } = &mut decl.item.sig else {
                        unreachable!();
                    };
                    methods
                        .iter_mut()
                        .zip(bodies.iter_mut())
                        .try_for_each(|(sig, body)| {
                            let mut local = Block::local();
                            sig.item.sig.params.insert(
                                0,
                                Spanned {
                                    span: sig.span,
                                    item: Param {
                                        name: Ident::Id(Id::this()),
                                        typ: Spanned {
                                            span: sig.span,
                                            item: Expr::ThisType,
                                        },
                                    },
                                },
                            );
                            sig.item
                                .sig
                                .params
                                .iter_mut()
                                .for_each(|p| self.insert(&mut local, &mut p.item.name));
                            self.block(local, body)
                        })
                }
            })?;
        file.main = self.globals.get(&Ustr::from("main")).cloned();
        debug_assert!(self.locals.is_empty());
        Ok(())
    }

    fn func_sig(&mut self, sig: &mut FuncSig) -> Out<()> {
        sig.params
            .iter_mut()
            .try_for_each(|p| self.expr(p.item.typ.span, &mut p.item.typ.item))?;
        sig.ret
            .as_mut()
            .map(|t| self.expr(t.span, &mut t.item))
            .transpose()?;
        Ok(())
    }

    fn stmt(&mut self, block: &mut Block, stmt: &mut Spanned<Stmt>) -> Out<()> {
        match &mut stmt.item {
            Stmt::Expr(e) => self.expr(stmt.span, e)?,
            Stmt::Assign { name, typ, rhs, .. } => {
                typ.as_mut()
                    .map(|t| self.expr(t.span, &mut t.item))
                    .transpose()?;
                self.expr(rhs.span, &mut rhs.item)?;
                self.insert(block, &mut name.item);
            }
            Stmt::Update { name, rhs } => {
                self.name(name.span, &mut name.item)?;
                self.expr(rhs.span, &mut rhs.item)?;
            }
            Stmt::Return(e) => {
                e.as_mut()
                    .map(|e| self.expr(e.span, &mut e.item))
                    .transpose()?;
            }
            Stmt::If { then, elif, els } => {
                self.branch(then)?;
                elif.iter_mut().try_for_each(|b| self.branch(b))?;
                els.as_mut()
                    .map(|(.., stmts)| self.block(Block::local(), stmts))
                    .transpose()?;
            }
            Stmt::While(branch) => self.branch(branch)?,
        }
        Ok(())
    }

    fn block(&mut self, mut block: Block, stmts: &mut [Spanned<Stmt>]) -> Out<()> {
        stmts
            .iter_mut()
            .try_for_each(|stmt| self.stmt(&mut block, stmt))?;
        self.drop_block(block);
        Ok(())
    }

    fn drop_block(&mut self, block: Block) {
        debug_assert!(block.local);
        for _ in 0..block.locals {
            self.locals.pop();
        }
    }

    fn branch(&mut self, branch: &mut Branch) -> Out<()> {
        self.expr(branch.cond.span, &mut branch.cond.item)?;
        self.block(Block::local(), &mut branch.body)
    }

    fn expr(&mut self, span: Span, expr: &mut Expr) -> Out<()> {
        match expr {
            Expr::Ident(id) => self.name(span, id),

            Expr::RefType(e) => self.expr(e.span, &mut e.item),
            Expr::Call(callee, args) | Expr::Method(callee, .., args) => {
                self.expr(callee.span, &mut callee.item)?;
                args.iter_mut()
                    .try_for_each(|a| self.expr(a.span, &mut a.item))
            }
            Expr::BinaryOp(lhs, .., rhs) => {
                self.expr(lhs.span, &mut lhs.item)?;
                self.expr(rhs.span, &mut rhs.item)
            }
            Expr::UnaryOp(x, ..) => self.expr(x.span, &mut x.item),
            Expr::New(e) => self.expr(e.span, &mut e.item),
            Expr::Object(callee, args) => {
                let mut names = Names::default();
                self.expr(callee.span, &mut callee.item)?;
                let Object::Unordered(args) = args else {
                    unreachable!()
                };
                args.iter_mut().try_for_each(|(name, a)| {
                    names.ensure_unique(name.span, name.item, true)?;
                    self.expr(a.span, &mut a.item)
                })
            }
            Expr::Access(callee, ..) => self.expr(callee.span, &mut callee.item),

            Expr::BuiltinType(..)
            | Expr::Unit
            | Expr::Integer(..)
            | Expr::Float(..)
            | Expr::String(..)
            | Expr::Boolean(..) => Ok(()),

            Expr::ThisType | Expr::StructType(..) | Expr::Ref(..) | Expr::Struct(..) => {
                unreachable!()
            }
        }
    }

    fn name(&mut self, span: Span, ident: &mut Ident) -> Out<()> {
        let id = ident.as_id_mut();
        let name = id.raw();
        if let Some(found) = self.locals.iter().rposition(|each| name == **each) {
            *ident = Ident::Idx(found);
            return Ok(());
        }
        if let Some(found) = self.globals.get(&name) {
            *id = found.clone();
            return Ok(());
        }
        if let Ok(builtin) = Builtin::from_str(&name) {
            *ident = Ident::Builtin(builtin);
            return Ok(());
        }
        Err(Error::UndefName {
            span,
            name,
            is_member: false,
        })
    }

    fn insert(&mut self, block: &mut Block, ident: &mut Ident) {
        let id = ident.as_id_mut();
        if block.local {
            self.locals.push(id.raw());
            *ident = Ident::Idx(self.locals.len() - 1);
            block.locals += 1;
            return;
        }
        self.globals.insert(id.raw(), id.clone());
    }
}

#[derive(Default)]
struct Block {
    local: bool,
    locals: usize,
}

impl Block {
    fn local() -> Self {
        Self {
            local: true,
            ..Default::default()
        }
    }
}

#[derive(Default)]
struct Names(UstrSet);

impl Names {
    fn ensure_unique(&mut self, span: Span, name: Ustr, is_member: bool) -> Out<()> {
        if self.0.insert(name) {
            return Ok(());
        }
        Err(Error::DuplicateName {
            span,
            name,
            is_member,
        })
    }
}
