use std::str::FromStr;
use ustr::{Ustr, UstrMap};

use crate::semantics::builtin::Builtin;
use crate::syntax::{Branch, Def, Expr, File, Id, Ident, Sig, Stmt};
use crate::{Error, Out, Span, Spanned};

#[derive(Default)]
pub(crate) struct Resolver {
    globals: UstrMap<Id>,
    locals: Vec<Ustr>,
}

impl Resolver {
    pub(crate) fn file(&mut self, file: &mut File) -> Out<()> {
        file.defs
            .iter_mut()
            .try_for_each(|def| match &mut def.item {
                Def::Func { sig, body } => {
                    let local = self.sig(sig)?;
                    self.block(local, body)
                }
            })?;
        file.main = self.globals.get(&Ustr::from("main")).cloned();
        debug_assert!(self.locals.is_empty());
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

    fn sig(&mut self, sig: &mut Sig) -> Out<Block> {
        sig.ret
            .as_mut()
            .map(|t| self.expr(t.span, &mut t.item))
            .transpose()?;
        let mut local = Block::local();
        sig.params.iter_mut().try_for_each(|p| {
            p.item
                .typ
                .as_mut()
                .map(|t| self.expr(t.span, &mut t.item))
                .transpose()?;
            self.insert(&mut local, &mut p.item.name);
            Ok(())
        })?;
        self.globals.insert(sig.name.raw(), sig.name.clone());
        Ok(local)
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
            Expr::Call(callee, args) => {
                self.expr(callee.span, &mut callee.item)?;
                args.iter_mut()
                    .try_for_each(|arg| self.expr(arg.span, &mut arg.item))
            }
            Expr::BinaryOp(lhs, .., rhs) => {
                self.expr(lhs.span, &mut lhs.item)?;
                self.expr(rhs.span, &mut rhs.item)
            }
            Expr::New(e) => self.expr(e.span, &mut e.item),

            Expr::BuiltinType(..)
            | Expr::Unit
            | Expr::Integer(..)
            | Expr::Float(..)
            | Expr::String(..)
            | Expr::Boolean(..) => Ok(()),

            Expr::Ref(..) => unreachable!(),
        }
    }

    fn name(&mut self, span: Span, ident: &mut Ident) -> Out<()> {
        let id = ident.as_id_mut();
        let raw = id.raw();
        if let Some(found) = self.locals.iter().rposition(|each| raw == **each) {
            *ident = Ident::Idx(found);
            return Ok(());
        }
        if let Some(found) = self.globals.get(&raw) {
            *id = found.clone();
            return Ok(());
        }
        if let Ok(builtin) = Builtin::from_str(&raw) {
            *ident = Ident::Builtin(builtin);
            return Ok(());
        }
        Err(Error::UndefName(span, raw))
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
