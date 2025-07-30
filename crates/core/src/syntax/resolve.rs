use ustr::{Ustr, UstrMap};

use crate::syntax::{Branch, Expr, Name, Shadowed, Sig, Stmt};
use crate::{Error, Out, Span, Spanned};

#[derive(Default)]
pub(crate) struct Resolver {
    globals: UstrMap<Name>,
    locals: UstrMap<Name>,
}

impl Resolver {
    pub(crate) fn file(&mut self, file: &mut [Spanned<Stmt>]) -> Out<()> {
        let mut block = Block::default();
        file.iter_mut()
            .try_for_each(|stmt| self.stmt(&mut block, stmt))?;
        debug_assert!(self.locals.is_empty());
        Ok(())
    }

    fn stmt(&mut self, block: &mut Block, stmt: &mut Spanned<Stmt>) -> Out<()> {
        match &mut stmt.item {
            Stmt::Func { sig, body, .. } => {
                let local = self.sig(block, sig)?;
                self.block(local, body)?;
            }
            Stmt::Expr(e) => self.expr(stmt.span, e)?,
            Stmt::Assign { name, typ, rhs, .. } => {
                typ.as_mut()
                    .map(|t| self.expr(t.span, &mut t.item))
                    .transpose()?;
                self.expr(rhs.span, &mut rhs.item)?;
                self.insert(block, name);
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
        }
        Ok(())
    }

    fn sig(&mut self, block: &mut Block, sig: &mut Sig) -> Out<Block> {
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
            self.insert(&mut local, &p.item.name);
            Ok(())
        })?;
        self.insert(block, &sig.name);
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
        block.shadowed.into_iter().for_each(|(raw, name)| {
            name.map(|old| self.locals.insert(raw, old))
                .unwrap_or_else(|| self.locals.remove(&raw));
        })
    }

    fn branch(&mut self, branch: &mut Branch) -> Out<()> {
        self.expr(branch.cond.span, &mut branch.cond.item)?;
        self.block(Block::local(), &mut branch.body)
    }

    fn expr(&mut self, span: Span, expr: &mut Expr) -> Out<()> {
        match expr {
            Expr::Name(n) => {
                let raw = n.raw();
                self.locals
                    .get(&raw)
                    .or_else(|| self.globals.get(&raw))
                    .map(|found| {
                        *n = found.clone();
                    })
                    .ok_or(Error::UndefName(span, raw))?;
            }

            Expr::Call(callee, args) => {
                self.expr(callee.span, &mut callee.item)?;
                args.iter_mut()
                    .try_for_each(|arg| self.expr(arg.span, &mut arg.item))?;
            }
            Expr::BinaryOp(lhs, .., rhs) => {
                self.expr(lhs.span, &mut lhs.item)?;
                self.expr(rhs.span, &mut rhs.item)?;
            }

            Expr::BuiltinType(..)
            | Expr::Unit
            | Expr::Number(..)
            | Expr::String(..)
            | Expr::Boolean(..) => (),
        }
        Ok(())
    }

    fn insert(&mut self, block: &mut Block, name: &Name) {
        if block.local {
            return block
                .shadowed
                .push(name.raw(), self.locals.insert(name.raw(), name.clone()));
        }
        self.globals.insert(name.raw(), name.clone());
    }
}

#[derive(Default)]
struct Block {
    local: bool,
    shadowed: Shadowed<Ustr, Name>,
}

impl Block {
    fn local() -> Self {
        Self {
            local: true,
            ..Default::default()
        }
    }
}
