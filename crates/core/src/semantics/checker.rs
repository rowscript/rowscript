use std::collections::HashMap;

use crate::semantics::Type;
use crate::semantics::solver::isa;
use crate::syntax::parser::Sym;
use crate::syntax::{Branch, BuiltinType, Expr, Name, Sig, Stmt};
use crate::{Error, Out, Span, Spanned};

pub(crate) trait Checked {
    fn checked(self) -> Out<()>;
}

impl Checked for Vec<Spanned<Stmt>> {
    fn checked(self) -> Out<()> {
        Checker::default().file(self.as_slice())
    }
}

#[derive(Default)]
struct Checker {
    globals: HashMap<Name, Type>,
    locals: HashMap<Name, Type>,
}

impl Checker {
    fn file(&mut self, file: &[Spanned<Stmt>]) -> Out<()> {
        let mut block = Block::global();
        file.iter()
            .try_for_each(|stmt| self.stmt(&mut block, stmt).map(|_| ()))
    }

    fn stmt(&mut self, block: &mut Block, stmt: &Spanned<Stmt>) -> Out<Type> {
        Ok(match &stmt.item {
            Stmt::Func(sig, body) => {
                let local = self.sig(block, sig)?;
                self.block(local, body)?
            }
            Stmt::Fn(sig, body) => {
                let local = self.sig(block, sig)?;
                self.block_expr(local, &body.item)?
            }
            Stmt::Expr(e) => self.infer(e)?.1,
            Stmt::Assign { name, typ, rhs, .. } => {
                let rhs_type = typ
                    .as_ref()
                    .map(|t| {
                        let want = self.check_type(t.span, &t.item)?;
                        self.check(rhs.span, &rhs.item, &want)?;
                        Ok(want)
                    })
                    .unwrap_or_else(|| Ok(self.infer(&rhs.item)?.1))?;
                self.insert(block, name.clone(), rhs_type.clone());
                rhs_type
            }
            Stmt::Return(e) => e
                .as_ref()
                .map(|e| {
                    self.check(e.span, &e.item, &block.ret)
                        .map(|_| block.ret.clone())
                })
                .transpose()?
                .unwrap_or(Type::BuiltinType(BuiltinType::Unit)),
            Stmt::If { then, elif, els } => {
                let want = self.branch(block, then)?;
                elif.iter().try_for_each(|b| {
                    let got = self.branch(block, b)?;
                    isa(b.span, &got, &want)
                })?;
                els.as_ref()
                    .map(|(span, stmts)| {
                        let got = self.block(block.local(), stmts)?;
                        isa(*span, &got, &want)
                    })
                    .transpose()?;
                want
            }
        })
    }

    fn sig(&mut self, block: &mut Block, sig: &Sig) -> Out<Block> {
        let ret = sig
            .ret
            .as_ref()
            .map(|t| self.check_type(t.span, &t.item))
            .transpose()?
            .unwrap_or(Type::BuiltinType(BuiltinType::Unit));
        let mut local = Block::func(ret.clone());
        let params = sig
            .params
            .iter()
            .map(|p| {
                let typ = p
                    .item
                    .typ
                    .as_ref()
                    .map(|t| self.check_type(t.span, &t.item))
                    .transpose()?
                    .unwrap_or(Type::BuiltinType(BuiltinType::Unit));
                self.insert(&mut local, p.item.name.clone(), typ.clone());
                Ok(typ)
            })
            .collect::<Out<Box<_>>>()?;
        self.insert(
            block,
            sig.name.clone(),
            Type::FunctionType(params, Box::new(ret)),
        );
        Ok(local)
    }

    fn block(&mut self, mut block: Block, stmts: &[Spanned<Stmt>]) -> Out<Type> {
        let typ = stmts
            .iter()
            .map(|stmt| self.stmt(&mut block, stmt))
            .collect::<Out<Vec<_>>>()?
            .into_iter()
            .last()
            .unwrap_or(Type::BuiltinType(BuiltinType::Unit));
        self.drop_block(block);
        Ok(typ)
    }

    fn block_expr(&mut self, block: Block, expr: &Expr) -> Out<Type> {
        let typ = self.infer(expr)?.1;
        self.drop_block(block);
        Ok(typ)
    }

    fn drop_block(&mut self, block: Block) {
        block.shadowed.into_iter().for_each(|(raw, name)| {
            match name {
                None => self.locals.remove(&raw),
                Some(old) => self.locals.insert(raw, old),
            };
        })
    }

    fn branch(&mut self, block: &Block, branch: &Branch) -> Out<Type> {
        self.check(
            branch.cond.span,
            &branch.cond.item,
            &Type::BuiltinType(BuiltinType::Bool),
        )?;
        self.block(block.local(), &branch.body)
    }

    fn check(&mut self, span: Span, expr: &Expr, want: &Type) -> Out<Option<Type>> {
        if let Expr::Number(..) = expr
            && let Type::BuiltinType(t) = want
            && t.is_number()
        {
            return Ok(None);
        }

        let (typ, got) = self.infer(expr)?;
        isa(span, &got, want)?;
        Ok(typ)
    }

    fn check_type(&mut self, span: Span, expr: &Expr) -> Out<Type> {
        self.check(span, expr, &Type::BuiltinType(BuiltinType::Type))
            .map(Option::unwrap)
    }

    fn infer(&mut self, expr: &Expr) -> Out<(Option<Type>, Type)> {
        Ok((
            None,
            match expr {
                Expr::Name(n) => self
                    .locals
                    .get(n)
                    .or_else(|| self.globals.get(n))
                    .cloned()
                    .unwrap(),
                Expr::BuiltinType(t) => {
                    return Ok((
                        Some(Type::BuiltinType(*t)),
                        Type::BuiltinType(BuiltinType::Type),
                    ));
                }
                Expr::Number(..) => Type::BuiltinType(BuiltinType::F64),
                Expr::String(..) => Type::BuiltinType(BuiltinType::Str),
                Expr::Boolean(..) => Type::BuiltinType(BuiltinType::Bool),
                Expr::Call(f, args) => {
                    let span = f.span;
                    let f_type = self.infer(&f.item)?.1;
                    let Type::FunctionType(params, ret) = f_type else {
                        return Err(Error::TypeMismatch {
                            span,
                            got: f_type.to_string(),
                            want: "function".to_string(),
                        });
                    };
                    {
                        let got = args.len();
                        let want = params.len();
                        if got != want {
                            return Err(Error::ArityMismatch { span, got, want });
                        }
                    }
                    args.iter().zip(params.iter()).try_for_each(|(got, want)| {
                        self.check(got.span, &got.item, want)?;
                        Ok(())
                    })?;
                    *ret
                }
                Expr::BinaryOp(lhs, op, rhs) => match op {
                    Sym::EqEq => {
                        let want = self.infer(&lhs.item)?.1;
                        self.check(rhs.span, &rhs.item, &want)?;
                        Type::BuiltinType(BuiltinType::Bool)
                    }

                    Sym::Lt | Sym::Gt | Sym::Le | Sym::Ge => {
                        let got = self.infer(&lhs.item)?.1;
                        if let Type::BuiltinType(t) = got
                            && t.is_number()
                        {
                            self.check(rhs.span, &rhs.item, &got)?;
                            Type::BuiltinType(BuiltinType::Bool)
                        } else {
                            return Err(Error::TypeMismatch {
                                span: lhs.span,
                                got: got.to_string(),
                                want: "number".to_string(),
                            });
                        }
                    }

                    Sym::Plus | Sym::Minus => {
                        let got = self.infer(&lhs.item)?.1;
                        if let Type::BuiltinType(t) = got
                            && t.is_number()
                        {
                            self.check(rhs.span, &rhs.item, &got)?;
                            got
                        } else {
                            return Err(Error::TypeMismatch {
                                span: lhs.span,
                                got: got.to_string(),
                                want: "number".to_string(),
                            });
                        }
                    }

                    Sym::Assign | Sym::LParen | Sym::RParen | Sym::Comma | Sym::Colon | Sym::Eq => {
                        unreachable!()
                    }
                },
            },
        ))
    }

    fn insert(&mut self, block: &mut Block, name: Name, typ: Type) {
        if block.is_local {
            return block
                .shadowed
                .push((name.clone(), self.locals.insert(name, typ)));
        }
        self.globals.insert(name, typ);
    }
}

struct Block {
    ret: Type,
    is_local: bool,
    shadowed: Vec<(Name, Option<Type>)>,
}

impl Block {
    fn global() -> Self {
        Self {
            ret: Type::BuiltinType(BuiltinType::Unit),
            is_local: false,
            shadowed: Default::default(),
        }
    }

    fn func(ret: Type) -> Self {
        Self {
            ret,
            is_local: true,
            shadowed: Default::default(),
        }
    }

    fn local(&self) -> Self {
        Self {
            ret: self.ret.clone(),
            is_local: true,
            shadowed: Default::default(),
        }
    }
}
