use std::collections::HashMap;
use std::mem::take;

use crate::semantics::{BuiltinType, Func, FunctionType, Functions, Type};
use crate::syntax::parse::Sym;
use crate::syntax::{Branch, Def, Expr, File, Id, Ident, Sig, Stmt};
use crate::{Error, Out, Span, Spanned};

#[derive(Default)]
pub(crate) struct Checker {
    globals: HashMap<Id, Type>,
    locals: Vec<Type>,
    fns: Functions,
}

impl Checker {
    pub(crate) fn file(mut self, file: &mut File) -> Out<Functions> {
        file.defs
            .iter_mut()
            .try_for_each(|def| match &mut def.item {
                Def::Func { sig, body } => {
                    let (typ, local) = self.sig(sig)?;
                    let got = self.block(local, body)?;
                    isa(def.span, &got, &typ.ret)?;
                    let old = self.fns.insert(
                        sig.name.clone(),
                        Func {
                            typ,
                            body: take(body),
                        },
                    );
                    debug_assert!(old.is_none());
                    Ok(())
                }
            })?;
        debug_assert!(self.locals.is_empty());
        Ok(self.fns)
    }

    fn stmt(&mut self, block: &mut Block, stmt: &mut Spanned<Stmt>) -> Out<Type> {
        Ok(match &mut stmt.item {
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
                self.insert(block, &name.item, rhs_type.clone());
                *typ = Some(Spanned {
                    span: typ.as_ref().map(|t| t.span).unwrap_or(name.span),
                    item: match rhs_type {
                        Type::Builtin(t) => Expr::BuiltinType(t),
                        _ => todo!(),
                    },
                });
                rhs_type
            }
            Stmt::Update { name, rhs } => {
                let rhs_type = self.infer(&rhs.item)?.1;
                let lhs_type = self.ident(&name.item);
                isa(name.span, &rhs_type, &lhs_type)?;
                lhs_type
            }
            Stmt::Return(e) => e
                .as_ref()
                .map(|e| {
                    self.check(e.span, &e.item, &block.ret)
                        .map(|_| block.ret.clone())
                })
                .transpose()?
                .unwrap_or(Type::Builtin(BuiltinType::Unit)),
            Stmt::If { then, elif, els } => {
                let want = self.branch(block, then)?;
                elif.iter_mut().try_for_each(|b| {
                    let got = self.branch(block, b)?;
                    isa(b.span, &got, &want)
                })?;
                els.as_mut()
                    .map(|(span, stmts)| {
                        let got = self.block(block.local(), stmts)?;
                        isa(*span, &got, &want)
                    })
                    .transpose()?;
                want
            }
            Stmt::While(branch) => self.branch(block, branch)?,
        })
    }

    fn sig(&mut self, sig: &Sig) -> Out<(FunctionType, Block)> {
        let ret = sig
            .ret
            .as_ref()
            .map(|t| self.check_type(t.span, &t.item))
            .transpose()?
            .unwrap_or(Type::Builtin(BuiltinType::Unit));
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
                    .unwrap_or(Type::Builtin(BuiltinType::Unit));
                self.insert(&mut local, &p.item.name, typ.clone());
                Ok(typ)
            })
            .collect::<Out<_>>()?;
        let typ = FunctionType { params, ret };
        self.globals
            .insert(sig.name.clone(), Type::Function(Box::new(typ.clone())));
        Ok((typ, local))
    }

    fn block(&mut self, mut block: Block, stmts: &mut [Spanned<Stmt>]) -> Out<Type> {
        let typ = stmts
            .iter_mut()
            .map(|stmt| self.stmt(&mut block, stmt))
            .collect::<Out<Vec<_>>>()?
            .into_iter()
            .last()
            .unwrap_or(Type::Builtin(BuiltinType::Unit));
        for _ in 0..block.locals {
            self.locals.pop();
        }
        Ok(typ)
    }

    fn branch(&mut self, block: &Block, branch: &mut Branch) -> Out<Type> {
        self.check(
            branch.cond.span,
            &branch.cond.item,
            &Type::Builtin(BuiltinType::Bool),
        )?;
        self.block(block.local(), &mut branch.body)
    }

    fn check(&mut self, span: Span, expr: &Expr, want: &Type) -> Out<Option<Type>> {
        if let Expr::Number(..) = expr
            && let Type::Builtin(t) = want
            && t.is_number()
        {
            return Ok(None);
        }

        let (typ, got) = self.infer(expr)?;
        isa(span, &got, want)?;
        Ok(typ)
    }

    fn check_type(&mut self, span: Span, expr: &Expr) -> Out<Type> {
        self.check(span, expr, &Type::Builtin(BuiltinType::Type))
            .map(Option::unwrap)
    }

    fn infer(&mut self, expr: &Expr) -> Out<(Option<Type>, Type)> {
        Ok((
            None,
            match expr {
                Expr::Ident(ident) => self.ident(ident),
                Expr::BuiltinType(t) => {
                    return Ok((Some(Type::Builtin(*t)), Type::Builtin(BuiltinType::Type)));
                }
                Expr::Unit => Type::Builtin(BuiltinType::Unit),
                Expr::Number(..) => Type::Builtin(BuiltinType::F64),
                Expr::String(..) => Type::Builtin(BuiltinType::Str),
                Expr::Boolean(..) => Type::Builtin(BuiltinType::Bool),
                Expr::Call(f, args) => {
                    let span = f.span;
                    let typ = self.infer(&f.item)?.1;
                    let Type::Function(typ) = typ else {
                        return Err(Error::TypeMismatch {
                            span,
                            got: typ.to_string(),
                            want: "function".to_string(),
                        });
                    };
                    {
                        let got = args.len();
                        let want = typ.params.len();
                        if got != want {
                            return Err(Error::ArityMismatch { span, got, want });
                        }
                    }
                    args.iter()
                        .zip(typ.params.iter())
                        .try_for_each(|(got, want)| {
                            self.check(got.span, &got.item, want)?;
                            Ok(())
                        })?;
                    typ.ret
                }
                Expr::BinaryOp(lhs, op, rhs) => match op {
                    Sym::EqEq => {
                        let want = self.infer(&lhs.item)?.1;
                        self.check(rhs.span, &rhs.item, &want)?;
                        Type::Builtin(BuiltinType::Bool)
                    }

                    Sym::Lt | Sym::Gt | Sym::Le | Sym::Ge => {
                        let got = self.infer(&lhs.item)?.1;
                        if let Type::Builtin(t) = got
                            && t.is_number()
                        {
                            self.check(rhs.span, &rhs.item, &got)?;
                            Type::Builtin(BuiltinType::Bool)
                        } else {
                            return Err(Error::TypeMismatch {
                                span: lhs.span,
                                got: got.to_string(),
                                want: "number".to_string(),
                            });
                        }
                    }

                    Sym::Plus | Sym::Minus | Sym::Mul => {
                        let got = self.infer(&lhs.item)?.1;
                        if let Type::Builtin(t) = got
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

                    Sym::LParen
                    | Sym::RParen
                    | Sym::LBrace
                    | Sym::RBrace
                    | Sym::Comma
                    | Sym::Colon
                    | Sym::Eq => unreachable!(),
                },
            },
        ))
    }

    fn ident(&self, ident: &Ident) -> Type {
        match ident {
            Ident::Id(n) => self.globals.get(n),
            Ident::Idx(i) => self.locals.get(*i),
        }
        .cloned()
        .unwrap()
    }

    fn insert(&mut self, block: &mut Block, name: &Ident, typ: Type) {
        match name {
            Ident::Id(n) => {
                self.globals.insert(n.clone(), typ);
            }
            Ident::Idx(i) => {
                self.locals.insert(*i, typ);
                block.locals += 1;
            }
        }
    }
}

struct Block {
    ret: Type,
    locals: usize,
}

impl Block {
    fn func(ret: Type) -> Self {
        Self { ret, locals: 0 }
    }

    fn local(&self) -> Self {
        Self {
            ret: self.ret.clone(),
            locals: 0,
        }
    }
}

fn isa(span: Span, got: &Type, want: &Type) -> Out<()> {
    match (got, want) {
        (Type::Builtin(a), Type::Builtin(b)) if a == b => Ok(()),
        (Type::Function(a), Type::Function(b)) if a.params.len() == b.params.len() => {
            a.params
                .iter()
                .zip(b.params.iter())
                .try_for_each(|(a, b)| isa(span, a, b))?;
            isa(span, &a.ret, &b.ret)
        }
        _ => {
            let got = got.to_string();
            let want = want.to_string();
            Err(Error::TypeMismatch { span, got, want })
        }
    }
}
