use std::collections::HashMap;
use std::mem::take;

use crate::semantics::{Func, Type};
use crate::syntax::parse::Sym;
use crate::syntax::{Branch, BuiltinType, Expr, Name, Shadowed, Sig, Stmt};
use crate::{Error, Out, Span, Spanned};

#[derive(Default)]
pub(crate) struct Checker {
    globals: HashMap<Name, Type>,
    locals: HashMap<Name, Type>,
    fns: HashMap<Name, Func>,
}

impl Checker {
    pub(crate) fn file(mut self, file: &mut [Spanned<Stmt>]) -> Out<HashMap<Name, Func>> {
        let mut block = Block::global();
        file.iter_mut().try_for_each(|stmt| {
            self.stmt(&mut block, stmt)?;
            Ok(())
        })?;
        debug_assert!(self.locals.is_empty());
        Ok(self.fns)
    }

    fn stmt(&mut self, block: &mut Block, stmt: &mut Spanned<Stmt>) -> Out<Type> {
        Ok(match &mut stmt.item {
            Stmt::Func { sig, body, .. } => {
                let local = self.sig(block, sig)?;
                let typ = self.block(local, body)?;
                let old = self.fns.insert(
                    sig.name.clone(),
                    Func {
                        params: sig.params.iter().map(|p| p.item.name.clone()).collect(),
                        body: take(body),
                    },
                );
                debug_assert!(old.is_none());
                typ
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
            .collect::<Out<_>>()?;
        self.insert(
            block,
            sig.name.clone(),
            Type::FunctionType(params, Box::new(ret)),
        );
        Ok(local)
    }

    fn block(&mut self, mut block: Block, stmts: &mut [Spanned<Stmt>]) -> Out<Type> {
        let typ = stmts
            .iter_mut()
            .map(|stmt| self.stmt(&mut block, stmt))
            .collect::<Out<Vec<_>>>()?
            .into_iter()
            .last()
            .unwrap_or(Type::BuiltinType(BuiltinType::Unit));
        block.shadowed.clear(&mut self.locals);
        Ok(typ)
    }

    fn branch(&mut self, block: &Block, branch: &mut Branch) -> Out<Type> {
        self.check(
            branch.cond.span,
            &branch.cond.item,
            &Type::BuiltinType(BuiltinType::Bool),
        )?;
        self.block(block.local(), &mut branch.body)
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
                Expr::Unit => Type::BuiltinType(BuiltinType::Unit),
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

                    Sym::Assign
                    | Sym::LParen
                    | Sym::RParen
                    | Sym::LBrace
                    | Sym::RBrace
                    | Sym::Comma
                    | Sym::Eq => unreachable!(),
                },
            },
        ))
    }

    fn insert(&mut self, block: &mut Block, name: Name, typ: Type) {
        if block.local {
            return block
                .shadowed
                .push(name.clone(), self.locals.insert(name, typ));
        }
        self.globals.insert(name, typ);
    }
}

struct Block {
    ret: Type,
    local: bool,
    shadowed: Shadowed<Name, Type>,
}

impl Block {
    fn global() -> Self {
        Self {
            ret: Type::BuiltinType(BuiltinType::Unit),
            local: false,
            shadowed: Default::default(),
        }
    }

    fn func(ret: Type) -> Self {
        Self {
            ret,
            local: true,
            shadowed: Default::default(),
        }
    }

    fn local(&self) -> Self {
        Self {
            ret: self.ret.clone(),
            local: true,
            shadowed: Default::default(),
        }
    }
}

fn isa(span: Span, got: &Type, want: &Type) -> Out<()> {
    match (got, want) {
        (Type::BuiltinType(a), Type::BuiltinType(b)) if a == b => Ok(()),
        (Type::FunctionType(xs, x), Type::FunctionType(ys, y)) if xs.len() == ys.len() => {
            xs.iter()
                .zip(ys.iter())
                .try_for_each(|(a, b)| isa(span, a, b))?;
            isa(span, x, y)
        }
        _ => {
            let got = got.to_string();
            let want = want.to_string();
            Err(Error::TypeMismatch { span, got, want })
        }
    }
}
