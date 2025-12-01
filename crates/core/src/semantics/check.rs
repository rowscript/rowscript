use std::collections::HashMap;
use std::mem::take;

use crate::semantics::{BuiltinType, Float, Func, FunctionType, Globals, Integer, Static, Type};
use crate::syntax::parse::Sym;
use crate::syntax::{Branch, Def, Expr, File, Id, Ident, Sig, Stmt};
use crate::{Error, Out, Span, Spanned};

#[derive(Default)]
pub(crate) struct Checker {
    globals: HashMap<Id, Type>,
    locals: Vec<Type>,
    gs: Globals,
}

impl Checker {
    pub(crate) fn file(mut self, file: &mut File) -> Out<Globals> {
        let mut funcs = Vec::default();
        let mut statics = Vec::default();

        file.decls.iter_mut().try_for_each(|decl| {
            let name = &decl.item.name;
            match &mut decl.item.sig {
                Sig::Func { params, ret } => {
                    let span = ret.as_ref().map(|s| s.span).unwrap_or(decl.span);
                    let ret = ret
                        .as_mut()
                        .map(|t| self.check_type(t.span, &mut t.item))
                        .transpose()?
                        .unwrap_or(Type::Builtin(BuiltinType::Unit));
                    let params = params
                        .iter_mut()
                        .map(|p| {
                            Ok(p.item
                                .typ
                                .as_mut()
                                .map(|t| self.check_type(t.span, &mut t.item))
                                .transpose()?
                                .unwrap_or(Type::Builtin(BuiltinType::Unit)))
                        })
                        .collect::<Out<_>>()?;
                    let f = FunctionType { params, ret };
                    let got = Type::Function(Box::new(f.clone()));
                    if file.main.as_ref() == Some(name) {
                        isa(span, &got, &Type::main())?;
                    }
                    funcs.push(f);
                    self.globals.insert(name.clone(), got);
                }
                Sig::Static { typ } => {
                    let t = self.check_type(typ.span, &mut typ.item)?;
                    statics.push(t.clone());
                    self.globals.insert(name.clone(), t);
                }
                Sig::Struct { members } => {
                    members.iter_mut().try_for_each(|m| {
                        self.check_type(m.span, &mut m.item.typ.item)?;
                        Ok(())
                    })?;
                    // TODO: Member types inserted into the global context.
                    self.globals
                        .insert(name.clone(), Type::Struct(name.clone()));
                }
            }
            Ok(())
        })?;

        let mut funcs = funcs.into_iter();
        let mut statics = statics.into_iter();

        file.decls
            .iter_mut()
            .try_for_each(|decl| match &mut decl.item.def {
                Def::Func { body } => {
                    let FunctionType { params, ret } = funcs.next().unwrap();
                    let mut local = Block::func(ret.clone());
                    params.iter().enumerate().for_each(|(i, p)| {
                        self.insert(&mut local, i, p.clone());
                    });
                    let got = self.block(local, body)?;
                    isa(decl.span, &got, &ret)?;
                    let old = self.gs.fns.insert(
                        decl.item.name.clone(),
                        Spanned {
                            span: decl.span,
                            item: Func {
                                typ: FunctionType { params, ret },
                                body: take(body),
                            },
                        },
                    );
                    debug_assert!(old.is_none());
                    Ok(())
                }
                Def::Static { rhs } => {
                    let typ = statics.next().unwrap();
                    self.check(rhs.span, &mut rhs.item, &typ)?;
                    self.gs.statics.insert(
                        decl.item.name.clone(),
                        Spanned {
                            span: decl.span,
                            item: Static {
                                typ,
                                expr: rhs.clone(),
                            },
                        },
                    );
                    Ok(())
                }
                Def::Struct => Ok(()),
            })?;
        debug_assert!(self.locals.is_empty());
        Ok(self.gs)
    }

    fn stmt(&mut self, block: &mut Block, stmt: &mut Spanned<Stmt>) -> Out<Type> {
        Ok(match &mut stmt.item {
            Stmt::Expr(e) => self.infer(stmt.span, e)?.1,
            Stmt::Assign { name, typ, rhs, .. } => {
                let rhs_type = typ
                    .as_mut()
                    .map(|t| {
                        let want = self.check_type(t.span, &mut t.item)?;
                        self.check(rhs.span, &mut rhs.item, &want)?;
                        Ok(want)
                    })
                    .unwrap_or_else(|| Ok(self.infer(rhs.span, &mut rhs.item)?.1))?;
                self.insert(block, name.item.as_idx(), rhs_type.clone());
                *typ = Some(Spanned {
                    span: typ.as_ref().map(|t| t.span).unwrap_or(name.span),
                    item: rhs_type.to_expr(name.span),
                });
                rhs_type
            }
            Stmt::Update { name, rhs } => {
                let t = self.ident(&name.item);
                self.check(rhs.span, &mut rhs.item, &t)?;
                t
            }
            Stmt::Return(e) => e
                .as_mut()
                .map(|e| {
                    self.check(e.span, &mut e.item, &block.ret)
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
            &mut branch.cond.item,
            &Type::Builtin(BuiltinType::Bool),
        )?;
        self.block(block.local(), &mut branch.body)
    }

    fn check(&mut self, span: Span, expr: &mut Expr, want: &Type) -> Out<Option<Type>> {
        if let Expr::Integer(Integer::I64(n)) = expr
            && let Type::Builtin(t) = want
            && t.is_integer()
            && let Some(n) = t.narrow_integer(*n)
        {
            *expr = Expr::Integer(n);
            return Ok(None);
        }

        if let Expr::Float(Float::F64(n)) = expr
            && let Type::Builtin(t) = want
            && t.is_float()
        {
            *expr = Expr::Float(t.narrow_float(*n));
            return Ok(None);
        }

        let (typ, got) = self.infer(span, expr)?;
        isa(span, &got, want)?;
        Ok(typ)
    }

    fn check_type(&mut self, span: Span, expr: &mut Expr) -> Out<Type> {
        self.check(span, expr, &Type::Builtin(BuiltinType::Type))
            .map(Option::unwrap)
    }

    fn infer(&mut self, span: Span, expr: &mut Expr) -> Out<(Option<Type>, Type)> {
        Ok((
            None,
            match expr {
                Expr::Ident(ident) => self.ident(ident),
                Expr::BuiltinType(t) => {
                    return Ok((Some(Type::Builtin(*t)), Type::Builtin(BuiltinType::Type)));
                }
                Expr::RefType(t) => {
                    let t = self.check_type(t.span, &mut t.item)?;
                    return Ok((
                        Some(Type::Ref(Box::new(t))),
                        Type::Builtin(BuiltinType::Type),
                    ));
                }
                Expr::Unit => Type::Builtin(BuiltinType::Unit),
                Expr::Integer(n) => {
                    debug_assert!(matches!(n, Integer::I64(..)));
                    Type::Builtin(BuiltinType::I64)
                }
                Expr::Float(n) => {
                    debug_assert!(matches!(n, Float::F64(..)));
                    Type::Builtin(BuiltinType::F64)
                }
                Expr::String(..) => Type::Builtin(BuiltinType::Str),
                Expr::Boolean(..) => Type::Builtin(BuiltinType::Bool),
                Expr::Call(f, args) => {
                    let typ = self.infer(f.span, &mut f.item)?.1;
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
                    args.iter_mut()
                        .zip(typ.params.iter())
                        .try_for_each(|(got, want)| {
                            self.check(got.span, &mut got.item, want)?;
                            Ok(())
                        })?;
                    typ.ret
                }
                Expr::BinaryOp(lhs, op, typ, rhs) => match op {
                    Sym::EqEq => {
                        let got = self.infer(lhs.span, &mut lhs.item)?.1;
                        self.check(rhs.span, &mut rhs.item, &got)?;
                        *typ = Some(got);
                        Type::Builtin(BuiltinType::Bool)
                    }
                    Sym::Lt | Sym::Gt | Sym::Le | Sym::Ge => {
                        let got = self.infer(lhs.span, &mut lhs.item)?.1;
                        if let Type::Builtin(t) = got
                            && (t.is_integer() || t.is_float())
                        {
                            self.check(rhs.span, &mut rhs.item, &got)?;
                            *typ = Some(got);
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
                        let got = self.infer(lhs.span, &mut lhs.item)?.1;
                        if let Type::Builtin(t) = got
                            && (t.is_integer() || t.is_float())
                        {
                            self.check(rhs.span, &mut rhs.item, &got)?;
                            *typ = Some(got.clone());
                            got
                        } else {
                            return Err(Error::TypeMismatch {
                                span: lhs.span,
                                got: got.to_string(),
                                want: "number".to_string(),
                            });
                        }
                    }
                    _ => unreachable!(),
                },
                Expr::UnaryOp(x, op, typ) => match op {
                    Sym::Mul => {
                        let got = self.infer(x.span, &mut x.item)?.1;
                        let Type::Ref(got) = got else {
                            return Err(Error::TypeMismatch {
                                span,
                                got: got.to_string(),
                                want: "reference type".to_string(),
                            });
                        };
                        *typ = Some(*got.clone());
                        *got
                    }
                    _ => unreachable!(),
                },
                Expr::New(t) => {
                    let typ = self.check_type(t.span, &mut t.item)?;
                    Type::Function(Box::new(FunctionType {
                        params: Box::new([typ.clone()]), // TODO: accurate arity
                        ret: Type::Ref(Box::new(typ)),
                    }))
                }
                Expr::Ref(..) => unreachable!(),
            },
        ))
    }

    fn ident(&self, ident: &Ident) -> Type {
        match ident {
            Ident::Id(n) => self.globals.get(n),
            Ident::Idx(i) => self.locals.get(*i),
            Ident::Builtin(b) => return b.r#type(),
        }
        .cloned()
        .unwrap()
    }

    fn insert(&mut self, block: &mut Block, idx: usize, typ: Type) {
        self.locals.insert(idx, typ);
        block.locals += 1;
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
        (Type::Ref(a), Type::Ref(b)) => isa(span, a, b),
        _ => {
            let got = got.to_string();
            let want = want.to_string();
            Err(Error::TypeMismatch { span, got, want })
        }
    }
}
