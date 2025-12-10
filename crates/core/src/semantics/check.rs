use std::collections::HashMap;
use std::iter::once;
use std::mem::take;

use ustr::UstrMap;

use crate::semantics::{
    BuiltinType, Float, Func, FuncType, Globals, Integer, Static, Struct, Type,
};
use crate::syntax::parse::Sym;
use crate::syntax::{
    Access, Branch, Def, Expr, File, FuncSig, Id, Ident, Object, Param, Sig, Stmt,
};
use crate::{Error, Out, Span, Spanned};

#[derive(Default)]
pub(crate) struct Checker {
    globals: HashMap<Id, Kind>,
    locals: Vec<Type>,
    type_locals: HashMap<Id, Type>,
    gs: Globals,
}

impl Checker {
    pub(crate) fn file(mut self, file: &mut File) -> Out<Globals> {
        let mut fns = Vec::default();
        let mut statics = Vec::default();
        let mut extends = Vec::default();

        file.decls.iter_mut().try_for_each(|decl| {
            match &mut decl.item.sig {
                Sig::Func(sig) => {
                    let span = sig.ret.as_ref().map(|s| s.span).unwrap_or(decl.span);
                    let (type_params, f) = self.func_sig(sig)?;
                    let got = type_params.clone().into_iter().rfold(
                        Type::Function(Box::new(f.clone())),
                        |body, (name, typ)| Type::Generic {
                            name,
                            typ: Box::new(typ),
                            body: Box::new(body),
                        },
                    );
                    if file.main.as_ref() == Some(&sig.name) {
                        isa(span, &got, &Type::main())?;
                    }
                    fns.push((sig.name.clone(), type_params, f));
                    self.globals.insert(sig.name.clone(), Kind::ValueLevel(got));
                }
                Sig::Static { name, typ } => {
                    let t = self.check_type(typ.span, &mut typ.item)?;
                    statics.push((name.clone(), t.clone()));
                    self.globals.insert(name.clone(), Kind::ValueLevel(t));
                }
                Sig::Struct {
                    name,
                    type_params,
                    members,
                } => {
                    let t = self.infer_with_type_params(type_params, |s| {
                        let members = members
                            .iter_mut()
                            .enumerate()
                            .map(|(i, m)| {
                                let t = s.check_type(m.span, &mut m.item.typ.item)?;
                                Ok((m.item.name, (i, t)))
                            })
                            .collect::<Out<_>>()?;
                        s.gs.structs.insert(
                            name.clone(),
                            Struct {
                                members,
                                ..Default::default()
                            },
                        );
                        Ok(Type::Struct(name.clone()))
                    })?;
                    self.globals.insert(name.clone(), Kind::TypeLevel(t));
                }
                Sig::Extends {
                    type_params,
                    target,
                    methods,
                } => {
                    let type_params = self.type_params(type_params)?;
                    self.with_type_params(&type_params, |s| {
                        let got = s.check_type(target.span, &mut target.item)?;
                        let Type::Struct(id) = got else {
                            return Err(Error::TypeMismatch {
                                span: target.span,
                                got: got.to_string(),
                                want: "struct".to_string(),
                            });
                        };
                        let methods = methods
                            .iter_mut()
                            .map(|m| s.func_sig(&mut m.item.sig))
                            .collect::<Out<Vec<_>>>()?;
                        extends.push((id, methods));
                        Ok(())
                    })?;
                }
            };
            Ok(())
        })?;

        let mut fns = fns.into_iter();
        let mut statics = statics.into_iter();
        let mut extends = extends.into_iter();

        file.decls
            .iter_mut()
            .try_for_each(|decl| match &mut decl.item.def {
                Def::Func { body } => {
                    let (name, type_params, typ) = fns.next().unwrap();
                    self.with_type_params(&type_params, |s| {
                        let mut local = Block::func(typ.ret.clone());
                        typ.params
                            .clone()
                            .into_iter()
                            .enumerate()
                            .for_each(|(i, p)| {
                                s.insert(&mut local, i, p);
                            });
                        let got = s.block(local, body)?;
                        isa(decl.span, &got, &typ.ret)?;
                        let old = s.gs.fns.insert(
                            name,
                            Spanned {
                                span: decl.span,
                                item: Func {
                                    typ,
                                    body: take(body),
                                },
                            },
                        );
                        debug_assert!(old.is_none());
                        Ok(())
                    })
                }
                Def::Static { rhs } => {
                    let (name, typ) = statics.next().unwrap();
                    self.check(rhs.span, &mut rhs.item, &typ)?;
                    self.gs.statics.insert(
                        name,
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
                Def::Extends { bodies } => {
                    let Sig::Extends { methods, .. } = &decl.item.sig else {
                        unreachable!()
                    };
                    let (target, types) = extends.next().unwrap();
                    let mut checked_extends = UstrMap::default();
                    let mut checked_bodies = Vec::default();
                    methods
                        .iter()
                        .zip(types.into_iter())
                        .zip(bodies.iter_mut())
                        .enumerate()
                        .try_for_each(|(i, ((sig, (type_params, typ)), body))| {
                            self.with_type_params(&type_params, |s| {
                                let mut local = Block::func(typ.ret.clone());
                                typ.params
                                    .clone()
                                    .into_iter()
                                    .enumerate()
                                    .for_each(|(i, p)| {
                                        s.insert(&mut local, i, p);
                                    });
                                let got = s.block(local, body)?;
                                isa(decl.span, &got, &typ.ret)?;
                                checked_extends.insert(sig.item.sig.name.raw(), (i, typ));
                                checked_bodies.push(take(body));
                                Ok(())
                            })
                        })?;
                    let s = self.gs.structs.get_mut(&target).unwrap();
                    s.extends = checked_extends;
                    s.bodies = checked_bodies;
                    Ok(())
                }
            })?;
        debug_assert!(self.locals.is_empty());
        Ok(self.gs)
    }

    fn func_sig(&mut self, sig: &mut FuncSig) -> Out<(Vec<(Ident, Type)>, FuncType)> {
        let type_params = self.type_params(&mut sig.type_params)?;
        let f = self.with_type_params(&type_params, |s| {
            let ret = sig
                .ret
                .as_mut()
                .map(|t| s.check_type(t.span, &mut t.item))
                .transpose()?
                .unwrap_or(Type::Builtin(BuiltinType::Unit));
            let params = sig
                .params
                .iter_mut()
                .map(|p| s.check_type(p.item.typ.span, &mut p.item.typ.item))
                .collect::<Out<_>>()?;
            Ok(FuncType { params, ret })
        })?;
        Ok((type_params, f))
    }

    fn stmt(&mut self, block: &mut Block, stmt: &mut Spanned<Stmt>) -> Out<Type> {
        Ok(match &mut stmt.item {
            Stmt::Expr(e) => self.infer(stmt.span, e)?.value_level(),
            Stmt::Assign { name, typ, rhs, .. } => {
                let rhs_type = typ
                    .as_mut()
                    .map(|t| {
                        let want = self.check_type(t.span, &mut t.item)?;
                        self.check(rhs.span, &mut rhs.item, &want)?;
                        Ok(want)
                    })
                    .unwrap_or_else(|| Ok(self.infer(rhs.span, &mut rhs.item)?.value_level()))?;
                self.insert(block, name.item.as_idx(), rhs_type.clone());
                *typ = Some(Spanned {
                    span: typ.as_ref().map(|t| t.span).unwrap_or(name.span),
                    item: rhs_type.to_expr(name.span),
                });
                rhs_type
            }
            Stmt::Update { name, rhs } => {
                let t = self.ident(&name.item)?.value_level();
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

    fn check(&mut self, span: Span, expr: &mut Expr, want: &Type) -> Out<Kind> {
        if let Expr::Integer(Integer::I64(n)) = expr
            && let Type::Builtin(t) = want
            && t.is_integer()
            && let Some(n) = t.narrow_integer(*n)
        {
            *expr = Expr::Integer(n);
            return Ok(Kind::ValueLevel(want.clone()));
        }

        if let Expr::Float(Float::F64(n)) = expr
            && let Type::Builtin(t) = want
            && t.is_float()
        {
            *expr = Expr::Float(t.narrow_float(*n));
            return Ok(Kind::ValueLevel(want.clone()));
        }

        let inferred = self.infer(span, expr)?;
        let got = match &inferred {
            Kind::ValueLevel(got) => got,
            Kind::TypeLevel(..) => &Type::Builtin(BuiltinType::Type),
        };
        isa(span, got, want)?;
        Ok(inferred)
    }

    fn check_type(&mut self, span: Span, expr: &mut Expr) -> Out<Type> {
        self.check(span, expr, &Type::Builtin(BuiltinType::Type))
            .map(Kind::type_level)
    }

    fn infer(&mut self, span: Span, expr: &mut Expr) -> Out<Kind> {
        Ok(Kind::ValueLevel(match expr {
            Expr::Ident(ident) => return self.ident(ident),
            Expr::BuiltinType(t) => return Ok(Kind::TypeLevel(Type::Builtin(*t))),
            Expr::RefType(t) => {
                let t = self.check_type(t.span, &mut t.item)?;
                return Ok(Kind::TypeLevel(Type::Ref(Box::new(t))));
            }
            Expr::Apply(..) => todo!("type application"),
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
                let typ = self.infer(f.span, &mut f.item)?.value_level();
                let Type::Function(typ) = typ else {
                    return Err(Error::TypeMismatch {
                        span,
                        got: typ.to_string(),
                        want: "function".to_string(),
                    });
                };
                self.check_args(span, args.len(), args.iter_mut(), &typ.params)?;
                typ.ret
            }
            Expr::BinaryOp(lhs, op, typ, rhs) => match op {
                Sym::EqEq => {
                    let got = self.infer(lhs.span, &mut lhs.item)?.value_level();
                    self.check(rhs.span, &mut rhs.item, &got)?;
                    *typ = Some(got);
                    Type::Builtin(BuiltinType::Bool)
                }
                Sym::Lt | Sym::Gt | Sym::Le | Sym::Ge => {
                    let got = self.infer(lhs.span, &mut lhs.item)?.value_level();
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
                    let got = self.infer(lhs.span, &mut lhs.item)?.value_level();
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
                    let got = self.infer(x.span, &mut x.item)?.value_level();
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
                Type::Function(Box::new(FuncType {
                    params: vec![typ.clone()], // TODO: accurate arity
                    ret: Type::Ref(Box::new(typ)),
                }))
            }
            Expr::Object(t, unordered) => {
                let got = self.check_type(t.span, &mut t.item)?;
                let Type::Struct(s) = &got else {
                    return Err(Error::TypeMismatch {
                        span: t.span,
                        got: got.to_string(),
                        want: "struct".to_string(),
                    });
                };
                let mut members = self.gs.structs.get(s).unwrap().members.clone();
                let Object::Unordered(args) = unordered else {
                    unreachable!()
                };
                let mut ordered = Vec::with_capacity(members.len());
                take(args).into_iter().try_for_each(|(name, mut arg)| {
                    let (i, typ) = members.remove(&name.item).ok_or(Error::UndefName {
                        span: name.span,
                        name: name.item,
                        is_member: true,
                    })?;
                    self.check(arg.span, &mut arg.item, &typ)?;
                    ordered.insert(i, arg.item);
                    Ok(())
                })?;
                if !members.is_empty() {
                    return Err(Error::MissingMembers(
                        span,
                        members.keys().cloned().collect(),
                    ));
                }
                *unordered = Object::Ordered(ordered);
                got
            }
            Expr::Access(a, acc) => {
                let s = self.infer_struct(a.span, &mut a.item)?;
                let Access::Named(name) = acc else {
                    unreachable!()
                };
                let Some((i, typ)) = self.gs.structs.get(&s).unwrap().members.get(&name.item)
                else {
                    return Err(Error::UndefName {
                        span: name.span,
                        name: name.item,
                        is_member: true,
                    });
                };
                *acc = Access::Indexed(*i);
                typ.clone()
            }
            Expr::Method {
                callee,
                target,
                method,
                args,
            } => {
                let s = self.infer_struct(callee.span, &mut callee.item)?;
                let Ident::Id(m) = &method.item else {
                    unreachable!()
                };
                let name = m.raw();
                let Some((i, f)) = self.gs.structs.get(&s).unwrap().extends.get(&name) else {
                    return Err(Error::UndefName {
                        span: method.span,
                        name,
                        is_member: true,
                    });
                };
                let got = 1 + args.len();
                let args = once(callee.as_mut()).chain(args.iter_mut());
                *target = Some(s);
                method.item = Ident::Idx(*i);
                let typ = f.clone();
                self.check_args(span, got, args, &typ.params)?;
                typ.ret
            }
            Expr::ThisType(t) => return self.infer(span, t),
            Expr::StructType(..) | Expr::Ref(..) | Expr::Struct(..) => unreachable!(),
        }))
    }

    fn infer_struct(&mut self, span: Span, expr: &mut Expr) -> Out<Id> {
        let got = self.infer(span, expr)?.value_level();
        let Type::Struct(s) = got else {
            return Err(Error::TypeMismatch {
                span,
                got: got.to_string(),
                want: "struct".to_string(),
            });
        };
        Ok(s)
    }

    fn check_args<'a, I: Iterator<Item = &'a mut Spanned<Expr>>>(
        &mut self,
        span: Span,
        got: usize,
        args: I,
        params: &[Type],
    ) -> Out<()> {
        let want = params.len();
        if got != want {
            return Err(Error::ArityMismatch { span, got, want });
        }
        args.zip(params.iter()).try_for_each(|(got, want)| {
            self.check(got.span, &mut got.item, want)?;
            Ok(())
        })
    }

    fn ident(&self, ident: &Ident) -> Out<Kind> {
        Ok(match ident {
            Ident::Id(n) => self.globals.get(n).cloned().unwrap(),
            Ident::Idx(i) => Kind::ValueLevel(self.locals.get(*i).unwrap().clone()),
            Ident::Builtin(b) => Kind::ValueLevel(b.r#type()),
            Ident::Type(n) => self
                .type_locals
                .get(n)
                .cloned()
                .map(Kind::TypeLevel)
                .unwrap(),
        })
    }

    fn insert(&mut self, block: &mut Block, idx: usize, typ: Type) {
        self.locals.insert(idx, typ);
        block.locals += 1;
    }

    fn type_params(&mut self, type_params: &mut [Spanned<Param>]) -> Out<Vec<(Ident, Type)>> {
        type_params
            .iter_mut()
            .map(|p| {
                self.check_type(p.item.typ.span, &mut p.item.typ.item)
                    .map(|t| (p.item.name.clone(), t))
            })
            .collect()
    }

    fn with_type_params<R, F: FnOnce(&mut Self) -> R>(
        &mut self,
        type_params: &[(Ident, Type)],
        f: F,
    ) -> R {
        for (name, typ) in type_params {
            let old = self.type_locals.insert(name.as_id().clone(), typ.clone());
            debug_assert!(old.is_none());
        }
        let ret = f(self);
        for (name, ..) in type_params {
            self.type_locals.remove(name.as_id());
        }
        debug_assert!(self.type_locals.is_empty());
        ret
    }

    fn infer_with_type_params<F: FnOnce(&mut Self) -> Out<Type>>(
        &mut self,
        type_params: &mut [Spanned<Param>],
        f: F,
    ) -> Out<Type> {
        let ps = self.type_params(type_params)?;
        let init = self.with_type_params(&ps, f)?;
        Ok(ps
            .into_iter()
            .rfold(init, |body, (name, typ)| Type::Generic {
                name,
                typ: Box::new(typ),
                body: Box::new(body),
            }))
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

#[derive(Clone)]
enum Kind {
    /// The expression is value-level, e.g. for `⊢ x : T`, the [`Type`] here represents `T`.
    ValueLevel(Type),
    /// The expression is type-level, e.g. for `⊢ T type`, the [`Type`] here represents `T`.
    TypeLevel(Type),
}

impl Kind {
    fn value_level(self) -> Type {
        if let Self::ValueLevel(typ) = self {
            return typ;
        }
        unreachable!()
    }

    fn type_level(self) -> Type {
        if let Self::TypeLevel(typ) = self {
            return typ;
        }
        unreachable!()
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
        (Type::Struct(a), Type::Struct(b)) if a == b => Ok(()),
        (Type::Generic { .. }, Type::Generic { .. }) => todo!(),
        _ => {
            let got = got.to_string();
            let want = want.to_string();
            Err(Error::TypeMismatch { span, got, want })
        }
    }
}
