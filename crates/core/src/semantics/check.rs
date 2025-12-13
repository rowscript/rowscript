use std::collections::HashMap;
use std::iter::once;
use std::mem::take;

use ustr::UstrMap;

use crate::semantics::{
    BuiltinType, Float, Func, FuncType, GenericParam, Globals, Integer, Static, Struct, StructType,
    Type,
};
use crate::syntax::parse::Sym;
use crate::syntax::{
    Access, Branch, Def, Expr, File, FuncSig, Id, Ident, Object, Sig, Stmt, TypeParam,
};
use crate::{Error, Out, Span, Spanned};

#[derive(Default)]
pub(crate) struct Checker {
    globals: HashMap<Id, Inferred>,
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
                    let body = Type::Function(Box::new(f.clone()));
                    let got = type_params
                        .clone()
                        .into_iter()
                        .rfold(body.clone(), |ret, param| Type::Generic {
                            param: Box::new(param),
                            ret: Box::new(ret),
                        });
                    if file.main.as_ref() == Some(&sig.name) {
                        isa(span, &got, &Type::main())?;
                    }
                    fns.push((sig.name.clone(), type_params, f));
                    self.globals.insert(
                        sig.name.clone(),
                        Inferred {
                            applicable: Some(body),
                            typ: got,
                        },
                    );
                }
                Sig::Static { name, typ } => {
                    let t = self.check_type(typ.span, &mut typ.item)?;
                    statics.push((name.clone(), t.clone()));
                    self.globals
                        .insert(name.clone(), Inferred::non_applicable(t));
                }
                Sig::Struct {
                    name,
                    type_params,
                    members,
                } => {
                    let i = self.infer_with_type_params(type_params, |s| {
                        let members = members
                            .iter_mut()
                            .map(|m| {
                                let t = s.check_type(m.span, &mut m.item.typ.item)?;
                                Ok((m.item.name, t))
                            })
                            .collect::<Out<Vec<_>>>()?;
                        let t = Type::Struct(StructType {
                            name: name.clone(),
                            members: members.iter().map(|(.., typ)| typ.clone()).collect(),
                        });
                        s.gs.structs.insert(
                            name.clone(),
                            Struct {
                                members: members
                                    .into_iter()
                                    .enumerate()
                                    .map(|(i, (name, ..))| (name, i))
                                    .collect(),
                                ..Default::default()
                            },
                        );
                        Ok(t)
                    })?;
                    self.globals.insert(name.clone(), i);
                }
                Sig::Extends {
                    type_params,
                    target,
                    methods,
                } => {
                    let type_params = self.type_params(type_params)?;
                    self.with_type_params(&type_params, |s| {
                        let got = s.check_type(target.span, &mut target.item)?;
                        let Type::Struct(StructType { name, .. }) = got else {
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
                        extends.push((name, methods));
                        Ok(())
                    })?;
                }
            };
            Ok(())
        })?;

        debug_assert!(self.type_locals.is_empty());

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

    fn func_sig(&mut self, sig: &mut FuncSig) -> Out<(Vec<GenericParam>, FuncType)> {
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
            Stmt::Expr(e) => self.infer(stmt.span, e)?.typ,
            Stmt::Assign { name, typ, rhs, .. } => {
                let rhs_type = typ
                    .as_mut()
                    .map(|t| {
                        let want = self.check_type(t.span, &mut t.item)?;
                        self.check(rhs.span, &mut rhs.item, &want)?;
                        Ok(want)
                    })
                    .unwrap_or_else(|| Ok(self.infer(rhs.span, &mut rhs.item)?.typ))?;
                self.insert(block, name.item.as_idx(), rhs_type.clone());
                *typ = Some(Spanned {
                    span: typ.as_ref().map(|t| t.span).unwrap_or(name.span),
                    item: rhs_type.to_expr(name.span),
                });
                rhs_type
            }
            Stmt::Update { name, rhs } => {
                let want = self.ident(&name.item)?.typ;
                self.check(rhs.span, &mut rhs.item, &want)?;
                want
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

        let got = self.infer(span, expr)?;
        isa(span, &got.typ, want)?;
        Ok(got.applicable)
    }

    fn check_type(&mut self, span: Span, expr: &mut Expr) -> Out<Type> {
        self.check(span, expr, &Type::Builtin(BuiltinType::Type))
            .map(Option::unwrap)
    }

    fn infer(&mut self, span: Span, expr: &mut Expr) -> Out<Inferred> {
        Ok(Inferred::non_applicable(match expr {
            Expr::Ident(ident) => return self.ident(ident),
            Expr::BuiltinType(t) => return Ok(Inferred::from(Type::Builtin(*t))),
            Expr::RefType(t) => {
                let t = self.check_type(t.span, &mut t.item)?;
                return Ok(Inferred::from(Type::Ref(Box::new(t))));
            }
            Expr::Apply(t, args) => {
                let Inferred { applicable, typ } = self.infer(t.span, &mut t.item)?;
                let Type::Generic { param, mut ret } = typ else {
                    return Err(Error::TypeMismatch {
                        span: t.span,
                        got: typ.to_string(),
                        want: "generic".to_string(),
                    });
                };
                let mut body = applicable.unwrap();
                args.iter_mut().try_for_each(|arg| {
                    let arg = self.check(arg.span, &mut arg.item, &param.constr)?.unwrap();
                    body.apply(param.typ.clone(), arg.clone());
                    ret.apply(param.typ.clone(), arg);
                    Ok(())
                })?;
                return Ok(Inferred {
                    applicable: Some(body),
                    typ: *ret,
                });
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
                let got = self.infer(f.span, &mut f.item)?.typ;
                let Type::Function(typ) = got else {
                    return Err(Error::TypeMismatch {
                        span,
                        got: got.to_string(),
                        want: "function".to_string(),
                    });
                };
                self.check_args(span, args.len(), args.iter_mut(), &typ.params)?;
                typ.ret
            }
            Expr::BinaryOp(lhs, op, typ, rhs) => match op {
                Sym::EqEq => {
                    let got = self.infer(lhs.span, &mut lhs.item)?.typ;
                    self.check(rhs.span, &mut rhs.item, &got)?;
                    *typ = Some(got);
                    Type::Builtin(BuiltinType::Bool)
                }
                Sym::Lt | Sym::Gt | Sym::Le | Sym::Ge => {
                    let got = self.infer(lhs.span, &mut lhs.item)?.typ;
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
                    let got = self.infer(lhs.span, &mut lhs.item)?.typ;
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
                    let got = self.infer(x.span, &mut x.item)?.typ;
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
                let Type::Struct(StructType { name, members }) = &got else {
                    return Err(Error::TypeMismatch {
                        span: t.span,
                        got: got.to_string(),
                        want: "struct".to_string(),
                    });
                };
                let mut indexes = self.gs.structs.get(name).unwrap().members.clone();
                let Object::Unordered(args) = unordered else {
                    unreachable!()
                };
                let mut ordered = Vec::with_capacity(indexes.len());
                take(args).into_iter().try_for_each(|(name, mut arg)| {
                    let i = indexes.remove(&name.item).ok_or(Error::UndefName {
                        span: name.span,
                        name: name.item,
                        is_member: true,
                    })?;
                    let want = &members[i];
                    self.check(arg.span, &mut arg.item, want)?;
                    ordered.insert(i, arg.item);
                    Ok(())
                })?;
                if !indexes.is_empty() {
                    return Err(Error::MissingMembers(
                        span,
                        indexes.keys().cloned().collect(),
                    ));
                }
                *unordered = Object::Ordered(ordered);
                got
            }
            Expr::Access(a, acc) => {
                let StructType { name, members } = self.infer_struct(a.span, &mut a.item)?;
                let Access::Named(m) = acc else {
                    unreachable!()
                };
                let Some(i) = self.gs.structs.get(&name).unwrap().members.get(&m.item) else {
                    return Err(Error::UndefName {
                        span: m.span,
                        name: m.item,
                        is_member: true,
                    });
                };
                *acc = Access::Indexed(*i);
                members[*i].clone()
            }
            Expr::Method {
                callee,
                target,
                method,
                args,
            } => {
                let StructType { name, .. } = self.infer_struct(callee.span, &mut callee.item)?;
                let Ident::Id(m) = &method.item else {
                    unreachable!()
                };
                let Some((i, f)) = self.gs.structs.get(&name).unwrap().extends.get(&m.raw()) else {
                    return Err(Error::UndefName {
                        span: method.span,
                        name: m.raw(),
                        is_member: true,
                    });
                };
                let got = 1 + args.len();
                let args = once(callee.as_mut()).chain(args.iter_mut());
                *target = Some(name);
                method.item = Ident::Idx(*i);
                let typ = f.clone();
                self.check_args(span, got, args, &typ.params)?;
                typ.ret
            }
            Expr::ThisType(t) => return self.infer(span, t),
            Expr::StructType(..) | Expr::Ref(..) | Expr::Struct(..) => unreachable!(),
        }))
    }

    fn infer_struct(&mut self, span: Span, expr: &mut Expr) -> Out<StructType> {
        let got = self.infer(span, expr)?.typ;
        let Type::Struct(t) = got else {
            return Err(Error::TypeMismatch {
                span,
                got: got.to_string(),
                want: "struct".to_string(),
            });
        };
        Ok(t)
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

    fn ident(&self, ident: &Ident) -> Out<Inferred> {
        Ok(match ident {
            Ident::Id(n) => self.globals.get(n).cloned().unwrap(),
            Ident::Idx(i) => Inferred::non_applicable(self.locals.get(*i).unwrap().clone()),
            Ident::Builtin(b) => Inferred::non_applicable(b.r#type()),
            Ident::Type(n) => self
                .type_locals
                .get(n)
                .cloned()
                .map(|typ| Inferred {
                    applicable: Some(Type::Id(n.clone())),
                    typ,
                })
                .unwrap(),
        })
    }

    fn insert(&mut self, block: &mut Block, idx: usize, typ: Type) {
        self.locals.insert(idx, typ);
        block.locals += 1;
    }

    fn type_params(&mut self, type_params: &mut [Spanned<TypeParam>]) -> Out<Vec<GenericParam>> {
        type_params
            .iter_mut()
            .map(|p| {
                self.check_type(p.item.constr.span, &mut p.item.constr.item)
                    .map(|constr| GenericParam {
                        variadic: p.item.variadic,
                        typ: p.item.typ.as_id().clone(),
                        constr,
                    })
            })
            .collect()
    }

    fn with_type_params<R, F: FnOnce(&mut Self) -> R>(
        &mut self,
        type_params: &[GenericParam],
        f: F,
    ) -> R {
        for p in type_params {
            let old = self.type_locals.insert(p.typ.clone(), p.constr.clone());
            debug_assert!(old.is_none());
        }
        let ret = f(self);
        for p in type_params {
            self.type_locals.remove(&p.typ);
        }
        ret
    }

    fn infer_with_type_params<F: FnOnce(&mut Self) -> Out<Type>>(
        &mut self,
        type_params: &mut [Spanned<TypeParam>],
        f: F,
    ) -> Out<Inferred> {
        let ps = self.type_params(type_params)?;
        let applicable = Some(self.with_type_params(&ps, f)?);
        let typ = ps
            .into_iter()
            .rfold(Type::Builtin(BuiltinType::Type), |ret, param| {
                Type::Generic {
                    param: Box::new(param),
                    ret: Box::new(ret),
                }
            });
        Ok(Inferred { applicable, typ })
    }
}

#[derive(Debug, Clone)]
struct Inferred {
    applicable: Option<Type>,
    typ: Type,
}

impl Inferred {
    fn non_applicable(typ: Type) -> Self {
        Self {
            applicable: None,
            typ,
        }
    }
}

impl From<Type> for Inferred {
    fn from(applicable: Type) -> Self {
        Self {
            applicable: Some(applicable),
            typ: Type::Builtin(BuiltinType::Type),
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
        (Type::Ref(a), Type::Ref(b)) => isa(span, a, b),
        (Type::Struct(a), Type::Struct(b)) if a.name == b.name => Ok(()),
        (Type::Id(a), Type::Id(b)) if a == b => Ok(()),
        _ => {
            let got = got.to_string();
            let want = want.to_string();
            Err(Error::TypeMismatch { span, got, want })
        }
    }
}

#[derive(Default)]
struct Applier(HashMap<Id, Type>);

impl Applier {
    fn apply(&mut self, t: &mut Type) {
        match t {
            Type::Builtin(..) => (),
            Type::Function(f) => {
                f.params.iter_mut().for_each(|p| self.apply(p));
                self.apply(&mut f.ret);
            }
            Type::Ref(x) => self.apply(x),
            Type::Struct(StructType { members, .. }) => {
                members.iter_mut().for_each(|x| self.apply(x))
            }
            Type::Generic { param, ret } => {
                self.apply(&mut param.constr);
                self.apply(ret);
            }
            Type::Id(id) => *t = self.0.get(id).cloned().unwrap(),
        }
    }
}

impl Type {
    fn apply(&mut self, id: Id, typ: Self) {
        Applier(HashMap::from([(id, typ)])).apply(self)
    }
}
