use std::collections::HashMap;
use std::ops::ControlFlow;
use std::rc::Rc;
use std::slice::from_ref;

use crate::Spanned;
use crate::semantics::Globals;
use crate::syntax::parse::Sym;
use crate::syntax::{Access, Branch, Expr, Id, Ident, Object, Stmt};

pub(crate) struct Vm<'a> {
    gs: &'a Globals,
    statics: HashMap<Id, Expr>,
}

impl<'a> Vm<'a> {
    pub(crate) fn new(gs: &'a Globals) -> Self {
        Self {
            gs,
            statics: Default::default(),
        }
    }

    pub(crate) fn func(&mut self, f: &[Spanned<Stmt>], args: Vec<Expr>) -> Expr {
        let mut block = args.len();
        let mut frame = args;
        let e = self.block(&mut frame, &mut block, f).into_expr();
        debug_assert!(frame.is_empty());
        e
    }

    fn block(
        &mut self,
        frame: &mut Vec<Expr>,
        block: &mut usize,
        body: &[Spanned<Stmt>],
    ) -> ControlFlow<Expr, Expr> {
        let e = body
            .iter()
            .try_fold(Expr::Unit, |_, stmt| self.stmt(frame, block, &stmt.item));
        for _ in 0..*block {
            frame.pop();
        }
        e
    }

    fn stmt(
        &mut self,
        frame: &mut Vec<Expr>,
        block: &mut usize,
        stmt: &Stmt,
    ) -> ControlFlow<Expr, Expr> {
        ControlFlow::Continue(match stmt {
            Stmt::Expr(e) => self.expr(frame, e),
            Stmt::Assign { name, rhs, .. } => {
                let e = self.expr(frame, &rhs.item);
                frame.insert(name.item.as_idx(), e.clone());
                *block += 1;
                e
            }
            Stmt::Update { name, rhs } => match &name.item {
                Ident::Id(id) => {
                    let e = self.expr(frame, &rhs.item);
                    self.statics.insert(id.clone(), e.clone());
                    e
                }
                Ident::Idx(idx) => {
                    let e = self.expr(frame, &rhs.item);
                    frame[*idx] = e.clone();
                    e
                }
                _ => unreachable!(),
            },
            Stmt::Return(v) => {
                return ControlFlow::Break(
                    v.as_ref()
                        .map(|e| self.expr(frame, &e.item))
                        .unwrap_or(Expr::Unit),
                );
            }
            Stmt::If { then, elif, els } => {
                let ret = from_ref(then)
                    .iter()
                    .chain(elif.iter())
                    .try_fold((), |_, branch| self.branch(frame, branch));
                if let ControlFlow::Break(c) = ret {
                    return c;
                }
                if let Some((.., stmts)) = els {
                    return self.block(frame, &mut 0, stmts);
                }
                Expr::Unit
            }
            Stmt::While(branch) => {
                loop {
                    let w = self.branch(frame, branch);
                    let ControlFlow::Break(c) = w else { break };
                    if c.is_break() {
                        return c;
                    }
                }
                Expr::Unit
            }
        })
    }

    fn branch(
        &mut self,
        frame: &mut Vec<Expr>,
        branch: &Branch,
    ) -> ControlFlow<ControlFlow<Expr, Expr>> {
        let Expr::Boolean(cond) = self.expr(frame, &branch.cond.item) else {
            unreachable!();
        };
        if !cond {
            return ControlFlow::Continue(());
        }
        ControlFlow::Break(self.block(frame, &mut 0, &branch.body))
    }

    fn expr(&mut self, frame: &[Expr], expr: &Expr) -> Expr {
        match expr {
            Expr::Ident(n) => match n {
                Ident::Id(id) => self
                    .statics
                    .get(id)
                    .or_else(|| self.gs.statics.get(id).map(|s| &s.item.expr.item))
                    .cloned()
                    .unwrap_or_else(|| Expr::Ident(Ident::Id(id.clone()))),
                Ident::Idx(idx) => frame.get(*idx).unwrap().clone(),
                Ident::Builtin(b) => Expr::Ident(Ident::Builtin(*b)),
            },
            Expr::Call(f, args) => {
                let args = args.iter().map(|arg| self.expr(frame, &arg.item)).collect();
                match self.expr(frame, &f.item) {
                    Expr::Ident(n) => match n {
                        Ident::Id(id) => {
                            let f = self.gs.fns.get(&id).unwrap();
                            self.func(&f.item.body, args)
                        }
                        Ident::Builtin(b) => b.eval(args),
                        Ident::Idx(..) => unreachable!(),
                    },
                    Expr::New(..) => {
                        // TODO: Other arity and other types.
                        let arg = args.into_iter().next().unwrap();
                        Expr::Ref(Rc::new(arg))
                    }
                    _ => unreachable!(),
                }
            }
            Expr::BinaryOp(lhs, op, .., rhs) => {
                match (self.expr(frame, &lhs.item), op, self.expr(frame, &rhs.item)) {
                    (Expr::Integer(a), Sym::Le, Expr::Integer(b)) => Expr::Boolean(a.le(&b)),
                    (Expr::Float(a), Sym::Le, Expr::Float(b)) => Expr::Boolean(a.le(&b)),

                    (Expr::Integer(a), Sym::Ge, Expr::Integer(b)) => Expr::Boolean(a.ge(&b)),
                    (Expr::Float(a), Sym::Ge, Expr::Float(b)) => Expr::Boolean(a.ge(&b)),

                    (Expr::Integer(a), Sym::Lt, Expr::Integer(b)) => Expr::Boolean(a.lt(&b)),
                    (Expr::Float(a), Sym::Lt, Expr::Float(b)) => Expr::Boolean(a.lt(&b)),

                    (Expr::Integer(a), Sym::Gt, Expr::Integer(b)) => Expr::Boolean(a.gt(&b)),
                    (Expr::Float(a), Sym::Gt, Expr::Float(b)) => Expr::Boolean(a.gt(&b)),

                    (Expr::Integer(a), Sym::Plus, Expr::Integer(b)) => Expr::Integer(a.add(&b)),
                    (Expr::Float(a), Sym::Plus, Expr::Float(b)) => Expr::Float(a.add(&b)),

                    (Expr::Integer(a), Sym::Minus, Expr::Integer(b)) => Expr::Integer(a.sub(&b)),
                    (Expr::Float(a), Sym::Minus, Expr::Float(b)) => Expr::Float(a.sub(&b)),

                    (Expr::Integer(a), Sym::Mul, Expr::Integer(b)) => Expr::Integer(a.mul(&b)),
                    (Expr::Float(a), Sym::Mul, Expr::Float(b)) => Expr::Float(a.mul(&b)),

                    (Expr::Unit, Sym::EqEq, Expr::Unit) => Expr::Boolean(true),
                    (Expr::Boolean(a), Sym::EqEq, Expr::Boolean(b)) => Expr::Boolean(a == b),

                    (Expr::Integer(a), Sym::EqEq, Expr::Integer(b)) => Expr::Boolean(a.eq(&b)),
                    (Expr::Float(a), Sym::EqEq, Expr::Float(b)) => Expr::Boolean(a.eq(&b)),

                    (Expr::String(a), Sym::EqEq, Expr::String(b)) => Expr::Boolean(a == b),

                    _ => unreachable!(),
                }
            }
            Expr::UnaryOp(x, op, ..) => match op {
                Sym::Mul => {
                    let Expr::Ref(v) = self.expr(frame, &x.item) else {
                        unreachable!()
                    };
                    Rc::try_unwrap(v).unwrap()
                }
                _ => unreachable!(),
            },
            Expr::Object(.., args) => {
                let Object::Ordered(args) = args else {
                    unreachable!()
                };
                Expr::Struct(args.iter().map(|x| self.expr(frame, x)).collect())
            }
            Expr::Access(s, acc) => {
                let Expr::Struct(s) = self.expr(frame, &s.item) else {
                    unreachable!()
                };
                let Access::Indexed(i) = acc else {
                    unreachable!()
                };
                s.to_vec().remove(*i)
            }
            Expr::Method {
                callee,
                target,
                method,
                args,
            } => {
                let mut args = args
                    .iter()
                    .map(|arg| self.expr(frame, &arg.item))
                    .collect::<Vec<_>>();
                args.insert(0, self.expr(frame, &callee.item));
                let m = self
                    .gs
                    .structs
                    .get(target.as_ref().unwrap())
                    .unwrap()
                    .extends
                    .get(&method.item)
                    .unwrap();
                self.func(&m.body, args)
            }
            Expr::Ref(e) => self.expr(frame, e),
            Expr::Struct(xs) => Expr::Struct(xs.iter().map(|x| self.expr(frame, x)).collect()),

            Expr::BuiltinType(..)
            | Expr::RefType(..)
            | Expr::Unit
            | Expr::Integer(..)
            | Expr::Float(..)
            | Expr::String(..)
            | Expr::Boolean(..)
            | Expr::New(..) => expr.clone(),

            Expr::ThisType(..) | Expr::StructType(..) => unreachable!(),
        }
    }
}

trait IntoExpr {
    fn into_expr(self) -> Expr;
}

impl IntoExpr for ControlFlow<Expr, Expr> {
    fn into_expr(self) -> Expr {
        match self {
            ControlFlow::Continue(e) | ControlFlow::Break(e) => e,
        }
    }
}
