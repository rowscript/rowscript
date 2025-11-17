use std::ops::ControlFlow;
use std::slice::from_ref;

use crate::Spanned;
use crate::semantics::Functions;
use crate::syntax::parse::Sym;
use crate::syntax::{Branch, Expr, Ident, Stmt};

pub(crate) struct Vm<'a> {
    fs: &'a Functions,
}

impl<'a> Vm<'a> {
    pub(crate) fn new(fs: &'a Functions) -> Self {
        Self { fs }
    }

    pub(crate) fn func(&self, f: &[Spanned<Stmt>], args: Vec<Expr>) -> Expr {
        let mut block = args.len();
        let mut frame = args;
        let e = self.block(&mut frame, &mut block, f).into_expr();
        debug_assert!(frame.is_empty());
        e
    }

    fn block(
        &self,
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
        &self,
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
            Stmt::Update { name, rhs } => {
                let Ident::Idx(idx) = name.item else { todo!() };
                let e = self.expr(frame, &rhs.item);
                frame[idx] = e.clone();
                e
            }
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
        &self,
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

    fn expr(&self, frame: &[Expr], expr: &Expr) -> Expr {
        match expr {
            Expr::Ident(n) => {
                if let Ident::Idx(idx) = n
                    && let Some(e) = frame.get(*idx)
                {
                    return e.clone();
                }
                Expr::Ident(n.clone())
            }
            Expr::Call(f, args) => {
                let args = args.iter().map(|e| self.expr(frame, &e.item)).collect();
                match self.expr(frame, &f.item) {
                    Expr::Ident(n) => match n {
                        Ident::Id(id) => {
                            let f = self.fs.get(&id).unwrap();
                            self.func(&f.item.body, args)
                        }
                        Ident::Builtin(b) => b.eval(args),
                        Ident::Idx(..) => unreachable!(),
                    },
                    Expr::New(..) => todo!("new expression"),
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
            Expr::New(..) => unreachable!(),

            Expr::BuiltinType(..)
            | Expr::RefType(..)
            | Expr::Unit
            | Expr::Integer(..)
            | Expr::Float(..)
            | Expr::String(..)
            | Expr::Boolean(..) => expr.clone(),
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
