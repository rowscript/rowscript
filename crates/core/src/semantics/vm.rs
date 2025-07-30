use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::mem::take;
use std::ops::ControlFlow;
use std::slice::from_ref;

use crate::semantics::Func;
use crate::syntax::parse::Sym;
use crate::syntax::{Branch, Expr, Name, Shadowed, Stmt};

pub(crate) struct VM<'a> {
    globals: &'a HashMap<Name, Func>,
}

impl<'a> VM<'a> {
    pub(crate) fn new(globals: &'a HashMap<Name, Func>) -> Self {
        Self { globals }
    }

    pub(crate) fn func(&self, func: &Func, args: Vec<Expr>) -> Expr {
        let mut block = Block::default();

        func.params
            .iter()
            .zip(args)
            .for_each(|(param, arg)| block.insert(param.clone(), arg));

        func.body
            .iter()
            .try_fold(Expr::Unit, |_, stmt| self.stmt(&mut block, &stmt.item))
            .into_expr()
    }

    fn stmt(&self, block: &mut Block, stmt: &Stmt) -> ControlFlow<Expr, Expr> {
        ControlFlow::Continue(match stmt {
            Stmt::Func { .. } => Expr::Unit,
            Stmt::Expr(e) => self.expr(block, e),
            Stmt::Assign { name, rhs, .. } => {
                let e = self.expr(block, &rhs.item);
                block.insert(name.clone(), e.clone());
                e
            }
            Stmt::Update { name, rhs } => {
                let e = self.expr(block, &rhs.item);
                block.update(name.item.clone(), e.clone());
                e
            }
            Stmt::Return(v) => {
                return ControlFlow::Break(
                    v.as_ref()
                        .map(|e| self.expr(block, &e.item))
                        .unwrap_or(Expr::Unit),
                );
            }
            Stmt::If { then, elif, els } => {
                let ret = from_ref(then)
                    .iter()
                    .chain(elif.iter())
                    .try_fold((), |_, branch| self.branch(block, branch));
                if let ControlFlow::Break(c) = ret {
                    return c;
                }
                if let Some((.., stmts)) = els {
                    return stmts
                        .iter()
                        .try_fold(Expr::Unit, |_, stmt| self.stmt(block, &stmt.item));
                }
                Expr::Unit
            }
            Stmt::While(branch) => {
                loop {
                    let w = self.branch(block, branch);
                    let ControlFlow::Break(c) = w else { break };
                    if c.is_break() {
                        return c;
                    }
                }
                Expr::Unit
            }
        })
    }

    fn branch(&self, block: &mut Block, branch: &Branch) -> ControlFlow<ControlFlow<Expr, Expr>> {
        let Expr::Boolean(cond) = self.expr(block, &branch.cond.item) else {
            unreachable!();
        };
        if !cond {
            return ControlFlow::Continue(());
        }
        ControlFlow::Break(
            branch
                .body
                .iter()
                .try_fold(Expr::Unit, |_, stmt| self.stmt(block, &stmt.item)),
        )
    }

    fn expr(&self, block: &Block, expr: &Expr) -> Expr {
        match expr {
            Expr::Name(n) => block
                .locals
                .get(n)
                .cloned()
                .unwrap_or_else(|| Expr::Name(n.clone())),
            Expr::Call(f, args) => {
                let Expr::Name(n) = self.expr(block, &f.item) else {
                    unreachable!();
                };
                let args = args.iter().map(|e| self.expr(block, &e.item)).collect();
                let f = self.globals.get(&n).unwrap();
                self.func(f, args)
            }
            Expr::BinaryOp(lhs, op, rhs) => {
                match (self.expr(block, &lhs.item), op, self.expr(block, &rhs.item)) {
                    // TODO: Integers.
                    (Expr::Number(a), Sym::Le, Expr::Number(b)) => Expr::Boolean(a <= b),
                    (Expr::Number(a), Sym::Ge, Expr::Number(b)) => Expr::Boolean(a >= b),
                    (Expr::Number(a), Sym::Lt, Expr::Number(b)) => Expr::Boolean(a < b),
                    (Expr::Number(a), Sym::Gt, Expr::Number(b)) => Expr::Boolean(a > b),
                    (Expr::Number(a), Sym::Plus, Expr::Number(b)) => Expr::Number(a + b),
                    (Expr::Number(a), Sym::Minus, Expr::Number(b)) => Expr::Number(a - b),
                    (Expr::Number(a), Sym::Mul, Expr::Number(b)) => Expr::Number(a * b),

                    (Expr::Unit, Sym::EqEq, Expr::Unit) => Expr::Boolean(true),
                    (Expr::Boolean(a), Sym::EqEq, Expr::Boolean(b)) => Expr::Boolean(a == b),
                    (Expr::Number(a), Sym::EqEq, Expr::Number(b)) => Expr::Boolean(a == b),
                    (Expr::String(a), Sym::EqEq, Expr::String(b)) => Expr::Boolean(a == b),

                    _ => unreachable!(),
                }
            }

            Expr::BuiltinType(..)
            | Expr::Unit
            | Expr::Number(..)
            | Expr::String(..)
            | Expr::Boolean(..) => expr.clone(),
        }
    }
}

#[derive(Default)]
struct Block {
    locals: HashMap<Name, Expr>,
    shadowed: Shadowed<Name, Expr>,
}

impl Block {
    fn insert(&mut self, name: Name, e: Expr) {
        self.shadowed
            .push(name.clone(), self.locals.insert(name, e));
    }

    fn update(&mut self, name: Name, e: Expr) {
        let Entry::Occupied(mut entry) = self.locals.entry(name) else {
            unreachable!();
        };
        entry.insert(e);
    }

    fn clear(&mut self) {
        take(&mut self.shadowed).clear(&mut self.locals);
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
