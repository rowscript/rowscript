use std::collections::HashMap;

use crate::semantics::{IR, Value};
use crate::syntax::Name;
use crate::syntax::parse::Sym;

struct VM {
    globals: HashMap<Name, Box<[IR]>>,
}

impl VM {
    fn run(&self, code: &[IR], mut stack: Vec<Value>) -> Value {
        for ir in code {
            match ir {
                IR::Load(usize, v) => stack.insert(*usize, v.clone()),
                IR::Call(f, args) => {
                    let Value::Global(n) = f else {
                        unreachable!();
                    };
                    let code = self.globals.get(n).unwrap();
                    stack.push(self.run(code, args.to_vec()));
                }
                IR::BinaryOp(lhs, op, rhs) => {
                    // TODO: Integers.
                    let (Value::Number(lhs), Value::Number(rhs)) = (lhs, rhs) else {
                        unreachable!();
                    };
                    stack.push(match op {
                        Sym::EqEq => Value::Boolean(lhs == rhs),
                        Sym::Le => Value::Boolean(lhs <= rhs),
                        Sym::Ge => Value::Boolean(lhs >= rhs),
                        Sym::Lt => Value::Boolean(lhs < rhs),
                        Sym::Gt => Value::Boolean(lhs > rhs),
                        Sym::Plus => Value::Number(lhs + rhs),
                        Sym::Minus => Value::Number(lhs - rhs),
                        _ => unreachable!(),
                    });
                }
                IR::Return => return stack.pop().unwrap(),
                IR::If { .. } => todo!(),
            }
        }
        unreachable!()
    }
}
