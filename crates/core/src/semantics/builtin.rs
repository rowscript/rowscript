use cranelift::prelude::AbiParam;
use cranelift::prelude::types::F64;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};

use strum::{Display, EnumString};

use crate::semantics::{BuiltinType, FunctionType, Type};
use crate::syntax::Expr;
use crate::{Error, Out};

#[derive(Debug, Clone, Display, EnumString)]
#[strum(prefix = "rowscript_core_")]
#[strum(serialize_all = "snake_case")]
pub enum Builtin {
    Println,
}

impl Builtin {
    pub(crate) fn r#type(&self) -> Type {
        match self {
            Builtin::Println => Type::Function(Box::new(FunctionType {
                params: Box::new([Type::Builtin(BuiltinType::U32)]),
                ret: Default::default(),
            })),
        }
    }

    fn eval(&self, args: Vec<Expr>) -> Expr {
        match self {
            Builtin::Println => {
                if let [v] = &args[..]
                    && let Expr::Number(n) = v
                {
                    println(*n);
                    return Expr::Unit;
                }
                unreachable!()
            }
        }
    }

    fn import(&self, builder: &mut JITBuilder) {
        match self {
            Builtin::Println => builder.symbol(self.to_string(), println as _),
        };
    }

    fn declare(&self, m: &mut JITModule) -> Out<FuncId> {
        let mut sig = m.make_signature();
        match self {
            Builtin::Println => {
                sig.params.push(AbiParam::new(F64)); // FIXME: correct type
                sig.returns.push(AbiParam::new(F64)); // FIXME: correct type
            }
        };
        m.declare_function(&self.to_string(), Linkage::Import, &sig)
            .map_err(Error::jit)
    }
}

fn println(v: f64) {
    println!("{v}");
}
