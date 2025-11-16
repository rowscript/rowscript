use cranelift::prelude::types::{I8, I32};
use cranelift::prelude::{AbiParam, Signature};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use strum::{Display, EnumString};

use crate::Error;
use crate::semantics::{BuiltinType, FunctionType, Integer, Type};
use crate::syntax::Expr;

#[derive(Debug, Clone, Display, EnumString)]
#[strum(prefix = "rowscript_core_")]
#[strum(serialize_all = "snake_case")]
pub enum Builtin {
    Println,
}

impl Builtin {
    pub(crate) fn r#type(&self) -> Type {
        (self.get().typ)()
    }

    pub(crate) fn eval(&self, args: Vec<Expr>) -> Expr {
        (self.get().eval)(args)
    }

    pub(crate) fn declare(&self, m: &mut JITModule) -> FuncId {
        let mut sig = m.make_signature();
        (self.get().declare)(&mut sig);
        m.declare_function(&self.to_string(), Linkage::Import, &sig)
            .map_err(Error::jit)
            .unwrap()
    }

    fn get(&self) -> &Proto {
        match self {
            Builtin::Println => &PRINTLN,
        }
    }
}

pub(crate) fn import(builder: &mut JITBuilder) {
    builder.symbols([(Builtin::Println.to_string(), println as _)]);
}

struct Proto {
    typ: fn() -> Type,
    eval: fn(Vec<Expr>) -> Expr,
    declare: fn(&mut Signature),
}

const PRINTLN: Proto = Proto {
    typ: || {
        Type::Function(Box::new(FunctionType {
            params: Box::new([Type::Builtin(BuiltinType::U32)]),
            ret: Default::default(),
        }))
    },
    eval: |args| {
        if let [v] = &args[..]
            && let Expr::Integer(Integer::U32(n)) = v
        {
            println(*n);
            return Expr::Unit;
        }
        unreachable!()
    },
    declare: |sig| {
        sig.params.push(AbiParam::new(I32)); // FIXME: correct type
        sig.returns.push(AbiParam::new(I8));
    },
};

fn println(v: u32) -> u8 {
    println!("{v}");
    Default::default()
}
