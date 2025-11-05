use cranelift::prelude::types::F64;
use cranelift::prelude::{AbiParam, Signature};
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_object::ObjectModule;
use strum::{Display, EnumString};

use crate::Error;
use crate::semantics::{BuiltinType, FunctionType, Type};
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

    pub(crate) fn declare(&self, m: &mut ObjectModule) -> FuncId {
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
            && let Expr::Number(n) = v
        {
            rowscript_core_println(*n);
            return Expr::Unit;
        }
        unreachable!()
    },
    declare: |sig| {
        sig.params.push(AbiParam::new(F64)); // FIXME: correct type
    },
};

#[unsafe(no_mangle)]
extern "C" fn rowscript_core_println(v: f64) {
    println!("{v}");
}
