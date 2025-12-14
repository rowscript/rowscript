use cranelift::prelude::types::{I8, I32};
use cranelift::prelude::{AbiParam, Signature};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use strum::{Display, EnumString};

use crate::Error;
use crate::semantics::{BuiltinType, FuncType, Integer, Type};
use crate::syntax::Expr;

#[derive(Debug, Copy, Clone, Display, EnumString)]
#[strum(prefix = "rowscript_core_")]
#[strum(serialize_all = "snake_case")]
pub enum Builtin {
    Println,
    Assert,
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

    fn get(&self) -> &Prototype {
        match self {
            Builtin::Println => &PRINTLN,
            Builtin::Assert => &ASSERT,
        }
    }
}

const PROTOTYPES: &[&Prototype] = &[&PRINTLN, &ASSERT];

pub(crate) fn import(builder: &mut JITBuilder) {
    for p in PROTOTYPES {
        builder.symbols([(p.id.to_string(), p.f)]);
    }
}

struct Prototype {
    id: Builtin,
    typ: fn() -> Type,
    eval: fn(Vec<Expr>) -> Expr,
    declare: fn(&mut Signature),
    f: *const u8,
}

const PRINTLN: Prototype = Prototype {
    id: Builtin::Println,
    typ: || {
        Type::Function(Box::new(FuncType {
            params: vec![Type::Builtin(BuiltinType::U32)],
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
    f: println as _,
};

fn println(v: u32) -> u8 {
    println!("{v}");
    Default::default()
}

const ASSERT: Prototype = Prototype {
    id: Builtin::Assert,
    typ: || {
        Type::Function(Box::new(FuncType {
            params: vec![Type::Builtin(BuiltinType::Bool)],
            ret: Default::default(),
        }))
    },
    eval: |args| {
        if let [v] = &args[..]
            && let Expr::Boolean(p) = v
        {
            assert!(*p);
            return Expr::Unit;
        }
        unreachable!();
    },
    declare: |sig| {
        sig.params.push(AbiParam::new(I8));
        sig.returns.push(AbiParam::new(I8));
    },
    f: assert as _,
};

fn assert(p: u8) -> u8 {
    assert_ne!(p, 0);
    Default::default()
}
