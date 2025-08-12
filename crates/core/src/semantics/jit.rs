use cranelift::codegen::Context;
use cranelift::prelude::settings::{Flags, builder as flags_builder};
use cranelift::prelude::types::{F32, F64, I8, I16, I32, I64};
use cranelift::prelude::{
    AbiParam, Configurable, FunctionBuilder, FunctionBuilderContext, InstBuilder, Type as JitType,
    Value, Variable,
};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Module, default_libcall_names};
use cranelift_native::builder as native_builder;

use crate::semantics::{BuiltinType, Func, Type};
use crate::syntax::{Expr, Id, Ident};

struct Jit {
    m: JITModule,
}

impl Default for Jit {
    fn default() -> Self {
        let mut flags = flags_builder();
        flags.set("use_colocated_libcalls", "false").unwrap();
        flags.set("is_pic", "false").unwrap();
        let m = JITModule::new(JITBuilder::with_isa(
            native_builder().unwrap().finish(Flags::new(flags)).unwrap(),
            default_libcall_names(),
        ));
        Self { m }
    }
}

impl Jit {
    fn func<'a>(&'a self, id: &'a Id, f: &'a Func) -> JitFunc<'a> {
        JitFunc {
            builder: Default::default(),
            ctx: self.m.make_context(),
            m: &self.m,
            id,
            f,
        }
    }
}

struct JitFunc<'a> {
    builder: FunctionBuilderContext,
    ctx: Context,

    m: &'a JITModule,
    id: &'a Id,
    f: &'a Func,
}

impl<'a> JitFunc<'a> {
    fn func(&mut self) {
        self.ctx.func.signature.params = self
            .f
            .typ
            .params
            .iter()
            .map(|t| {
                let Type::Builtin(t) = *t else { todo!() };
                AbiParam::new(t.into())
            })
            .collect();
        let Type::Builtin(t) = self.f.typ.ret else {
            todo!()
        };
        self.ctx.func.signature.returns = vec![AbiParam::new(t.into())];

        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder);

        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);
    }

    fn expr(builder: &mut FunctionBuilder, expr: &Expr) -> Value {
        match expr {
            Expr::Ident(ident) => {
                let Ident::Idx(idx) = ident else { todo!() };
                builder.use_var(Variable::from_u32(*idx as _))
            }
            Expr::BuiltinType(..) => unreachable!(),
            Expr::Unit => builder.ins().iconst(I8, 0),
            Expr::Number(n) => builder.ins().f64const(*n),
            Expr::String(..) => todo!(),
            Expr::Boolean(b) => builder.ins().iconst(I8, *b as i64),
            Expr::Call(..) => todo!(),
            Expr::BinaryOp(..) => todo!(),
        }
    }
}

impl From<BuiltinType> for JitType {
    fn from(t: BuiltinType) -> Self {
        match t {
            BuiltinType::I8 | BuiltinType::U8 => I8,
            BuiltinType::I16 | BuiltinType::U16 => I16,
            BuiltinType::I32 | BuiltinType::U32 => I32,
            BuiltinType::I64 | BuiltinType::U64 => I64,
            BuiltinType::F32 => F32,
            BuiltinType::F64 => F64,
            _ => todo!(),
        }
    }
}
