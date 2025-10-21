use cranelift::codegen::Context;
use cranelift::prelude::settings::{Flags, builder as flags_builder};
use cranelift::prelude::types::{F32, F64, I8, I16, I32, I64};
use cranelift::prelude::{
    AbiParam, Configurable, FloatCC, FunctionBuilder, FunctionBuilderContext, InstBuilder,
    Signature, Type as JitType, Value, Variable,
};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module, default_libcall_names};
use cranelift_native::builder as native_builder;

use crate::semantics::{BuiltinType, Func, FunctionType, Functions, Type};
use crate::syntax::parse::Sym;
use crate::syntax::{Expr, Id, Ident, Stmt};

struct Jit<'a> {
    fns: &'a Functions,
    m: JITModule,
    ctx: Context,
}

impl<'a> Jit<'a> {
    fn new(fns: &'a Functions) -> Self {
        let mut flags = flags_builder();
        flags.set("opt_level", "none").unwrap();
        flags.set("enable_verifier", "true").unwrap();
        let m = JITModule::new(JITBuilder::with_isa(
            native_builder().unwrap().finish(Flags::new(flags)).unwrap(),
            default_libcall_names(),
        ));
        let ctx = m.make_context();
        Self { fns, m, ctx }
    }

    fn func(&'a mut self, id: &'a Id, f: &'a Func) -> JitFunc<'a> {
        JitFunc {
            jit: self,
            id,
            f,
            ctx: Default::default(),
        }
    }
}

struct JitFunc<'a> {
    jit: &'a mut Jit<'a>,
    id: &'a Id,
    f: &'a Func,

    ctx: FunctionBuilderContext,
}

impl<'a> JitFunc<'a> {
    fn func(&mut self) {
        self.f.typ.to_signature(&mut self.jit.ctx.func.signature);

        let mut builder = FunctionBuilder::new(&mut self.jit.ctx.func, &mut self.ctx);

        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);
    }

    fn expr(&mut self, builder: &mut FunctionBuilder, expr: &Expr) -> Value {
        match expr {
            Expr::Ident(ident) => {
                let Ident::Idx(idx) = ident else { todo!() };
                builder.use_var(Variable::from_u32(*idx as _))
            }
            Expr::BuiltinType(..) => unreachable!(),
            Expr::Unit => builder.ins().iconst(I8, 0),
            Expr::Number(n) => builder.ins().f64const(*n),
            Expr::String(..) => todo!("use UstrSet to prevent duplicate in data sections"),
            Expr::Boolean(b) => builder.ins().iconst(I8, *b as i64),
            Expr::Call(f, args) => {
                let mut sig = self.jit.m.make_signature();

                let Expr::Ident(ident) = &f.item else {
                    unreachable!();
                };
                let id = ident.as_id();
                self.jit.fns.get(id).unwrap().typ.to_signature(&mut sig);
                // TODO: How to call back to functions in interpretation mode, or we don't?
                let callee = self
                    .jit
                    .m
                    .declare_function(&id.raw(), Linkage::Import, &sig)
                    .unwrap();
                let local_callee = self.jit.m.declare_func_in_func(callee, builder.func);

                let args = args
                    .iter()
                    .map(|a| self.expr(builder, &a.item))
                    .collect::<Box<_>>();
                let call = builder.ins().call(local_callee, &args);
                builder.inst_results(call)[0]
            }
            Expr::BinaryOp(lhs, op, rhs) => {
                let a = self.expr(builder, &lhs.item);
                let b = self.expr(builder, &rhs.item);
                // TODO: Integers.
                match op {
                    Sym::Le => builder.ins().fcmp(FloatCC::LessThanOrEqual, a, b),
                    Sym::Ge => builder.ins().fcmp(FloatCC::GreaterThanOrEqual, a, b),
                    Sym::Lt => builder.ins().fcmp(FloatCC::LessThan, a, b),
                    Sym::Gt => builder.ins().fcmp(FloatCC::GreaterThan, a, b),
                    Sym::Plus => builder.ins().fadd(a, b),
                    Sym::Minus => builder.ins().fsub(a, b),
                    Sym::Mul => builder.ins().fmul(a, b),
                    Sym::EqEq => builder.ins().fcmp(FloatCC::Equal, a, b),
                    _ => unreachable!(),
                }
            }
        }
    }

    fn stmt(&mut self, builder: &mut FunctionBuilder, stmt: &Stmt) -> Value {
        match stmt {
            Stmt::Func { .. } => todo!("nested function"),
            Stmt::Expr(e) => self.expr(builder, e),
            Stmt::Assign { .. } => todo!("assignment (definition)"),
            Stmt::Update { .. } => todo!("assignment (update)"),
            Stmt::Return(..) => todo!("return statement"),
            Stmt::If { .. } => todo!("if statement"),
            Stmt::While(..) => todo!("while statement"),
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

impl FunctionType {
    fn to_signature(&self, sig: &mut Signature) {
        sig.params = self
            .params
            .iter()
            .map(|t| {
                let Type::Builtin(t) = *t else { todo!() };
                AbiParam::new(t.into())
            })
            .collect();
        let Type::Builtin(t) = self.ret else { todo!() };
        sig.returns = vec![AbiParam::new(t.into())];
    }
}
