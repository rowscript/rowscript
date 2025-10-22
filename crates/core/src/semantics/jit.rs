use cranelift::codegen::Context;
use cranelift::codegen::ir::BlockArg;
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
use crate::syntax::{Branch, Expr, Ident, Stmt};
use crate::{Span, Spanned};

struct Jit<'a> {
    fns: &'a Functions,
    m: JITModule,
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
        Self { fns, m }
    }
}

impl Func {
    fn compile(&self, jit: &mut Jit, ctx: &mut Context) {
        self.typ.to_signature(&mut ctx.func.signature);

        let mut builder_ctx = FunctionBuilderContext::default();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);

        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        for s in &self.body {
            s.item.compile(jit, &mut builder);
        }

        todo!()
    }
}

impl Expr {
    fn compile(&self, jit: &mut Jit, builder: &mut FunctionBuilder) -> Value {
        match self {
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
                let mut sig = jit.m.make_signature();

                let Expr::Ident(ident) = &f.item else {
                    unreachable!();
                };
                let id = ident.as_id();
                jit.fns.get(id).unwrap().typ.to_signature(&mut sig);
                // TODO: How to call back to functions in interpretation mode, or we don't?
                let callee = jit
                    .m
                    .declare_function(&id.raw(), Linkage::Import, &sig)
                    .unwrap();
                let local_callee = jit.m.declare_func_in_func(callee, builder.func);

                let args = args
                    .iter()
                    .map(|a| a.item.compile(jit, builder))
                    .collect::<Box<_>>();
                let call = builder.ins().call(local_callee, &args);
                builder.inst_results(call)[0]
            }
            Expr::BinaryOp(lhs, op, rhs) => {
                let a = lhs.item.compile(jit, builder);
                let b = rhs.item.compile(jit, builder);
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
}

impl Stmt {
    fn compile(&self, jit: &mut Jit, builder: &mut FunctionBuilder) -> Value {
        match self {
            Stmt::Func { .. } => todo!("nested function"),
            Stmt::Expr(e) => e.compile(jit, builder),
            Stmt::Assign { name, rhs, .. } | Stmt::Update { name, rhs } => {
                let Ident::Idx(idx) = name.item else { todo!() };
                let value = rhs.item.compile(jit, builder);
                builder.def_var(Variable::from_u32(idx as _), value);
                value
            }
            Stmt::Return(e) => {
                let value = e
                    .as_ref()
                    .map(|v| v.item.compile(jit, builder))
                    .unwrap_or_else(|| builder.ins().f64const(0.));
                builder.ins().return_(&[value]);
                value
            }
            Stmt::If { then, elif, els } => Self::r#if(then, elif, els, jit, builder),
            Stmt::While(b) => {
                let header_block = builder.create_block();
                let body_block = builder.create_block();
                let exit_block = builder.create_block();

                builder.ins().jump(header_block, &[]);
                builder.switch_to_block(header_block);

                let cond = b.cond.item.compile(jit, builder);
                builder.ins().brif(cond, body_block, &[], exit_block, &[]);

                builder.switch_to_block(body_block);
                builder.seal_block(body_block);
                for stmt in &b.body {
                    stmt.item.compile(jit, builder);
                }
                builder.ins().jump(header_block, &[]);

                builder.switch_to_block(exit_block);
                builder.seal_block(header_block);
                builder.seal_block(exit_block);

                builder.ins().f64const(0.)
            }
        }
    }

    fn r#if(
        then: &Branch,
        elif: &[Branch],
        els: &Option<(Span, Box<[Spanned<Self>]>)>,
        jit: &mut Jit,
        builder: &mut FunctionBuilder,
    ) -> Value {
        let cond = then.cond.item.compile(jit, builder);

        let then_block = builder.create_block();
        let merge_block = builder.create_block();
        let else_block = builder.create_block();

        builder.append_block_param(merge_block, F64); // TODO: correct JIT type

        let no_else = elif.is_empty() && els.is_none();
        if no_else {
            builder.ins().brif(cond, then_block, &[], merge_block, &[]);
        } else {
            builder.ins().brif(cond, then_block, &[], else_block, &[]);
        }

        {
            builder.switch_to_block(then_block);
            builder.seal_block(then_block);
            let mut then_return = builder.ins().f64const(0.);
            for stmt in &then.body {
                then_return = stmt.item.compile(jit, builder);
            }
            builder
                .ins()
                .jump(merge_block, &[BlockArg::Value(then_return)]);
        }

        if !no_else {
            builder.switch_to_block(else_block);
            builder.seal_block(else_block);

            let mut else_return = builder.ins().f64const(0.);
            if elif.is_empty() {
                for stmt in &els.as_ref().unwrap().1 {
                    else_return = stmt.item.compile(jit, builder);
                }
            } else {
                else_return = Self::r#if(&elif[0], &elif[1..], els, jit, builder);
            }

            builder
                .ins()
                .jump(merge_block, &[BlockArg::Value(else_return)]);
        }

        builder.switch_to_block(merge_block);
        builder.seal_block(merge_block);

        builder.block_params(merge_block)[0]
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
