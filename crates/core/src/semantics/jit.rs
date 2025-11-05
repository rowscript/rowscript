use std::fs::File;
use std::io::Write;
use std::iter::once;
use std::path::Path;

use cranelift::VERSION;
use cranelift::codegen::Context;
use cranelift::codegen::gimli::write::{
    Address, AttributeValue, DwarfUnit, LineProgram, LineString, UnitEntryId,
};
use cranelift::codegen::gimli::{
    DW_AT_byte_size, DW_AT_comp_dir, DW_AT_encoding, DW_AT_language, DW_AT_low_pc, DW_AT_name,
    DW_AT_producer, DW_AT_stmt_list, DW_ATE_unsigned, DW_LANG_Rust, DW_TAG_base_type, Encoding,
    Format, RunTimeEndian,
};
use cranelift::codegen::ir::Endianness;
use cranelift::codegen::isa::TargetIsa;
use cranelift::prelude::settings::{Flags, builder as flags_builder};
use cranelift::prelude::types::{F64, I8};
use cranelift::prelude::{
    AbiParam, Configurable, FloatCC, FunctionBuilder, FunctionBuilderContext, InstBuilder,
    Signature, Type as JitType, Value, Variable,
};
use cranelift_module::{Linkage, Module, default_libcall_names};
use cranelift_native::builder as native_builder;
use cranelift_object::{ObjectBuilder, ObjectModule};

use crate::semantics::{BuiltinType, Func, FunctionType, Functions, Type};
use crate::syntax::parse::Sym;
use crate::syntax::{Branch, Expr, Id, Ident, Stmt};
use crate::{Error, Out, Span, Spanned};

pub(crate) struct Jit<'a> {
    fs: &'a Functions,
    m: ObjectModule,
}

impl<'a> Jit<'a> {
    pub(crate) fn new(fs: &'a Functions) -> Self {
        let mut flags = flags_builder();
        flags.set("opt_level", "none").unwrap();
        flags.enable("is_pic").unwrap();
        #[cfg(debug_assertions)]
        {
            flags.enable("enable_verifier").unwrap();
        }
        let m = ObjectModule::new(
            ObjectBuilder::new(
                native_builder().unwrap().finish(Flags::new(flags)).unwrap(),
                b"main",
                default_libcall_names(),
            )
            .unwrap(),
        );
        Self { fs, m }
    }

    pub(crate) fn compile(mut self, path: &Path) -> Out<()> {
        let mut ctx = self.m.make_context();
        self.fs
            .iter()
            .try_for_each(|(id, f)| f.item.compile(id, &mut self, &mut ctx))?;
        let bytes = self.m.finish().emit().map_err(Error::Emit)?;
        let out = path.with_extension("obj").into_boxed_path();
        File::create(&out)
            .unwrap()
            .write_all(&bytes)
            .map_err(|e| Error::Io(out, e))?;
        Ok(())
    }
}

impl Func {
    fn compile(&self, id: &Id, jit: &mut Jit, ctx: &mut Context) -> Out<()> {
        self.typ.to_signature(&mut ctx.func.signature);

        let mut builder_ctx = FunctionBuilderContext::default();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);

        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        for (idx, typ) in self.typ.params.iter().enumerate() {
            let val = builder.block_params(entry_block)[idx];
            let &Type::Builtin(typ) = typ else { todo!() };
            let var = declare_local(idx as _, Some(typ), &mut builder);
            builder.def_var(var, val);
        }

        let mut return_value = None;
        let mut returned = false;
        for s in &self.body {
            return_value = Some(s.item.compile(jit, &mut builder, &mut returned));
        }
        if !returned {
            let ret = return_value.unwrap_or_else(|| builder.ins().iconst(I8, 0));
            builder.ins().return_(&[ret]);
        }
        builder.finalize();

        let id = jit
            .m
            .declare_function(&id.raw(), Linkage::Export, &ctx.func.signature)
            .map_err(Error::jit)?;
        jit.m.define_function(id, ctx).map_err(Error::jit)?;

        jit.m.clear_context(ctx);
        Ok(())
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
                let args = args
                    .iter()
                    .map(|a| a.item.compile(jit, builder))
                    .collect::<Box<_>>();

                let mut sig = jit.m.make_signature();
                let Expr::Ident(ident) = &f.item else {
                    unreachable!();
                };
                let callee = match ident {
                    Ident::Id(id) => {
                        jit.fs.get(id).unwrap().item.typ.to_signature(&mut sig);
                        // TODO: How to call back to functions in interpretation mode, or we don't?
                        jit.m
                            .declare_function(&id.raw(), Linkage::Import, &sig)
                            .unwrap()
                    }
                    Ident::Builtin(b) => b.declare(&mut jit.m),
                    Ident::Idx(..) => todo!("local function"),
                };
                let local_callee = jit.m.declare_func_in_func(callee, builder.func);
                let call = builder.ins().call(local_callee, &args);
                builder
                    .inst_results(call)
                    .iter()
                    .next()
                    .cloned()
                    .unwrap_or_else(|| builder.ins().iconst(I8, 0))
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
    fn compile(&self, jit: &mut Jit, builder: &mut FunctionBuilder, returned: &mut bool) -> Value {
        match self {
            Stmt::Expr(e) => e.compile(jit, builder),
            Stmt::Assign { name, typ, rhs, .. } => {
                Self::assign(&name.item, typ, &rhs.item, jit, builder)
            }
            Stmt::Update { name, rhs } => Self::assign(&name.item, &None, &rhs.item, jit, builder),
            Stmt::Return(e) => {
                let value = e
                    .as_ref()
                    .map(|v| v.item.compile(jit, builder))
                    .unwrap_or_else(|| builder.ins().iconst(I8, 0));
                builder.ins().return_(&[value]);
                *returned = true;
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
                    stmt.item.compile(jit, builder, returned);
                }
                builder.ins().jump(header_block, &[]);

                builder.switch_to_block(exit_block);
                builder.seal_block(header_block);
                builder.seal_block(exit_block);

                builder.ins().f64const(0.)
            }
        }
    }

    fn assign(
        name: &Ident,
        typ: &Option<Spanned<Expr>>,
        rhs: &Expr,
        jit: &mut Jit,
        builder: &mut FunctionBuilder,
    ) -> Value {
        let value = rhs.compile(jit, builder);
        let Ident::Idx(idx) = name else { todo!() };
        let var = declare_local(
            *idx as _,
            typ.as_ref().map(|t| match t.item {
                Expr::BuiltinType(t) => t,
                _ => todo!(),
            }),
            builder,
        );
        builder.def_var(var, value);
        value
    }

    fn r#if(
        then: &Branch,
        elif: &[Branch],
        els: &Option<(Span, Box<[Spanned<Self>]>)>,
        jit: &mut Jit,
        builder: &mut FunctionBuilder,
    ) -> Value {
        let merge_block = builder.create_block();

        let branches = once(then).chain(elif.iter()).enumerate();
        let branches_len = 1 + elif.len();
        let mut next_branch = None;

        for (i, branch) in branches {
            if let Some(block) = next_branch {
                builder.switch_to_block(block);
            }

            let cond = branch.cond.item.compile(jit, builder);
            let then_block = builder.create_block();
            let next_block = if i + 1 < branches_len || els.is_some() {
                builder.create_block()
            } else {
                merge_block
            };
            builder.ins().brif(cond, then_block, &[], next_block, &[]);

            builder.switch_to_block(then_block);
            builder.seal_block(then_block);
            let mut returned = false;
            for stmt in &branch.body {
                stmt.item.compile(jit, builder, &mut returned);
            }
            if !returned {
                builder.ins().jump(merge_block, &[]);
            }

            next_branch = Some(next_block);
        }

        let last_branch = next_branch.unwrap();
        builder.switch_to_block(last_branch);
        builder.seal_block(last_branch);
        if let Some((_, els)) = els {
            let mut returned = false;
            for stmt in els {
                stmt.item.compile(jit, builder, &mut returned);
            }
            if !returned {
                builder.ins().jump(merge_block, &[]);
            }
        }

        builder.ins().iconst(I8, 0)
    }
}

fn declare_local(idx: u32, typ: Option<BuiltinType>, builder: &mut FunctionBuilder) -> Variable {
    let var = match typ {
        None => Variable::from_u32(idx),
        Some(typ) => builder.declare_var(typ.into()),
    };
    debug_assert_eq!(var.as_u32(), idx);
    var
}

impl From<BuiltinType> for JitType {
    fn from(t: BuiltinType) -> Self {
        match t {
            // TODO: Use these:
            // BuiltinType::Bool | BuiltinType::I8 | BuiltinType::U8 => I8,
            // BuiltinType::I16 | BuiltinType::U16 => I16,
            // BuiltinType::I32 | BuiltinType::U32 => I32,
            // BuiltinType::I64 | BuiltinType::U64 => I64,
            // BuiltinType::F32 => F32,
            BuiltinType::Unit | BuiltinType::Bool => I8,

            BuiltinType::I8
            | BuiltinType::U8
            | BuiltinType::I16
            | BuiltinType::U16
            | BuiltinType::I32
            | BuiltinType::U32
            | BuiltinType::I64
            | BuiltinType::U64
            | BuiltinType::F32
            | BuiltinType::F64 => F64,

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

#[allow(dead_code)]
struct DebugContext {
    endian: RunTimeEndian,
    dwarf: DwarfUnit,
    array_size_type: UnitEntryId,
}

#[allow(dead_code)]
impl DebugContext {
    fn new(isa: &dyn TargetIsa, path: &Path) -> Self {
        let dir = path.parent().unwrap().as_os_str().as_encoded_bytes();
        let file = path.file_name().unwrap().as_encoded_bytes();

        let encoding = Encoding {
            address_size: isa.frontend_config().pointer_bytes(),
            format: Format::Dwarf32,
            version: 5,
        };

        let endian = match isa.endianness() {
            Endianness::Little => RunTimeEndian::Little,
            Endianness::Big => RunTimeEndian::Big,
        };

        let mut dwarf = DwarfUnit::new(encoding);
        dwarf.unit.line_program = LineProgram::new(
            encoding,
            Default::default(),
            LineString::new(dir, encoding, &mut dwarf.line_strings),
            None,
            LineString::new(file, encoding, &mut dwarf.line_strings),
            None,
        );

        {
            let root = dwarf.unit.get_mut(dwarf.unit.root());
            root.set(
                DW_AT_producer,
                AttributeValue::StringRef(dwarf.strings.add(format!(
                    "{} v{} with Cranelift v{VERSION}",
                    env!("CARGO_PKG_NAME"),
                    env!("CARGO_PKG_VERSION"),
                ))),
            );
            root.set(DW_AT_language, AttributeValue::Language(DW_LANG_Rust));
            root.set(
                DW_AT_name,
                AttributeValue::StringRef(dwarf.strings.add(path.display().to_string())),
            );
            root.set(DW_AT_stmt_list, AttributeValue::Udata(0));
            root.set(
                DW_AT_comp_dir,
                AttributeValue::StringRef(dwarf.strings.add(dir)),
            );
            root.set(DW_AT_low_pc, AttributeValue::Address(Address::Constant(0)));
        }

        let array_size_type = dwarf.unit.add(dwarf.unit.root(), DW_TAG_base_type);
        let array_size_type_entry = dwarf.unit.get_mut(array_size_type);
        array_size_type_entry.set(
            DW_AT_name,
            AttributeValue::StringRef(dwarf.strings.add("__ARRAY_SIZE_TYPE__")),
        );
        array_size_type_entry.set(DW_AT_encoding, AttributeValue::Encoding(DW_ATE_unsigned));
        array_size_type_entry.set(
            DW_AT_byte_size,
            AttributeValue::Udata(isa.frontend_config().pointer_bytes().into()),
        );

        Self {
            endian,
            dwarf,
            array_size_type,
        }
    }
}
