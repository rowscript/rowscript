use std::collections::HashMap;
use std::env::current_dir;
use std::iter::once;
use std::path::Path;

use cranelift::VERSION;
use cranelift::codegen::Context;
use cranelift::codegen::gimli::write::{
    Address, AttributeValue, DwarfUnit, EndianVec, LineProgram, LineString, Range, RangeList,
    Sections,
};
use cranelift::codegen::gimli::{
    DW_AT_comp_dir, DW_AT_high_pc, DW_AT_language, DW_AT_low_pc, DW_AT_name, DW_AT_producer,
    DW_AT_ranges, DW_AT_stmt_list, DW_LANG_Rust, Encoding, Format, RunTimeEndian,
};
use cranelift::codegen::ir::{RelSourceLoc, SourceLoc};
use cranelift::codegen::isa::OwnedTargetIsa;
use cranelift::prelude::settings::{Flags, builder as flags_builder};
use cranelift::prelude::types::{F64, I8};
use cranelift::prelude::{
    AbiParam, Configurable, FloatCC, FunctionBuilder, FunctionBuilderContext, InstBuilder,
    Signature, Type as JitType, Value, Variable,
};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module, default_libcall_names};
use cranelift_native::builder as native_builder;
use object::build::elf::Builder;
use object::write::{Object, StandardSegment, Symbol, SymbolSection};
use object::{BinaryFormat, SectionKind, SymbolFlags, SymbolKind, SymbolScope};
use wasmtime_internal_jit_debug::gdb_jit_int::GdbJitImageRegistration;

use crate::semantics::builtin::import;
use crate::semantics::{BuiltinType, Func, FunctionType, Functions, Type};
use crate::syntax::parse::Sym;
use crate::syntax::{Branch, Expr, Id, Ident, Stmt};
use crate::{Error, Out, Span, Spanned};

pub struct Code {
    main: Option<Id>,
    code: HashMap<Id, *const u8>,
    _dbg: Vec<GdbJitImageRegistration>,
}

impl Code {
    pub fn main(&self) -> Option<*const u8> {
        self.main
            .as_ref()
            .and_then(|main| self.code.get(main))
            .cloned()
    }

    pub fn first_non_main(&self) -> Option<*const u8> {
        self.code
            .iter()
            .filter(|(id, ..)| id.raw() != "main")
            .map(|(.., ptr)| ptr)
            .next()
            .cloned()
    }
}

pub(crate) struct Jit<'a> {
    path: &'a Path,
    fs: &'a Functions,
    main: Option<Id>,
    isa: OwnedTargetIsa,
    m: JITModule,
    locs: HashMap<Id, Vec<RelSourceLoc>>,
    dbg: Vec<GdbJitImageRegistration>,
}

impl<'a> Jit<'a> {
    pub(crate) fn new(path: &'a Path, fs: &'a Functions, main: Option<Id>) -> Self {
        let mut flags = flags_builder();
        flags.set("opt_level", "none").unwrap();
        #[cfg(debug_assertions)]
        {
            flags.enable("enable_verifier").unwrap();
        }
        let isa = native_builder().unwrap().finish(Flags::new(flags)).unwrap();
        let mut builder = JITBuilder::with_isa(isa.clone(), default_libcall_names());
        import(&mut builder);
        Self {
            path,
            fs,
            main,
            isa,
            m: JITModule::new(builder),
            locs: Default::default(),
            dbg: Default::default(),
        }
    }

    pub(crate) fn compile(mut self) -> Out<Code> {
        let mut ctx = self.m.make_context();
        let ids = self
            .fs
            .iter()
            .map(|(id, f)| {
                f.item
                    .compile(id, &mut self, &mut ctx)
                    .map(|func_id| (id, func_id))
            })
            .collect::<Out<Vec<_>>>()?;
        self.m.finalize_definitions().map_err(Error::jit)?;
        let code = ids
            .into_iter()
            .map(|(id, func_id)| {
                let (ptr, size) = self.m.get_finalized_function(func_id);
                self.register_debug_info(id, ptr, size)?;
                Ok((id.clone(), ptr))
            })
            .collect::<Out<_>>()?;
        let main = self.main;
        let _dbg = self.dbg;
        Ok(Code { main, code, _dbg })
    }

    fn register_debug_info(&mut self, id: &Id, code: *const u8, size: usize) -> Out<()> {
        let mut obj = Object::new(
            BinaryFormat::Elf,
            match self.isa.triple().architecture {
                target_lexicon::Architecture::X86_64 => object::Architecture::X86_64,
                target_lexicon::Architecture::Aarch64(..) => object::Architecture::Aarch64,
                _ => todo!(),
            },
            match self.isa.triple().endianness().unwrap() {
                target_lexicon::Endianness::Little => object::Endianness::Little,
                target_lexicon::Endianness::Big => object::Endianness::Big,
            },
        );

        let text_id = obj.add_section(
            obj.segment_name(StandardSegment::Text).into(),
            b".text".into(),
            SectionKind::Text,
        );
        obj.add_symbol(Symbol {
            name: id.raw().as_str().into(),
            value: 0,
            size: size as _,
            kind: SymbolKind::Text,
            scope: SymbolScope::Compilation,
            weak: false,
            section: SymbolSection::Section(text_id),
            flags: SymbolFlags::None,
        });

        let sections = self.build_debug_info(id, code, size)?;
        sections
            .for_each(|id, data| {
                let debug_id = obj.add_section(
                    obj.segment_name(StandardSegment::Debug).into(),
                    id.name().into(),
                    SectionKind::Debug,
                );
                obj.set_section_data(debug_id, data.slice(), 1);
                Ok(())
            })
            .map_err(Error::WriteObject)?;

        let bytes = obj.write().map_err(Error::WriteObject)?;

        let mut builder = Builder::read(bytes.as_slice()).map_err(Error::ModifyObject)?;
        let text = builder
            .sections
            .iter_mut()
            .find(|s| s.name.as_slice() == b".text")
            .unwrap();
        text.sh_addr = code as _;
        text.sh_offset = 0;
        text.sh_size = size as _;

        let mut modified = Vec::new();
        builder.write(&mut modified).map_err(Error::ModifyObject)?;

        // Debug the object file:
        //use std::io::Write;
        //std::fs::File::create(format!("{id}.o"))
        //    .unwrap()
        //    .write_all(&modified)
        //    .unwrap();

        self.dbg.push(GdbJitImageRegistration::register(modified));

        Ok(())
    }

    fn build_debug_info(
        &self,
        id: &Id,
        code: *const u8,
        size: usize,
    ) -> Out<Sections<EndianVec<RunTimeEndian>>> {
        let dir = current_dir().unwrap();
        let full = dir.join(self.path);
        let dir = dir.as_os_str().as_encoded_bytes();
        let file = self.path.as_os_str().as_encoded_bytes();

        let encoding = Encoding {
            address_size: self.isa.frontend_config().pointer_bytes(),
            format: Format::Dwarf32,
            version: 5,
        };

        let endian = match self.isa.triple().endianness().unwrap() {
            target_lexicon::Endianness::Little => RunTimeEndian::Little,
            target_lexicon::Endianness::Big => RunTimeEndian::Big,
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
            let range_list = RangeList(vec![Range::StartLength {
                begin: Address::Constant(code as _),
                length: size as _,
            }]);
            let range_list_id = dwarf.unit.ranges.add(range_list);

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
                AttributeValue::StringRef(dwarf.strings.add(full.as_os_str().as_encoded_bytes())),
            );
            root.set(DW_AT_stmt_list, AttributeValue::LineProgramRef);
            root.set(
                DW_AT_comp_dir,
                AttributeValue::StringRef(dwarf.strings.add(dir)),
            );
            root.set(
                DW_AT_low_pc,
                AttributeValue::Address(Address::Constant(code as _)),
            );
            root.set(
                DW_AT_high_pc,
                AttributeValue::Address(Address::Constant(size as _)),
            );
            root.set(DW_AT_ranges, AttributeValue::RangeListRef(range_list_id));
        }

        {
            let (file_id, ..) = dwarf.unit.line_program.files().next().unwrap();
            let locs = self.locs.get(id).unwrap();

            dwarf
                .unit
                .line_program
                .begin_sequence(Some(Address::Constant(code as _)));

            let mut prev = Default::default();
            for loc in locs {
                let row = dwarf.unit.line_program.row();
                row.address_offset = loc.expand(SourceLoc::new(0)).bits() as _;
                row.line = 2; // TODO
                row.column = 2; // TODO
                row.file = file_id;
                if *loc != prev {
                    row.is_statement = true;
                }
                dwarf.unit.line_program.generate_row();
                prev = *loc;
            }

            dwarf.unit.line_program.end_sequence(size as _);
        }

        let mut sections = Sections::new(EndianVec::new(endian));
        dwarf.write(&mut sections).map_err(Error::EmitDebugInfo)?;

        Ok(sections)
    }
}

impl Func {
    fn compile(&self, id: &Id, jit: &mut Jit, ctx: &mut Context) -> Out<FuncId> {
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
            return_value = Some(s.compile(jit, &mut builder, &mut returned));
        }
        if !returned {
            let ret = return_value.unwrap_or_else(|| builder.ins().iconst(I8, 0));
            builder.ins().return_(&[ret]);
        }
        let locs = builder.func.srclocs.values().cloned().collect();
        builder.finalize();

        let func_id = jit
            .m
            .declare_function(&id.raw(), Linkage::Export, &ctx.func.signature)
            .map_err(Error::jit)?;
        jit.m.define_function(func_id, ctx).map_err(Error::jit)?;
        jit.locs.insert(id.clone(), locs);
        jit.m.clear_context(ctx);

        Ok(func_id)
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

impl Spanned<Stmt> {
    fn compile(&self, jit: &mut Jit, builder: &mut FunctionBuilder, returned: &mut bool) -> Value {
        builder.set_srcloc(SourceLoc::new(self.span.start as _));
        match &self.item {
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
                    stmt.compile(jit, builder, returned);
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
        els: &Option<(Span, Box<[Self]>)>,
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
                stmt.compile(jit, builder, &mut returned);
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
                stmt.compile(jit, builder, &mut returned);
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
