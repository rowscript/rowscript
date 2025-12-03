use std::collections::HashMap;
use std::env::current_dir;
use std::iter::once;
use std::mem::transmute;
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
use cranelift::prelude::types::{F32, F64, I8, I16, I32, I64};
use cranelift::prelude::{
    AbiParam, Configurable, FloatCC, FunctionBuilder, FunctionBuilderContext, InstBuilder, IntCC,
    Signature, Type as JitType, Value, Variable,
};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module, default_libcall_names};
use cranelift_native::builder as native_builder;
use object::elf::SectionHeader64;
use object::write::{Object, StandardSegment, Symbol, SymbolSection};
use object::{
    BinaryFormat, Endianness, File, SectionKind, SymbolFlags, SymbolKind, SymbolScope, U64,
};
use wasmtime_internal_jit_debug::gdb_jit_int::GdbJitImageRegistration;

use crate::semantics::builtin::import;
use crate::semantics::{BuiltinType, Float, Func, FunctionType, Globals, Integer, Type};
use crate::syntax::parse::Sym;
use crate::syntax::{Branch, Expr, Id, Ident, Stmt};
use crate::{Error, LineCol, Out, Span, Spanned};

pub struct Code {
    main: Option<Id>,
    code: HashMap<Id, *const u8>,
    _dbg: Vec<GdbJitImageRegistration>,
}

impl Code {
    pub fn exec(&self) -> Out<()> {
        let ptr = self.main()?;
        unsafe { transmute::<*const u8, fn() -> u8>(ptr)() };
        Ok(())
    }

    fn main(&self) -> Out<*const u8> {
        self.main
            .as_ref()
            .and_then(|main| self.code.get(main))
            .cloned()
            .ok_or(Error::ExpectedMain)
    }

    pub fn first_non_main(self) -> Option<*const u8> {
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
    lines: &'a [LineCol],
    gs: &'a Globals,
    main: Option<Id>,
    isa: OwnedTargetIsa,
    m: JITModule,
    locs: HashMap<Id, (Vec<LineCol>, Vec<RelSourceLoc>)>,
    dbg: Vec<GdbJitImageRegistration>,
}

impl<'a> Jit<'a> {
    pub(crate) fn new(
        path: &'a Path,
        lines: &'a [LineCol],
        gs: &'a Globals,
        main: Option<Id>,
    ) -> Self {
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
            lines,
            gs,
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
            .gs
            .fns
            .iter()
            .map(|(id, f)| {
                f.compile(id, &mut self, &mut ctx)
                    .map(|(func_id, size)| (id, func_id, size))
            })
            .collect::<Out<Vec<_>>>()?;
        self.m.finalize_definitions().map_err(Error::jit)?;
        let code = ids
            .into_iter()
            .map(|(id, func_id, size)| {
                let ptr = self.m.get_finalized_function(func_id);
                self.register_object(id, ptr, size)?;
                Ok((id.clone(), ptr))
            })
            .collect::<Out<_>>()?;
        let main = self.main;
        let _dbg = self.dbg;
        Ok(Code { main, code, _dbg })
    }

    fn register_object(&mut self, id: &Id, code: *const u8, size: usize) -> Out<()> {
        let endian = match self.isa.triple().endianness().unwrap() {
            target_lexicon::Endianness::Little => Endianness::Little,
            target_lexicon::Endianness::Big => Endianness::Big,
        };

        let mut obj = Object::new(
            BinaryFormat::Elf,
            match self.isa.triple().architecture {
                target_lexicon::Architecture::X86_64 => object::Architecture::X86_64,
                target_lexicon::Architecture::Aarch64(..) => object::Architecture::Aarch64,
                _ => todo!(),
            },
            endian,
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
            scope: SymbolScope::Linkage,
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

        let File::Elf64(file) = File::parse(bytes.as_slice()).map_err(Error::ModifyObject)? else {
            unreachable!();
        };
        let sh_off = file.elf_header().e_shoff.get(endian);
        let sections = file.elf_section_table();
        sections.iter().for_each(|s| {
            if s.sh_name == Default::default() {
                return;
            }
            let s = s as *const _ as *mut SectionHeader64<Endianness>;
            unsafe {
                (*s).sh_addr = U64::new(endian, (bytes.as_ptr() as u64) + sh_off);
            }
        });
        {
            let (.., text) = sections.section_by_name(endian, b".text").unwrap();
            let text = text as *const _ as *mut SectionHeader64<Endianness>;
            unsafe {
                (*text).sh_addr = U64::new(endian, code as _);
                (*text).sh_offset = Default::default();
                (*text).sh_size = U64::new(endian, size as _);
            }
        }

        self.dbg.push(GdbJitImageRegistration::register(bytes));

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
                AttributeValue::Address(Address::Constant(code as u64 + (size as u64))),
            );
            root.set(DW_AT_ranges, AttributeValue::RangeListRef(range_list_id));
        }

        {
            let (file_id, ..) = dwarf.unit.line_program.files().next().unwrap();
            let (lines, locs) = self.locs.get(id).unwrap();
            let mut lines = lines.iter();

            dwarf
                .unit
                .line_program
                .begin_sequence(Some(Address::Constant(code as _)));

            let mut prev = None;
            let first_row = dwarf.unit.line_program.row();
            first_row.basic_block = true;
            first_row.prologue_end = true;
            for loc in locs {
                if Some(*loc) == prev {
                    continue;
                }
                let line = lines.next().unwrap();
                let row = dwarf.unit.line_program.row();
                row.address_offset = loc.expand(SourceLoc::new(0)).bits() as _;
                row.line = (line.start.0 + 1) as _;
                row.column = (line.start.1 + 1) as _;
                row.file = file_id;
                row.is_statement = true;

                dwarf.unit.line_program.generate_row();
                prev = Some(*loc);
            }

            dwarf.unit.line_program.end_sequence(size as _);
        }

        let mut sections = Sections::new(EndianVec::new(endian));
        dwarf.write(&mut sections).map_err(Error::EmitDebugInfo)?;

        Ok(sections)
    }
}

impl Spanned<Func> {
    fn compile(&self, id: &Id, jit: &mut Jit, ctx: &mut Context) -> Out<(FuncId, usize)> {
        self.item.typ.to_signature(&mut ctx.func.signature);

        let mut builder_ctx = FunctionBuilderContext::default();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);

        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        for (idx, typ) in self.item.typ.params.iter().enumerate() {
            let val = builder.block_params(entry_block)[idx];
            let &Type::Builtin(typ) = typ else { todo!() };
            let var = declare_local(idx as _, Some(typ), &mut builder);
            builder.def_var(var, val);
        }

        let mut lines = Vec::default();
        let mut return_value = None;
        let mut returned = false;
        for s in &self.item.body {
            return_value = Some(s.compile(jit, &mut builder, &mut lines, &mut returned));
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
        let size = ctx.compiled_code().unwrap().buffer.data().len();
        jit.locs.insert(id.clone(), (lines, locs));
        jit.m.clear_context(ctx);

        Ok((func_id, size))
    }
}

impl Spanned<Stmt> {
    fn compile(
        &self,
        jit: &mut Jit,
        builder: &mut FunctionBuilder,
        lines: &mut Vec<LineCol>,
        returned: &mut bool,
    ) -> Value {
        builder.set_srcloc(SourceLoc::new(self.span.start as _));
        lines.push(jit.lines[self.span.start]);
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
            Stmt::If { then, elif, els } => Self::r#if(then, elif, els, jit, builder, lines),
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
                    stmt.compile(jit, builder, lines, returned);
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
        lines: &mut Vec<LineCol>,
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
                stmt.compile(jit, builder, lines, &mut returned);
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
                stmt.compile(jit, builder, lines, &mut returned);
            }
            if !returned {
                builder.ins().jump(merge_block, &[]);
            }
        }

        builder.ins().iconst(I8, 0)
    }
}

impl Expr {
    fn compile(&self, jit: &mut Jit, builder: &mut FunctionBuilder) -> Value {
        match self {
            Expr::Ident(ident) => {
                let Ident::Idx(idx) = ident else { todo!() };
                builder.use_var(Variable::from_u32(*idx as _))
            }
            Expr::BuiltinType(..) | Expr::RefType(..) => unreachable!(),
            Expr::Unit => builder.ins().iconst(I8, 0),
            Expr::Integer(n) => match n {
                Integer::I8(n) => builder.ins().iconst(I8, *n as i64),
                Integer::I16(n) => builder.ins().iconst(I16, *n as i64),
                Integer::I32(n) => builder.ins().iconst(I32, *n as i64),
                Integer::I64(n) => builder.ins().iconst(I64, *n),
                Integer::U8(n) => builder.ins().iconst(I8, *n as i64),
                Integer::U16(n) => builder.ins().iconst(I16, *n as i64),
                Integer::U32(n) => builder.ins().iconst(I32, *n as i64),
                Integer::U64(n) => builder.ins().iconst(I64, *n as i64),
            },
            Expr::Float(n) => match n {
                Float::F32(n) => builder.ins().f32const(*n),
                Float::F64(n) => builder.ins().f64const(*n),
            },
            Expr::String(..) => todo!("use UstrSet to prevent duplicate in data sections"),
            Expr::Boolean(b) => builder.ins().iconst(I8, *b as i64),
            Expr::Call(f, args) => {
                let args = args
                    .iter()
                    .map(|a| a.item.compile(jit, builder))
                    .collect::<Box<_>>();

                let mut sig = jit.m.make_signature();
                let Expr::Ident(ident) = &f.item else {
                    todo!("new expression");
                };
                let callee = match ident {
                    Ident::Id(id) => {
                        jit.gs.fns.get(id).unwrap().item.typ.to_signature(&mut sig);
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
                builder.inst_results(call)[0]
            }
            Expr::BinaryOp(lhs, op, typ, rhs) => {
                let a = lhs.item.compile(jit, builder);
                let b = rhs.item.compile(jit, builder);
                let Type::Builtin(typ) = *typ.as_ref().unwrap() else {
                    unreachable!()
                };
                if typ.is_integer() {
                    typ.compile_integer(builder, op, a, b)
                } else if typ.is_float() {
                    typ.compile_float(builder, op, a, b)
                } else {
                    unreachable!()
                }
            }
            Expr::UnaryOp(..) => todo!(),
            Expr::Object(..) => todo!("initializer"),
            Expr::Access(..) => todo!("access"),
            Expr::Method(..) => todo!("method"),
            Expr::New(..) | Expr::StructType(..) | Expr::Ref(..) | Expr::Struct(..) => {
                unreachable!()
            }
        }
    }
}

impl BuiltinType {
    fn compile_integer(self, builder: &mut FunctionBuilder, op: &Sym, a: Value, b: Value) -> Value {
        match op {
            Sym::Le => builder.ins().icmp(
                if self.is_signed_integer() {
                    IntCC::SignedLessThanOrEqual
                } else {
                    IntCC::UnsignedLessThanOrEqual
                },
                a,
                b,
            ),
            Sym::Ge => builder.ins().icmp(
                if self.is_signed_integer() {
                    IntCC::SignedGreaterThanOrEqual
                } else {
                    IntCC::UnsignedGreaterThanOrEqual
                },
                a,
                b,
            ),
            Sym::Lt => builder.ins().icmp(
                if self.is_signed_integer() {
                    IntCC::SignedLessThan
                } else {
                    IntCC::UnsignedLessThan
                },
                a,
                b,
            ),
            Sym::Gt => builder.ins().icmp(
                if self.is_signed_integer() {
                    IntCC::SignedGreaterThan
                } else {
                    IntCC::UnsignedGreaterThan
                },
                a,
                b,
            ),
            Sym::Plus => builder.ins().iadd(a, b),
            Sym::Minus => builder.ins().isub(a, b),
            Sym::Mul => builder.ins().imul(a, b),
            Sym::EqEq => builder.ins().icmp(IntCC::Equal, a, b),
            _ => unreachable!(),
        }
    }

    fn compile_float(self, builder: &mut FunctionBuilder, op: &Sym, a: Value, b: Value) -> Value {
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
            BuiltinType::Unit | BuiltinType::Bool | BuiltinType::I8 | BuiltinType::U8 => I8,
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
