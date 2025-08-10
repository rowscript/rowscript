use cranelift::codegen::Context;
use cranelift::prelude::settings::{Flags, builder as flags_builder};
use cranelift::prelude::{Configurable, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module, default_libcall_names};
use cranelift_native::builder as native_builder;

use crate::syntax::{Id, Stmt};
use crate::{Out, Spanned};

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
    fn func(&mut self, id: &Id, _body: &[Spanned<Stmt>]) -> Out<*const u8> {
        let func = Func::new(&self.m);

        let _id =
            self.m
                .declare_function(id.raw().as_str(), Linkage::Local, &func.ctx.func.signature);

        todo!()
    }
}

struct Func<'a> {
    m: &'a JITModule,
    builder: FunctionBuilderContext,
    ctx: Context,
}

impl<'a> Func<'a> {
    fn new(m: &'a JITModule) -> Self {
        Self {
            m,
            builder: Default::default(),
            ctx: m.make_context(),
        }
    }
}
