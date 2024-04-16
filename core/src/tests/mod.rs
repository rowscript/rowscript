use std::env;
use std::path::Path;
#[cfg(feature = "codegen-ecma")]
use std::rc::Rc;

#[cfg(feature = "codegen-ecma")]
use swc_common::{
    errors::{ColorConfig, Handler},
    input::StringInput,
    SourceMap,
};
#[cfg(feature = "codegen-ecma")]
use swc_ecma_parser::{
    lexer::Lexer,
    {Parser, Syntax},
};

#[cfg(feature = "codegen-ecma")]
use crate::codegen::ecma::{Ecma, OUT_FILE};
#[cfg(not(feature = "codegen-ecma"))]
use crate::codegen::noop::Noop;
use crate::codegen::Target;
use crate::{Driver, Error};

mod playground;

mod example_eertree;
mod example_minesweeper;
mod example_nqueens;
mod example_phi;

mod fail_hole;
mod fail_parse;
mod fail_reserved;
mod fail_resolve;

mod fail_issue114;
mod fail_issue134;
mod ok_issue101;
mod ok_issue104;
mod ok_issue127;
mod ok_issue135;
mod ok_issue75;
mod ok_issue93;

mod ok_alias;
mod ok_array;
mod ok_array_iter;
mod ok_bool;
mod ok_builtin;
mod ok_chainable;
mod ok_class;
mod ok_class_associated;
mod ok_class_generics;
mod ok_class_helper;
mod ok_class_interface;
mod ok_const;
mod ok_ctl;
mod ok_enum;
mod ok_enum_default;
mod ok_enum_rowpoly;
mod ok_fn;
mod ok_fn_recur;
mod ok_fori;
mod ok_forof;
mod ok_implicit_named;
mod ok_implicit_unnamed;
mod ok_interface;
mod ok_interface_stuck;
mod ok_map;
mod ok_map_iter;
mod ok_modsys;
mod ok_mut;
mod ok_num_add;
mod ok_object;
mod ok_object_assign;
mod ok_object_rowpoly;
mod ok_op;
mod ok_postulate_fn;
mod ok_postulate_type;
mod ok_reflect;
mod ok_reflected;
mod ok_rev_app;
mod ok_typeclassopedia;
mod ok_typeclassopedia_stuck;
mod ok_unit;
mod ok_unreflect;
mod ok_varargs;
mod ok_varargs_hetero;
mod ok_verify;

#[cfg(not(feature = "codegen-ecma"))]
fn run_target() -> Box<dyn Target> {
    Box::new(Noop::default())
}

#[cfg(feature = "codegen-ecma")]
fn run_target() -> Box<dyn Target> {
    Box::new(Ecma::default())
}

fn run_helper(mod_path: &str) -> Result<(), Error> {
    let target = run_target();
    let pkg = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join("tests")
        .join(mod_path.to_string().split("::").last().unwrap());
    let mut driver = Driver::new(pkg.as_path(), target);
    driver.run()?;
    parse_outfiles(&driver.codegen.outdir)
}

#[cfg(not(feature = "codegen-ecma"))]
fn parse_outfiles(_: &Path) -> Result<(), Error> {
    Ok(())
}

#[cfg(feature = "codegen-ecma")]
fn parse_outfiles(d: &Path) -> Result<(), Error> {
    for r in d
        .to_path_buf()
        .read_dir()
        .map_err(|e| Error::IO(d.into(), e))?
    {
        let entry = r.map_err(|e| Error::IO(d.into(), e))?;
        let entry_path = entry.path();
        let path = entry_path.as_path();
        if entry
            .file_type()
            .map_err(|e| Error::IO(path.into(), e))?
            .is_dir()
        {
            parse_outfiles(&path)?;
            continue;
        }
        if entry.file_name() != OUT_FILE {
            continue;
        }
        parse_outfile(&path)?
    }
    Ok(())
}

#[cfg(feature = "codegen-ecma")]
fn parse_outfile(file: &Path) -> Result<(), Error> {
    let cm = Rc::<SourceMap>::default();
    let handler = Handler::with_tty_emitter(ColorConfig::Auto, true, false, Some(cm.clone()));

    let file = cm.load_file(file).map_err(|e| Error::IO(file.into(), e))?;
    let mut parser = Parser::new_from(Lexer::new(
        Syntax::Es(Default::default()),
        Default::default(),
        StringInput::from(file.as_ref()),
        None,
    ));

    for e in parser.take_errors() {
        e.into_diagnostic(&handler).emit();
    }

    parser.parse_module().map_err(|e| {
        e.into_diagnostic(&handler).emit();
        Error::CodegenTest
    })?;

    Ok(())
}

pub fn run_ok(mod_path: &str) {
    run_helper(mod_path).unwrap()
}

pub fn run_err(mod_path: &str) -> Error {
    run_helper(mod_path).unwrap_err()
}
