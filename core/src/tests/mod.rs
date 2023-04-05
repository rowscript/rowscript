use std::env;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use swc_common::errors::{ColorConfig, Handler};
use swc_common::input::StringInput;
use swc_common::SourceMap;
use swc_ecma_parser::lexer::Lexer;
use swc_ecma_parser::{Parser, Syntax};

use crate::codegen::ecma::Ecma;
use crate::codegen::Target;
use crate::{Driver, Error};

mod fail_parse;
mod fail_resolve;
mod ok_alias;
mod ok_bool;
mod ok_enum;
mod ok_fn;
mod ok_fn_recur;
mod ok_hole;
mod ok_implicit_named;
mod ok_implicit_unnamed;
mod ok_interface;
mod ok_interface_stuck;
mod ok_object;
mod ok_object_rowpoly;
mod ok_oop;
mod ok_oop_generics;
mod ok_postulate_fn;
mod ok_postulate_type;
mod ok_typeclassopedia;
mod ok_typeclassopedia_stuck;

fn run_helper(mod_path: &str) -> Result<(), Error> {
    let target = Ecma::default();
    let pkg = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join("tests")
        .join(mod_path.to_string().split("::").last().unwrap());
    let outfile = pkg.join(target.filename());
    Driver::new(pkg).run(Box::new(target))?;
    parse_js(outfile.as_path())
}

fn parse_js(path: &Path) -> Result<(), Error> {
    let cm = Rc::<SourceMap>::default();
    let handler = Handler::with_tty_emitter(ColorConfig::Auto, true, false, Some(cm.clone()));

    let file = cm.load_file(path)?;
    let mut parser = Parser::new_from(Lexer::new(
        Syntax::Es(Default::default()),
        Default::default(),
        StringInput::from(&*file),
        None,
    ));

    for e in parser.take_errors() {
        e.into_diagnostic(&handler).emit();
    }

    parser.parse_module().map_err(|e| {
        e.into_diagnostic(&handler).emit();
        Error::Codegen
    })?;

    Ok(())
}

pub fn run_ok(mod_path: &str) {
    run_helper(mod_path).unwrap()
}

pub fn run_err(mod_path: &str) -> Error {
    run_helper(mod_path).unwrap_err()
}
