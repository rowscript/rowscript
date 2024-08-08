use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use crate::{Compiler, FILE_EXT, OUT_DIR};

#[test]
fn test_stdlib() {
    let pkg = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("std")
        .into_boxed_path();

    let mut libs = pkg
        .read_dir()
        .unwrap()
        .into_iter()
        .map(Result::unwrap)
        .filter(|e| e.file_type().unwrap().is_dir() && e.file_name() != OUT_DIR)
        .map(|e| e.file_name().to_string_lossy().to_string())
        .collect::<Vec<_>>();
    libs.sort();

    let mut w = BufWriter::new(File::create(pkg.join(format!("index.{}", FILE_EXT))).unwrap());
    libs.into_iter()
        .try_fold((), |_, l| writeln!(w, "from .{l} import _;"))
        .unwrap();
    w.flush().unwrap();

    Compiler::new(&pkg).run().unwrap();
}
