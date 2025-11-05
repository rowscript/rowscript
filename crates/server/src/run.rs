use std::fs::read_to_string;
use std::path::Path;

use rowscript_core::{Source, State};

pub(crate) fn run(path: &Path) {
    if path.is_dir() {
        todo!("run a package")
    }
    let ext = path
        .extension()
        .expect("Expected file extensions: .rows or .so");
    match ext.to_string_lossy().as_ref() {
        "rows" => run_file(path),
        "so" => todo!("run a library"),
        ext => panic!("Invalid file extension '.{ext}', expected .rows or .so"),
    }
}

fn run_file(file: &Path) {
    let text = read_to_string(file).expect("Failed to read source file");
    let mut src = Source::new(&text);
    if let Err(e) = State::parse_with(&mut src)
        .and_then(State::resolve)
        .and_then(State::check)
        .and_then(State::eval)
    {
        src.print(file, e);
        panic!("Failed to run source file");
    }
}
