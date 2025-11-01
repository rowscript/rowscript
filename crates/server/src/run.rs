use std::fs::read_to_string;
use std::path::Path;

use rowscript_core::{Source, State};

pub(crate) fn run(path: Option<&Path>) {
    let p = path.unwrap_or(Path::new("."));
    if p.is_dir() {
        todo!("run a package")
    }
    let ext = p
        .extension()
        .expect("Expected file extensions: .rows or .so");
    match ext.to_string_lossy().as_ref() {
        "rows" => run_file(p),
        "so" => todo!("run a library"),
        ext => panic!("Invalid file extension '.{ext}', expected .rows or .so"),
    }
}

fn run_file(file: &Path) {
    let text = read_to_string(file).expect("Failed to read source file");
    let mut src = Source::new(&text);
    match State::parse_with(&mut src)
        .and_then(State::resolve)
        .and_then(State::check)
    {
        Ok(..) => todo!("run a file"),
        Err(e) => {
            src.explain(e).iter().for_each(|(span, msg)| {
                eprintln!(
                    "{}:{}:{}: {msg}",
                    file.display(),
                    span.start.0 + 1,
                    span.start.1 + 1
                );
            });
            panic!("Failed to run source file");
        }
    }
}
