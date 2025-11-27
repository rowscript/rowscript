use std::fs::read_to_string;
use std::path::Path;

use rowscript_core::State;

pub(crate) fn run(path: &Path, interp: bool) {
    if path.is_dir() {
        todo!("run a package")
    }
    let ext = path
        .extension()
        .expect("Expected file extensions: .rows or .so");
    match ext.to_string_lossy().as_ref() {
        "rows" => run_file(path, interp),
        "so" => todo!("run a library"),
        ext => panic!("Invalid file extension '.{ext}', expected .rows or .so"),
    }
}

fn run_file(file: &Path, interp: bool) {
    let text = read_to_string(file).expect("Failed to read source file");
    let mut s = State::default();
    if let Err(e) = s
        .parse(&text)
        .and_then(|_| s.resolve())
        .and_then(|_| s.check())
        .and_then(|_| match interp {
            true => s.eval(),
            false => s.compile(file).and_then(|c| c.exec()),
        })
    {
        s.print(file, e);
        panic!("Failed to run source file");
    }
}
