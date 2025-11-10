use std::fs::read_to_string;
use std::path::Path;

use rowscript_core::State;

pub(crate) fn build(path: &Path) {
    if path.is_dir() {
        todo!("build a package")
    }
    build_file(path)
}

fn build_file(file: &Path) {
    let text = read_to_string(file).expect("Failed to read source file");
    let mut s = State::default();
    if let Err(e) = s
        .parse(&text)
        .and_then(|_| s.resolve())
        .and_then(|_| s.check())
        .and_then(|_| s.compile(file))
    {
        s.print(file, e);
        panic!("Failed to build source file");
    }
}
