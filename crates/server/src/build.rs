use std::fs::read_to_string;
use std::path::Path;

use rowscript_core::{Source, State};

pub(crate) fn build(path: &Path) {
    if path.is_dir() {
        todo!("build a package")
    }
    build_file(path)
}

fn build_file(file: &Path) {
    let text = read_to_string(file).expect("Failed to read source file");
    let mut src = Source::new(&text);
    if let Err(e) = State::parse_with(&mut src)
        .and_then(State::resolve)
        .and_then(State::check)
        .and_then(|s| s.compile(file))
    {
        src.explain(e).iter().for_each(|(span, msg)| {
            eprintln!(
                "{}:{}:{}: {msg}",
                file.display(),
                span.start.0 + 1,
                span.start.1 + 1
            );
        });
        panic!("Failed to build source file");
    }
}
