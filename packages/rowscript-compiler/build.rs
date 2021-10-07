use std::path::PathBuf;
use std::process::Command;

fn main() {
    let root_dir = ["..", "rowscript-grammar"].iter().collect::<PathBuf>();
    let src_dir = root_dir.join("src");

    if !src_dir.exists() {
        Command::new("npm")
            .arg("i")
            .current_dir(&root_dir)
            .status()
            .unwrap();

        Command::new("npm")
            .args(&["run", "build"])
            .current_dir(&root_dir)
            .status()
            .unwrap();
    }

    cc::Build::new()
        .include(&src_dir)
        .file(src_dir.join("parser.c"))
        .compile("rowscript-grammar");
}
