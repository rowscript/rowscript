use std::fs::remove_dir_all;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    let root_dir = ["..", "rowscript-grammar"].iter().collect::<PathBuf>();
    let src_dir = root_dir.join("src");

    let _ = remove_dir_all(&src_dir);

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

    cc::Build::new()
        .include(&src_dir)
        .file(src_dir.join("parser.c"))
        .compile("rowscript-grammar");

    println!(
        "cargo:rerun-if-changed={}",
        root_dir.join("grammar.js").to_str().unwrap()
    );
}
