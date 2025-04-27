use std::io::{Write, stderr, stdout};
use std::path::Path;
use std::process::Command;

use crate::OUT_DIR;
use crate::codegen::ecma::OUT_FILE;

#[test]
#[ignore]
fn test_run_all_generated() {
    let tests = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join("tests");
    for r in tests.read_dir().unwrap() {
        let entry = r.unwrap();
        if entry.file_type().unwrap().is_file() {
            continue;
        }
        let test_dir = entry.path();
        let out_dir = test_dir.join(OUT_DIR);
        if !out_dir.exists() {
            continue;
        }
        let out_file = out_dir.join(OUT_FILE);
        assert!(out_file.exists());
        let out = Command::new("node")
            .args([OUT_FILE])
            .current_dir(out_dir)
            .output()
            .unwrap();
        stdout().write_all(&out.stdout).unwrap();
        stderr().write_all(&out.stderr).unwrap();
        assert!(out.status.success())
    }
}
