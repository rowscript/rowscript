use std::env;

fn main() {
    if env::var("CARGO_CFG_TARGET_ENV").as_deref() == Ok("msvc") {
        println!("cargo:rustc-link-arg=/stack:{}", 8 * 1024 * 1024);
    }
}
