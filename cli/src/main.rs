use std::path::PathBuf;
use std::process::ExitCode;

use clap::Parser;

use rowscript_core::Driver;

#[derive(Parser)]
#[command(version)]
struct Args {
    #[arg(index = 1, default_value = ".")]
    path: PathBuf,
}

fn main() -> ExitCode {
    Driver::new(Args::parse().path)
        .check()
        .map_or(ExitCode::FAILURE, |_| ExitCode::SUCCESS)
}
