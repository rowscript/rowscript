use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, ValueEnum};
use log::error;
use log::LevelFilter::{Debug, Info, Trace};

use rowscript_core::codegen::ecma::Ecma;
use rowscript_core::codegen::noop::Noop;
use rowscript_core::Compiler;

#[derive(Parser)]
#[command(version)]
struct Args {
    #[arg(index = 1, default_value = ".")]
    path: PathBuf,
    #[arg(short, long, value_enum, default_value_t = TargetID::Ecma)]
    target: TargetID,
    #[arg(short, long, action = clap::ArgAction::Count)]
    verbose: u8,
}

#[derive(Copy, Clone, ValueEnum)]
enum TargetID {
    Noop,
    Ecma,
}

fn main() -> ExitCode {
    let Args {
        path,
        target,
        verbose,
    } = Args::parse();

    match verbose {
        0 => None,
        1 => Some(Info),
        2 => Some(Debug),
        _ => Some(Trace),
    }
    .map_or_else(env_logger::init, |l| {
        env_logger::builder().filter_level(l).init()
    });

    match target {
        TargetID::Noop => Compiler::<Noop>::run(&path),
        TargetID::Ecma => Compiler::<Ecma>::run(&path),
    }
    .map_err(|e| error!("compilation failed: {e}"))
    .map_or(ExitCode::FAILURE, |_| ExitCode::SUCCESS)
}
