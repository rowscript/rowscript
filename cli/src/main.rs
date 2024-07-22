use std::env::set_var;
use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, ValueEnum};
use log::error;

use rowscript_core::codegen::{ecma, noop, Target};
use rowscript_core::Driver;

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

impl From<TargetID> for Box<dyn Target> {
    fn from(val: TargetID) -> Self {
        match val {
            TargetID::Noop => Box::<noop::Noop>::default(),
            TargetID::Ecma => Box::<ecma::Ecma>::default(),
        }
    }
}

fn main() -> ExitCode {
    let Args {
        path,
        target,
        verbose,
    } = Args::parse();

    if let Some(lvl) = match verbose {
        1 => Some("info"),
        2 => Some("debug"),
        3 => Some("trace"),
        _ => None,
    } {
        set_var("RUST_LOG", lvl);
    }
    env_logger::init();

    Driver::new(&path, target.into())
        .run()
        .map_err(|e| error!("compilation failed: {e}"))
        .map_or(ExitCode::FAILURE, |_| ExitCode::SUCCESS)
}
