use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, ValueEnum};

use rowscript_core::codegen::{es6, noop, Target};
use rowscript_core::Driver;

#[derive(Parser)]
#[command(version)]
struct Args {
    #[arg(index = 1, default_value = ".")]
    path: PathBuf,
    #[arg(short, long, value_enum, default_value_t = DEFAULT_TARGET_ID)]
    target: TargetID,
}

#[cfg(feature = "codegen-es6")]
const DEFAULT_TARGET_ID: TargetID = TargetID::Es6;
#[cfg(not(feature = "codegen-es6"))]
const DEFAULT_TARGET_ID: TargetID = TargetID::Noop;

#[derive(Copy, Clone, ValueEnum)]
enum TargetID {
    Noop,
    #[cfg(feature = "codegen-es6")]
    Es6,
}

impl Into<Box<dyn Target>> for TargetID {
    fn into(self) -> Box<dyn Target> {
        match self {
            TargetID::Noop => Box::new(noop::Noop::default()),
            TargetID::Es6 => Box::new(es6::Es6::default()),
        }
    }
}

fn main() -> ExitCode {
    let args = Args::parse();
    Driver::new(args.path)
        .run(args.target.into())
        .map_or(ExitCode::FAILURE, |_| ExitCode::SUCCESS)
}
