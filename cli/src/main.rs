use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, ValueEnum};

use rowscript_core::codegen::{es6, noop, Codegen};
use rowscript_core::Driver;

#[derive(Parser)]
#[command(version)]
struct Args {
    #[arg(index = 1, default_value = ".")]
    path: PathBuf,
    #[arg(short, long, value_enum, default_value_t = DEFAULT_TARGET)]
    target: Target,
}

#[cfg(feature = "codegen-es6")]
const DEFAULT_TARGET: Target = Target::Es6;
#[cfg(not(feature = "codegen-es6"))]
const DEFAULT_TARGET: Target = Target::Noop;

#[derive(Copy, Clone, ValueEnum)]
enum Target {
    Noop,
    #[cfg(feature = "codegen-es6")]
    Es6,
}

impl Into<Box<dyn Codegen>> for Target {
    fn into(self) -> Box<dyn Codegen> {
        match self {
            Target::Noop => Box::new(noop::Noop::default()),
            Target::Es6 => Box::new(es6::Es6::default()),
        }
    }
}

fn main() -> ExitCode {
    let args = Args::parse();
    Driver::new(args.path)
        .run(args.target.into())
        .map_or(ExitCode::FAILURE, |_| ExitCode::SUCCESS)
}
