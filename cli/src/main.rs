use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, ValueEnum};

use rowscript_core::codegen::{ecma, noop, Target};
use rowscript_core::Driver;

#[derive(Parser)]
#[command(version)]
struct Args {
    #[arg(index = 1, default_value = ".")]
    path: PathBuf,
    #[arg(short, long, value_enum, default_value_t = DEFAULT_TARGET_ID)]
    target: TargetID,
}

#[cfg(feature = "codegen-ecma")]
const DEFAULT_TARGET_ID: TargetID = TargetID::Ecma;
#[cfg(not(feature = "codegen-ecma"))]
const DEFAULT_TARGET_ID: TargetID = TargetID::Noop;

#[derive(Copy, Clone, ValueEnum)]
enum TargetID {
    Noop,
    #[cfg(feature = "codegen-ecma")]
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
    let args = Args::parse();
    Driver::new(args.path, args.target.into())
        .run()
        .map_or(ExitCode::FAILURE, |_| ExitCode::SUCCESS)
}
