use std::path::Path;

use crate::build::build;
use crate::run::run;
use crate::serve::serve;
use clap::{Parser, Subcommand};

mod build;
mod run;
mod serve;

const NAME: &str = env!("CARGO_PKG_NAME");
const VERSION: &str = env!("CARGO_PKG_VERSION");

fn main() {
    match Cli::parse().command {
        Command::Run { path, interp } => run(&path, interp),
        Command::Build { path } => build(&path),
        Command::Server => serve(),
    }
}

#[derive(Parser)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Run a program
    Run {
        /// Path to a file or package
        #[clap(default_value = ".")]
        path: Box<Path>,
        /// Interpret the program without JIT compilation
        #[arg(short, long)]
        interp: bool,
    },
    /// Build a program
    Build {
        /// Path to a file or package
        #[clap(default_value = ".")]
        path: Box<Path>,
    },
    /// Start the language server
    Server,
}
