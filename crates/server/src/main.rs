use std::path::Path;

use clap::{Parser, Subcommand};

use crate::run::run;
use crate::serve::serve;

mod run;
mod serve;

const NAME: &str = env!("CARGO_PKG_NAME");
const VERSION: &str = env!("CARGO_PKG_VERSION");

fn main() {
    match Cli::parse().command {
        Command::Run { path } => run(path.as_deref()),
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
        path: Option<Box<Path>>,
    },
    /// Start the language server
    Server,
}
