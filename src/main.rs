use rowscript_compiler as compiler;

use anyhow::{anyhow, Result};
use clap::Parser;
use std::io::Read;
use std::{fs, io};

#[derive(Parser)]
#[clap(about = "RowScript programming language")]
struct Cli {
    #[clap(subcommand)]
    sub: Cmd,
}

#[derive(Parser)]
enum Cmd {
    #[clap(about = "Build source files")]
    Build(Build),

    #[clap(about = "Format source files")]
    Fmt(Fmt),
}

#[derive(Parser)]
struct Build {
    #[clap(required = true, index = 1, about = "Input source file")]
    file: String,
}

#[derive(Parser)]
struct Fmt {
    #[clap(required = true, index = 1, about = "Input source file")]
    file: String,
}

impl Build {
    fn build_file_or_stdin(&self) -> Result<String> {
        let f = &self.file;
        match f.as_str() {
            "-" => {
                let mut buf = String::new();
                io::stdin()
                    .read_to_string(&mut buf)
                    .map_err(|x| anyhow!("read stdin error: {}", x))?;
                Ok(buf)
            }
            _ => fs::read_to_string(f).map_err(|x| anyhow!("read file `{}` error: {}", f, x)),
        }
    }

    fn file(self) -> String {
        if self.file == "-" {
            return "<stdin>".to_string();
        }
        self.file
    }
}

fn main() {
    env_logger::init_from_env(
        env_logger::Env::new()
            .filter("ROWSCRIPT_LOG")
            .write_style("ROWSCRIPT_LOG_STYLE"),
    );

    match Cli::parse().sub {
        Cmd::Build(cmd) => {
            if let Err(msg) = cmd.build_file_or_stdin().map(compiler::build) {
                log::error!("{}:{}", cmd.file(), msg);
            }
        }
        Cmd::Fmt(_) => todo!(),
    }
}
