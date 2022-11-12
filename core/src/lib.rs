extern crate core;

use std::fs::read_to_string;
use std::io;

use pest::Parser;
use pest_derive::Parser;
use thiserror::Error;

#[cfg(test)]
mod tests;
mod theory;

#[derive(Error, Debug)]
pub enum Error {
    #[error("IO error")]
    IO(#[from] io::Error),
    #[error("parse error")]
    Parsing(#[from] pest::error::Error<Rule>),
}

#[derive(Parser)]
#[grammar = "theory/rows.pest"]
struct RowsParser;

pub struct Driver {
    file: String,
}

impl Driver {
    pub fn new(file: &str) -> Self {
        Self {
            file: file.to_string(),
        }
    }

    pub fn parse_file(&self) -> Result<(), Error> {
        let src = read_to_string(self.file.as_str())?;
        self.parse_text(src.as_str())
    }

    pub fn parse_text(&self, src: &str) -> Result<(), Error> {
        let file = RowsParser::parse(Rule::file, src)?.next().unwrap();
        Ok(())
    }
}
