extern crate core;

use std::convert::identity;
use std::fs::read_to_string;
use std::io;

use pest::Parser;
use pest_derive::Parser;
use thiserror::Error;

use crate::theory::abs::def::Def;
use crate::theory::conc::trans;

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
#[grammar = "theory/surf.pest"]
struct RowsParser;

pub struct Driver<'a> {
    file: &'a str,
}

impl<'a> Driver<'a> {
    pub fn new(file: &'a str) -> Self {
        Self { file }
    }

    pub fn check(self) -> Result<(), Error> {
        let src = read_to_string(self.file)?;
        self.check_text(src.as_str())
    }

    pub fn check_text(self, src: &str) -> Result<(), Error> {
        let file = RowsParser::parse(Rule::file, src)?.next().unwrap();
        let defs = file
            .into_inner()
            .map(|d| match d.as_rule() {
                Rule::fn_def => Some(trans::fn_def(d)),
                Rule::EOI => None,
                _ => unreachable!(),
            })
            .into_iter()
            .filter_map(identity)
            .collect::<Vec<_>>();
        dbg!(defs);
        Ok(())
    }
}
