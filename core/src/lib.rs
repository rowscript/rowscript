extern crate core;

use std::convert::identity;
use std::fs::read_to_string;
use std::io;

use ariadne::{Color, Label, Report, ReportKind, Source};
use pest::error::InputLocation;
use pest::Parser;
use pest_derive::Parser;
use thiserror::Error;

use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::theory::conc::resolve::Resolver;
use crate::theory::conc::trans;
use crate::theory::Loc;
use crate::Error::{Parsing, UnresolvedVar};

#[cfg(test)]
mod tests;
mod theory;

#[derive(Error, Debug)]
pub enum Error {
    #[error("IO error")]
    IO(#[from] io::Error),

    #[error("parse error")]
    Parsing(#[from] pest::error::Error<Rule>),

    #[error("unresolved variable")]
    UnresolvedVar(Loc),
}

impl Error {
    fn print<F: AsRef<str>, S: AsRef<str>>(&self, file: F, source: S) {
        let (range, msg) = match self {
            Parsing(e) => {
                let range = match e.location {
                    InputLocation::Pos(start) => start..source.as_ref().len(),
                    InputLocation::Span((start, end)) => start..end,
                };
                (range, e.variant.message().to_string())
            }
            UnresolvedVar(loc) => (loc.start..loc.end, self.to_string()),
            _ => todo!(),
        };
        Report::build(ReportKind::Error, file.as_ref(), range.start)
            .with_message(self.to_string())
            .with_label(
                Label::new((file.as_ref(), range))
                    .with_message(msg)
                    .with_color(Color::Red),
            )
            .with_code(1)
            .finish()
            .print((file.as_ref(), Source::from(source.as_ref())))
            .unwrap();
    }
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

        let mut r: Resolver = Default::default();
        let mut resolved: Vec<Def<Expr>> = Default::default();
        for d in defs {
            resolved.push(r.def(d)?);
        }

        dbg!(resolved);
        Ok(())
    }
}
