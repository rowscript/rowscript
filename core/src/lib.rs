extern crate core;

use std::convert::identity;
use std::fs::read_to_string;
use std::io;

use pest::Parser;
use pest_derive::Parser;
use thiserror::Error;

use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::theory::conc::resolve::Resolver;
use crate::theory::conc::trans;
use crate::theory::{LineCol, LocalVar};

#[cfg(test)]
mod tests;
mod theory;

#[derive(Error, Debug)]
pub enum Error {
    #[error("IO error")]
    IO(#[from] io::Error),

    #[error("parse error")]
    Parsing(#[from] pest::error::Error<Rule>),

    #[error("{0}:{1}: unresolved variable \"{2}\"")]
    UnresolvedVar(String, LineCol, LocalVar),
}

impl Error {
    fn print<S : AsRef<str>, T : AsRef<str>>(&self, filename: S, source: T) {
        use ariadne::*;
        match self {
            Error::UnresolvedVar(_, loc, var) => {
                Report::build(ReportKind::Error, filename.as_ref(), loc.start)
                    .with_code(1)
                    .with_message("unresolved variable")
                    .with_label(
                        Label::new((filename.as_ref(), loc.start..loc.end))
                            .with_message(format!(
                                "variable {} cannot be resolved within context",
                                var.name
                            ))
                            .with_color(Color::Red),
                    )
                    .finish()
                    .print((filename.as_ref(), Source::from(source.as_ref())))
                    .unwrap();
            }
            _ => todo!(),
        }
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

        let mut r: Resolver = Resolver::from(self);
        let mut resolved: Vec<Def<Expr>> = Default::default();
        for d in defs {
            resolved.push(r.def(d)?);
        }

        dbg!(resolved);
        Ok(())
    }
}
