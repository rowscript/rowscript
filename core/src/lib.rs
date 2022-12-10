extern crate core;

use std::fs::read_to_string;
use std::io;

use ariadne::{Color, Label, Report, ReportKind, Source};
use pest::error::InputLocation;
use pest::Parser;
use pest_derive::Parser;
use thiserror::Error;

use crate::theory::abs::data::Term;
use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::theory::conc::elab::Elaborator;
use crate::theory::conc::resolve::Resolver;
use crate::theory::conc::trans;
use crate::theory::Loc;

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
    #[error("duplicate field(s)")]
    DuplicateField(Loc),

    #[error("expected function type, got \"{0}\"")]
    ExpectedPi(Box<Term>, Loc),
    #[error("expected tuple type, got \"{0}\"")]
    ExpectedSigma(Box<Term>, Loc),

    #[error("expected \"{0}\", found \"{1}\"")]
    NonUnifiable(Box<Term>, Box<Term>, Loc),
}

const PARSER_FAILED: &str = "failed while parsing";
const RESOLVER_FAILED: &str = "failed while resolving";
const CHECKER_FAILED: &str = "failed while typechecking";
const UNIFIER_FAILED: &str = "failed while unifying";

impl Error {
    fn print<F: AsRef<str>, S: AsRef<str>>(&self, file: F, source: S) {
        use Error::*;
        let (range, title, msg) = match self {
            IO(_) => (0..source.as_ref().len(), PARSER_FAILED, None),
            Parsing(e) => {
                let range = match e.location {
                    InputLocation::Pos(start) => start..source.as_ref().len(),
                    InputLocation::Span((start, end)) => start..end,
                };
                (range, PARSER_FAILED, Some(e.variant.message().to_string()))
            }
            UnresolvedVar(loc) => (loc.start..loc.end, RESOLVER_FAILED, Some(self.to_string())),
            DuplicateField(loc) => (loc.start..loc.end, RESOLVER_FAILED, Some(self.to_string())),
            ExpectedPi(_, loc) => (loc.start..loc.end, CHECKER_FAILED, Some(self.to_string())),
            ExpectedSigma(_, loc) => (loc.start..loc.end, CHECKER_FAILED, Some(self.to_string())),
            NonUnifiable(_, _, loc) => (loc.start..loc.end, UNIFIER_FAILED, Some(self.to_string())),
        };
        let mut b = Report::build(ReportKind::Error, file.as_ref(), range.start)
            .with_message(title)
            .with_code(1);
        if let Some(m) = msg {
            b = b.with_label(
                Label::new((file.as_ref(), range))
                    .with_message(m)
                    .with_color(Color::Red),
            );
        }
        b.finish()
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
        let file = self.file.clone();
        let src = read_to_string(self.file)?;
        self.check_text(src.as_str()).map_err(|e| {
            e.print(file, src);
            e
        })
    }

    fn check_text(self, src: &str) -> Result<(), Error> {
        use trans::*;

        let mut defs: Vec<Def<Expr>> = Default::default();
        let file = RowsParser::parse(Rule::file, src)?.next().unwrap();
        for d in file.into_inner() {
            match d.as_rule() {
                Rule::fn_def => defs.push(fn_def(d)),
                Rule::fn_postulate => defs.push(fn_postulate(d)),
                Rule::EOI => {}
                _ => unreachable!(),
            }
        }

        let mut r = Resolver::default();
        let mut resolved = Vec::default();
        for d in defs {
            resolved.push(r.def(d)?);
        }

        let mut e = Elaborator::default();
        e.defs(resolved)?;
        dbg!(&e);

        Ok(())
    }
}
