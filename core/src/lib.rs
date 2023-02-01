extern crate core;

use std::fs::read_to_string;
use std::io;
use std::ops::Range;
use std::path::PathBuf;

use ariadne::{Color, Label, Report, ReportKind, Source};
use pest::error::InputLocation;
use pest::Parser;
use pest_derive::Parser;
use thiserror::Error;

use crate::theory::abs::data::Term;
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
    #[error("duplicate name")]
    DuplicateName(Loc),

    #[error("unresolved implicit parameter \"{0}\"")]
    UnresolvedImplicitParam(String, Loc),
    #[error("expected function type, got \"{0}\"")]
    ExpectedPi(Box<Term>, Loc),
    #[error("expected tuple type, got \"{0}\"")]
    ExpectedSigma(Box<Term>, Loc),
    #[error("expected object type, got \"{0}\"")]
    ExpectedObject(Box<Term>, Loc),
    #[error("expected enum type, got \"{0}\"")]
    ExpectedEnum(Box<Term>, Loc),
    #[error("fields not known yet, got \"{0}\"")]
    FieldsUnknown(Box<Term>, Loc),
    #[error("expected class type, got \"{0}\"")]
    ExpectedClass(Box<Term>, Loc),
    #[error("not exhaustive, got \"{0}\"")]
    NonExhaustive(Box<Term>, Loc),
    #[error("unresolved field \"{0}\" in \"{1}\"")]
    UnresolvedField(String, Box<Term>, Loc),
    #[error("expected interface type, got \"{0}\"")]
    ExpectedInterface(Box<Term>, Loc),
    #[error("expected type alias, got \"{0}\"")]
    ExpectedAlias(Box<Term>, Loc),
    #[error("unresolved implementation, got type \"{0}\"")]
    UnresolvedImplementation(Box<Term>, Loc),

    #[error("expected \"{0}\", found \"{1}\"")]
    NonUnifiable(Box<Term>, Box<Term>, Loc),
    #[error("field(s) \"{0}\" not contained in \"{1}\"")]
    NonRowSat(Box<Term>, Box<Term>, Loc),
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

            UnresolvedVar(loc) => self.simple_message(loc, RESOLVER_FAILED),
            DuplicateName(loc) => self.simple_message(loc, RESOLVER_FAILED),

            UnresolvedImplicitParam(_, loc) => self.simple_message(loc, CHECKER_FAILED),
            ExpectedPi(_, loc) => self.simple_message(loc, CHECKER_FAILED),
            ExpectedSigma(_, loc) => self.simple_message(loc, CHECKER_FAILED),
            ExpectedObject(_, loc) => self.simple_message(loc, CHECKER_FAILED),
            ExpectedEnum(_, loc) => self.simple_message(loc, CHECKER_FAILED),
            FieldsUnknown(_, loc) => self.simple_message(loc, CHECKER_FAILED),
            ExpectedClass(_, loc) => self.simple_message(loc, CHECKER_FAILED),
            NonExhaustive(_, loc) => self.simple_message(loc, CHECKER_FAILED),
            UnresolvedField(_, _, loc) => self.simple_message(loc, CHECKER_FAILED),
            ExpectedInterface(_, loc) => self.simple_message(loc, CHECKER_FAILED),
            ExpectedAlias(_, loc) => self.simple_message(loc, CHECKER_FAILED),
            UnresolvedImplementation(_, loc) => self.simple_message(loc, CHECKER_FAILED),

            NonUnifiable(_, _, loc) => self.simple_message(loc, UNIFIER_FAILED),
            NonRowSat(_, _, loc) => self.simple_message(loc, UNIFIER_FAILED),
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

    fn simple_message(&self, loc: &Loc, msg: &'static str) -> (Range<usize>, &str, Option<String>) {
        (loc.start..loc.end, msg, Some(self.to_string()))
    }
}

#[derive(Parser)]
#[grammar = "theory/surf.pest"]
struct RowsParser;

pub struct Driver {
    path: PathBuf,
    elab: Elaborator,
}

impl Driver {
    pub fn new(path: PathBuf) -> Self {
        Self {
            path,
            elab: Elaborator::default(),
        }
    }

    pub fn check(&mut self) -> Result<(), Error> {
        for r in self.path.read_dir()? {
            let entry = r?;
            if entry.file_type()?.is_dir() {
                continue;
            }
            let file = entry.path();
            match file.extension() {
                None => continue,
                Some(e) if e != "rows" => continue,
                _ => {
                    let src = read_to_string(&file)?;
                    self.check_text(src.as_str()).map_err(|e| {
                        e.print(file.to_str().unwrap(), src);
                        e
                    })?;
                }
            }
        }
        Ok(())
    }

    fn check_text(&mut self, src: &str) -> Result<(), Error> {
        self.elab
            .defs(Resolver::default().defs(trans::file(RowsParser::parse(Rule::file, src)?))?)
    }
}
