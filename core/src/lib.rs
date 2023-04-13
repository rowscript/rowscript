use std::fs::{read_to_string, write};
use std::io;
use std::ops::Range;
use std::path::PathBuf;

use ariadne::{Color, Label, Report, ReportKind, Source};
use pest::error::InputLocation;
use pest::Parser;
use pest_derive::Parser;
use thiserror::Error;

use crate::codegen::Target;
use crate::theory::abs::data::Term;
use crate::theory::conc::elab::Elaborator;
use crate::theory::conc::resolve::Resolver;
use crate::theory::conc::trans;
use crate::theory::Loc;

pub mod codegen;
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
    #[error("unresolved implementation, got \"{0}\"")]
    UnresolvedImplementation(Box<Term>, Loc),
    #[error("expected constraint, got \"{0}\"")]
    ExpectedImplementsOf(Box<Term>, Loc),

    #[error("expected \"{0}\", found \"{1}\"")]
    NonUnifiable(Box<Term>, Box<Term>, Loc),
    #[error("field(s) \"{0}\" not contained in \"{1}\"")]
    NonRowSat(Box<Term>, Box<Term>, Loc),

    #[error("unsolved meta \"{0}\"")]
    UnsolvedMeta(Box<Term>, Loc),
    #[error("not erasable term \"{0}\"")]
    NonErasable(Box<Term>, Loc),

    #[cfg(test)]
    #[error("codegen error")]
    CodegenTest,
}

const PARSER_FAILED: &str = "failed while parsing";
const RESOLVER_FAILED: &str = "failed while resolving";
const CHECKER_FAILED: &str = "failed while typechecking";
const UNIFIER_FAILED: &str = "failed while unifying";
const CODEGEN_FAILED: &str = "failed while generating code";

fn print_err<F: AsRef<str>, S: AsRef<str>>(e: Error, file: F, source: S) -> Error {
    fn simple_message<'a>(
        e: &Error,
        loc: &Loc,
        msg: &'a str,
    ) -> (Range<usize>, &'a str, Option<String>) {
        (loc.start..loc.end, msg, Some(e.to_string()))
    }

    use Error::*;

    let (range, title, msg) = match &e {
        IO(_) => (Range::default(), PARSER_FAILED, None),
        Parsing(e) => {
            let range = match e.location {
                InputLocation::Pos(start) => start..source.as_ref().len(),
                InputLocation::Span((start, end)) => start..end,
            };
            (range, PARSER_FAILED, Some(e.variant.message().to_string()))
        }

        UnresolvedVar(loc) => simple_message(&e, loc, RESOLVER_FAILED),
        DuplicateName(loc) => simple_message(&e, loc, RESOLVER_FAILED),

        UnresolvedImplicitParam(_, loc) => simple_message(&e, loc, CHECKER_FAILED),
        ExpectedPi(_, loc) => simple_message(&e, loc, CHECKER_FAILED),
        ExpectedSigma(_, loc) => simple_message(&e, loc, CHECKER_FAILED),
        ExpectedObject(_, loc) => simple_message(&e, loc, CHECKER_FAILED),
        ExpectedEnum(_, loc) => simple_message(&e, loc, CHECKER_FAILED),
        FieldsUnknown(_, loc) => simple_message(&e, loc, CHECKER_FAILED),
        ExpectedClass(_, loc) => simple_message(&e, loc, CHECKER_FAILED),
        NonExhaustive(_, loc) => simple_message(&e, loc, CHECKER_FAILED),
        UnresolvedField(_, _, loc) => simple_message(&e, loc, CHECKER_FAILED),
        ExpectedInterface(_, loc) => simple_message(&e, loc, CHECKER_FAILED),
        ExpectedAlias(_, loc) => simple_message(&e, loc, CHECKER_FAILED),
        UnresolvedImplementation(_, loc) => simple_message(&e, loc, CHECKER_FAILED),
        ExpectedImplementsOf(_, loc) => simple_message(&e, loc, CHECKER_FAILED),

        NonUnifiable(_, _, loc) => simple_message(&e, loc, UNIFIER_FAILED),
        NonRowSat(_, _, loc) => simple_message(&e, loc, UNIFIER_FAILED),

        UnsolvedMeta(_, loc) => simple_message(&e, loc, CODEGEN_FAILED),
        NonErasable(_, loc) => simple_message(&e, loc, CODEGEN_FAILED),

        CodegenTest => (Range::default(), CODEGEN_FAILED, None),
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
    e
}

#[derive(Parser)]
#[grammar = "theory/surf.pest"]
struct RowsParser;

pub struct Driver {
    path: PathBuf,
    elab: Elaborator,
    target: Box<dyn Target>,
}

impl Driver {
    pub fn new(path: PathBuf, target: Box<dyn Target>) -> Self {
        Self {
            path,
            elab: Default::default(),
            target,
        }
    }

    pub fn outfile_path(&self) -> PathBuf {
        self.path.join(self.target.filename())
    }

    pub fn run(&mut self) -> Result<(), Error> {
        let mut files = Vec::default();

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
                    let path = file.to_str().unwrap().to_string();
                    let defs = RowsParser::parse(Rule::file, src.as_str())
                        .map_err(Error::from)
                        .map(trans::file)
                        .and_then(|d| Resolver::default().defs(d))
                        .and_then(|d| self.elab.defs(d))
                        .map_err(|e| print_err(e, &path, &src))?;
                    files.push((path, src, defs));
                }
            }
        }

        let mut buf = Vec::default();
        for (path, src, defs) in files {
            self.target
                .package(&mut buf, &self.elab.sigma, defs)
                .map_err(|e| print_err(e, &path, &src))?;
        }
        if !buf.is_empty() {
            write(self.outfile_path(), buf)?
        }

        Ok(())
    }
}
