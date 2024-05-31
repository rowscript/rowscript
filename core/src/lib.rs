use std::fs::read_to_string;
use std::io;
use std::ops::Range;
use std::path::{Path, PathBuf};

use ariadne::{Color, Label, Report, ReportKind, Source};
use pest::error::InputLocation;
use pest::Parser;
use pest_derive::Parser;
use thiserror::Error;

use crate::codegen::{Codegen, Target};
use crate::theory::abs::data::Term;
use crate::theory::abs::def::Def;
use crate::theory::conc::elab::Elaborator;
use crate::theory::conc::load::{prelude_path, Import, Loaded, ModuleID};
use crate::theory::conc::resolve::Resolver;
use crate::theory::conc::trans::Trans;
use crate::theory::{Loc, Var};
use crate::theory::{ResolvedVar, VarKind};

pub mod codegen;
#[cfg(test)]
mod tests;
pub mod theory;

#[derive(Error, Debug)]
pub enum Error {
    #[error("IO error on file \"{0}\": \"{1}\"")]
    IO(Box<Path>, io::Error),
    #[error("parse error")]
    Parsing(#[from] Box<pest::error::Error<Rule>>),

    #[error("unresolved variable")]
    UnresolvedVar(Loc),
    #[error("duplicate name")]
    DuplicateName(Loc),

    #[error("unresolved implicit parameter \"{0}\"")]
    UnresolvedImplicitParam(String, Loc),
    #[error("expected function type, got \"{0}\"")]
    ExpectedPi(Term, Loc),
    #[error("expected tuple type, got \"{0}\"")]
    ExpectedSigma(Term, Loc),
    #[error("expected object type, got \"{0}\"")]
    ExpectedObject(Term, Loc),
    #[error("expected array type for variadic parameters, got \"{0}\"")]
    NonVariadicType(Term, Loc),
    #[error("expected definition with anonymous variadic parameters")]
    NonAnonVariadicDef(Loc),
    #[error("expected enum type, got \"{0}\"")]
    ExpectedEnum(Term, Loc),
    #[error("cannot extend with fields \"{0}\"")]
    FieldsNonExtendable(Term, Loc),
    #[error("not exhaustive, got \"{0}\"")]
    NonExhaustive(Term, Loc),
    #[error("unresolved field \"{0}\" in \"{1}\"")]
    UnresolvedField(String, Term, Loc),
    #[error("expected interface type, got \"{0}\"")]
    ExpectedInterface(Term, Loc),
    #[error("expected type alias, got \"{0}\"")]
    ExpectedAlias(Term, Loc),
    #[error("unsatisfied constraint \"{0}\", got \"{1}\"")]
    UnsatisfiedConstraint(Var, Term, Loc),
    #[error("class method \"{0}\" from \"{1}\" not implemented, got \"{2}\"")]
    ClassMethodNotImplemented(Var, Var, Term, Loc),
    #[error("unresolved instance, got \"{0}\"")]
    UnresolvedInstance(Term, Loc),
    #[error("expected constraint, got \"{0}\"")]
    ExpectedInstanceof(Term, Loc),
    #[error("expected reflectable type, got \"{0}\"")]
    ExpectedReflectable(Term, Loc),

    #[error("expected \"{0}\", found \"{1}\"")]
    NonUnifiable(Term, Term, Loc),
    #[error("field(s) \"{0}\" not contained in \"{1}\"")]
    NonRowSat(Term, Term, Loc),

    #[error("unsolved meta \"{0}\"")]
    UnsolvedMeta(Term, Loc),
    #[error("not erasable term \"{0}\"")]
    NonErasable(Term, Loc),

    #[cfg(test)]
    #[error("codegen error")]
    CodegenTest,
}

const PARSER_FAILED: &str = "failed while parsing";
const RESOLVER_FAILED: &str = "failed while resolving";
const CHECKER_FAILED: &str = "failed while typechecking";
const UNIFIER_FAILED: &str = "failed while unifying";
const CODEGEN_FAILED: &str = "failed while generating code";

fn print_err<S: AsRef<str>>(e: Error, file: &Path, source: S) -> Error {
    fn simple_message<'a>(
        e: &Error,
        loc: &Loc,
        msg: &'a str,
    ) -> (Range<usize>, &'a str, Option<String>) {
        (loc.start..loc.end, msg, Some(e.to_string()))
    }

    use Error::*;

    let (range, title, msg) = match &e {
        IO(..) => (Range::default(), PARSER_FAILED, None),
        Parsing(e) => {
            let range = match e.location {
                InputLocation::Pos(start) => start..source.as_ref().len(),
                InputLocation::Span((start, end)) => start..end,
            };
            (range, PARSER_FAILED, Some(e.variant.message().to_string()))
        }

        UnresolvedVar(loc) | DuplicateName(loc) => simple_message(&e, loc, RESOLVER_FAILED),

        UnresolvedImplicitParam(.., loc)
        | ExpectedPi(.., loc)
        | ExpectedSigma(.., loc)
        | ExpectedObject(.., loc)
        | NonVariadicType(.., loc)
        | NonAnonVariadicDef(loc)
        | ExpectedEnum(.., loc)
        | FieldsNonExtendable(.., loc)
        | NonExhaustive(.., loc)
        | UnresolvedField(.., loc)
        | ExpectedInterface(.., loc)
        | ExpectedAlias(.., loc)
        | UnsatisfiedConstraint(.., loc)
        | ClassMethodNotImplemented(.., loc)
        | UnresolvedInstance(.., loc)
        | ExpectedInstanceof(.., loc)
        | ExpectedReflectable(.., loc) => simple_message(&e, loc, CHECKER_FAILED),

        NonUnifiable(.., loc) | NonRowSat(.., loc) => simple_message(&e, loc, UNIFIER_FAILED),

        UnsolvedMeta(.., loc) | NonErasable(.., loc) => simple_message(&e, loc, CODEGEN_FAILED),

        #[cfg(test)]
        CodegenTest => (Default::default(), CODEGEN_FAILED, None),
    };
    let file_str = file.to_str().unwrap();
    let mut b = Report::build(ReportKind::Error, file_str, range.start)
        .with_message(title)
        .with_code(1);
    if let Some(m) = msg {
        b = b.with_label(
            Label::new((file_str, range))
                .with_message(m)
                .with_color(Color::Red),
        );
    }
    b.finish()
        .print((file_str, Source::from(source.as_ref())))
        .unwrap();
    e
}

#[derive(Parser)]
#[grammar = "theory/surf.pest"]
pub struct RowsParser;

pub const OUTDIR: &str = "dist";
pub const FILE_EXT: &str = "rows";

pub struct ModuleFile {
    file: Box<Path>,
    imports: Vec<Import>,
    defs: Vec<Def<Term>>,
}

pub struct Module {
    module: ModuleID,
    files: Vec<ModuleFile>,
    includes: Vec<PathBuf>,
}

pub struct Driver {
    path: Box<Path>,
    trans: Trans,
    loaded: Loaded,
    elab: Elaborator,
    codegen: Codegen,
}

enum Loadable {
    ViaID(ModuleID),
    ViaPath(PathBuf),
}

impl Driver {
    pub fn new(path: &Path, target: Box<dyn Target>) -> Self {
        let codegen = Codegen::new(target, path.join(OUTDIR));
        Self {
            path: path.into(),
            trans: Default::default(),
            loaded: Default::default(),
            elab: Default::default(),
            codegen,
        }
    }

    pub fn run(&mut self) -> Result<(), Error> {
        self.load(Loadable::ViaPath(prelude_path()), true)?;
        self.load_module(ModuleID::default())
    }

    fn load_module(&mut self, module: ModuleID) -> Result<(), Error> {
        match self.loaded.contains(&module) {
            true => Ok(()),
            false => self.load(Loadable::ViaID(module), false),
        }
    }

    fn load(&mut self, loadable: Loadable, is_ubiquitous: bool) -> Result<(), Error> {
        use Loadable::*;

        let mut files = Vec::default();
        let mut includes = Vec::default();

        let (path, module) = match loadable {
            ViaID(m) => (m.to_source_path(self.path.as_ref()), Some(m)),
            ViaPath(p) => (p, None),
        };

        for r in path
            .read_dir()
            .map_err(|e| Error::IO(path.into_boxed_path(), e))?
        {
            let entry = r.unwrap();
            if entry.file_type().unwrap().is_dir() {
                continue;
            }
            let file = entry.path();
            match file.extension() {
                None => continue,
                Some(e) => {
                    if self.codegen.should_include(&file) {
                        includes.push(file.clone());
                        continue;
                    }

                    if e != FILE_EXT {
                        continue;
                    }

                    let filepath = file.as_path();
                    let src = read_to_string(&file).map_err(|e| Error::IO(filepath.into(), e))?;
                    let (imports, defs) = self
                        .load_src(&module, src.as_str(), is_ubiquitous)
                        .map_err(|e| print_err(e, &file, src))?;
                    files.push(ModuleFile {
                        file: filepath.into(),
                        imports,
                        defs,
                    });
                }
            }
        }

        if let Some(module) = module {
            self.codegen.module(
                &self.elab.sigma,
                Module {
                    module,
                    files,
                    includes,
                },
            )?;
        }

        Ok(())
    }

    fn load_src(
        &mut self,
        module: &Option<ModuleID>,
        src: &str,
        is_ubiquitous: bool,
    ) -> Result<(Vec<Import>, Vec<Def<Term>>), Error> {
        let (mut imports, defs) = RowsParser::parse(Rule::file, src)
            .map_err(Box::new)
            .map_err(Error::from)
            .map(|p| self.trans.file(p))?;
        imports
            .iter()
            .try_fold((), |_, i| self.load_module(i.module.clone()))?;
        let defs = Resolver::new(&self.elab.ubiquitous, &self.loaded)
            .file(&mut imports, defs)
            .and_then(|d| self.elab.defs(d))?;
        for d in &defs {
            if is_ubiquitous {
                self.elab.ubiquitous.insert(
                    d.name.to_string(),
                    ResolvedVar(VarKind::InModule, d.name.clone()),
                );
            }
            match module {
                Some(m) if !d.is_private() => self.loaded.insert(m, d)?,
                _ => {}
            }
        }
        Ok((imports, defs))
    }
}

const DEFAULT_RED_ZONE: usize = 512 * 1024;
const DEFAULT_EXTRA_STACK: usize = 4 * 1024 * 1024;

#[inline(always)]
pub fn maybe_grow<R, F: FnOnce() -> R>(f: F) -> R {
    stacker::maybe_grow(DEFAULT_RED_ZONE, DEFAULT_EXTRA_STACK, f)
}
