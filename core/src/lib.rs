use std::fs::read_to_string;
use std::io;
use std::ops::Range;
use std::path::Path;

use ariadne::{Color, Label, Report, ReportKind, Source};
use pest::error::Error as PestError;
use pest::error::InputLocation;
use thiserror::Error;

use crate::codegen::{Codegen, Target};
use crate::theory::abs::data::Term;
use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::theory::conc::elab::Elaborator;
use crate::theory::conc::load::{Import, Loaded, ModuleID};
use crate::theory::conc::resolve::Resolver;
use crate::theory::surf::{Parsed, Parser, Rule};
use crate::theory::{Loc, Syntax, Var};
use crate::theory::{ResolvedVar, VarKind};

pub mod codegen;
mod prelude;
#[cfg(test)]
mod tests;
pub mod theory;

type Src = &'static str;

#[derive(Error, Debug)]
pub enum Error {
    #[error("IO error on file \"{0}\": \"{1}\"")]
    IO(Box<Path>, io::Error),
    #[error("parse error")]
    Parsing(#[from] Box<PestError<Rule>>),

    #[error("unresolved variable")]
    UnresolvedVar(Loc),
    #[error("duplicate name")]
    DuplicateName(Loc),

    #[error("unresolved implicit parameter \"{0}\"")]
    UnresolvedImplicitParam(Src, Loc),
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
    UnresolvedField(Src, Term, Loc),
    #[error("field(s) unknown yet, got \"{0}\"")]
    FieldsUnknown(Term, Loc),
    #[error("expected interface type, got \"{0}\"")]
    ExpectedInterface(Term, Loc),
    #[error("expected capability type, got \"{0}\"")]
    ExpectedCapability(Var, Loc),
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
    #[error("duplicate effect, got \"{0}\"")]
    DuplicateEffect(Var, Loc),
    #[error("cannot catch effects from pure expressions, got \"{0}\"")]
    NonCatchableExpr(Term, Loc),
    #[error("cannot catch async effects from expressions, got \"{0}\"")]
    CatchAsyncEffect(Term, Loc),
    #[error("unresolved effect \"{0}\", got \"{1}\"")]
    UnresolvedEffect(Var, Term, Loc),
    #[error("expected reflectable type, got \"{0}\"")]
    ExpectedReflectable(Term, Loc),
    #[error("definition \"{0}\" not checked yet")]
    NotCheckedYet(Var, Loc),

    #[error("expected \"{0}\", found \"{1}\"")]
    NonUnifiable(Term, Term, Loc),
    #[error("expected effect \"{0}\", found \"{1}\"")]
    EffectNonUnifiable(Term, Term, Loc),
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

fn print_err(e: Error, path: &Path, src: Src) -> Error {
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
                InputLocation::Pos(start) => {
                    start
                        ..src[start..]
                            .find('\n')
                            .map(|l| start + l)
                            .unwrap_or_else(|| src.len())
                }
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
        | FieldsUnknown(.., loc)
        | ExpectedInterface(.., loc)
        | ExpectedCapability(.., loc)
        | ExpectedAlias(.., loc)
        | UnsatisfiedConstraint(.., loc)
        | ClassMethodNotImplemented(.., loc)
        | UnresolvedInstance(.., loc)
        | ExpectedInstanceof(.., loc)
        | DuplicateEffect(.., loc)
        | NonCatchableExpr(.., loc)
        | CatchAsyncEffect(.., loc)
        | UnresolvedEffect(.., loc)
        | ExpectedReflectable(.., loc)
        | NotCheckedYet(.., loc) => simple_message(&e, loc, CHECKER_FAILED),

        NonUnifiable(.., loc) | EffectNonUnifiable(.., loc) | NonRowSat(.., loc) => {
            simple_message(&e, loc, UNIFIER_FAILED)
        }

        UnsolvedMeta(.., loc) | NonErasable(.., loc) => simple_message(&e, loc, CODEGEN_FAILED),

        #[cfg(test)]
        CodegenTest => (Default::default(), CODEGEN_FAILED, None),
    };
    let path_str = path.to_string_lossy();
    let labels = msg
        .map(|m| {
            vec![Label::new((&path_str, range.clone()))
                .with_message(m)
                .with_color(Color::Red)]
        })
        .unwrap_or_default();
    Report::build(ReportKind::Error, (&path_str, range))
        .with_message(title)
        .with_labels(labels)
        .finish()
        .eprint((&path_str, Source::from(src)))
        .unwrap();
    e
}

pub const OUT_DIR: &str = "dist";
pub const FILE_EXT: &str = "rows";

pub struct File<T: Syntax> {
    path: Box<Path>,
    src: Src,
    imports: Box<[Import]>,
    defs: Box<[Def<T>]>,
}

pub struct Module<T: Syntax> {
    module: ModuleID,
    files: Box<[File<T>]>,
    includes: Box<[Box<Path>]>,
}

#[derive(Clone)]
pub struct Compiler<T: Target> {
    path: Box<Path>,
    parser: Parser,
    loaded: Loaded,
    elab: Elaborator,
    codegen: Codegen<T>,
}

impl<T: Target> Compiler<T> {
    fn new(path: &Path) -> Self {
        let codegen = Codegen::new(path);
        Self {
            path: path.into(),
            parser: Default::default(),
            loaded: Default::default(),
            elab: Default::default(),
            codegen,
        }
    }

    pub fn run(path: &Path) -> Result<(), Error> {
        let mut c = Self::new(path);
        c.load_prelude()?;
        c.load_module(ModuleID::default())
    }

    fn load_prelude(&mut self) -> Result<(), Error> {
        let parsed = prelude::FILES
            .into_iter()
            .map(|(p, src)| {
                let path = Path::new(p);
                let Parsed { imports, defs } = self.parser.parse(path, src)?;
                if !imports.is_empty() {
                    unreachable!("unexpected imports in prelude file {p}")
                }
                Ok::<_, Error>(File {
                    path: path.into(),
                    src,
                    imports,
                    defs,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let resolved = Resolver::new(&self.elab.ubiquitous, &self.loaded).files(parsed)?;
        self.check(None, true, resolved)?;
        Ok(())
    }

    fn load_module(&mut self, module: ModuleID) -> Result<(), Error> {
        if self.loaded.contains(&module) {
            return Ok(());
        }

        let mut includes = Vec::default();
        let mut sources = Vec::default();
        let module_path = module.to_source_path(self.path.as_ref());
        for r in module_path
            .read_dir()
            .map_err(|e| Error::IO(module_path, e))?
        {
            let entry = r.unwrap();
            if entry.file_type().unwrap().is_dir() {
                continue;
            }
            let path = entry.path().into_boxed_path();
            if self.codegen.should_include(&path) {
                includes.push(path);
                continue;
            }
            if path.extension() != Some(FILE_EXT.as_ref()) {
                continue;
            }
            let src: Src = read_to_string(&path)
                .map_err(|e| Error::IO(path.clone(), e))?
                .leak();
            sources.push((path, src))
        }
        // Files are forcibly loaded in alphabetical order.
        sources.sort_by(|a, b| a.0.cmp(&b.0));

        let parsed = sources
            .into_iter()
            .map(|(p, src)| {
                self.parse_and_import(&p, src)
                    .map_err(|e| print_err(e, &p, src))
            })
            .collect::<Result<_, _>>()?;
        let resolved = Resolver::new(&self.elab.ubiquitous, &self.loaded).files(parsed)?;
        let files = self.check(Some(&module), false, resolved)?;
        let includes = includes.into_boxed_slice();
        let checked = Module {
            module,
            files,
            includes,
        };
        self.codegen.module(&self.elab.sigma, checked)?;
        Ok(())
    }

    fn parse_and_import(&mut self, path: &Path, src: Src) -> Result<File<Expr>, Error> {
        let Parsed { imports, defs } = self.parser.parse(path, src)?;
        imports
            .iter()
            .try_fold((), |_, i| self.load_module(i.module.clone()))?;
        Ok(File {
            path: path.into(),
            src,
            imports,
            defs,
        })
    }

    fn check(
        &mut self,
        module: Option<&ModuleID>,
        is_ubiquitous: bool,
        files: Box<[File<Expr>]>,
    ) -> Result<Box<[File<Term>]>, Error> {
        let files = self.elab.files(files)?;
        for f in &files {
            for d in &f.defs {
                if is_ubiquitous && !d.name.is_unbound() {
                    self.elab.ubiquitous.insert(
                        d.name.as_str(),
                        ResolvedVar(VarKind::Inside, d.name.clone()),
                    );
                }
                if let Some(m) = module {
                    if d.is_public {
                        self.loaded
                            .insert(m, d)
                            .map_err(|e| print_err(e, &f.path, f.src))?
                    }
                }
            }
        }
        Ok(files)
    }
}

#[cfg(test)]
impl Compiler<codegen::ecma::Ecma> {
    pub fn new_cached(path: &Path) -> Self {
        use std::sync::OnceLock;
        static ONCE: OnceLock<Compiler<codegen::ecma::Ecma>> = OnceLock::new();
        let mut c = ONCE
            .get_or_init(|| {
                let mut c = Self::new(Path::new("."));
                c.load_prelude().unwrap();
                c
            })
            .clone();
        c.codegen = Codegen::new(path); // FIXME: bad hack here :(
        c.path = path.into();
        c
    }

    pub fn run_cached(&mut self) -> Result<(), Error> {
        self.load_module(ModuleID::default())
    }
}

const DEFAULT_RED_ZONE: usize = 512 * 1024;
const DEFAULT_EXTRA_STACK: usize = 4 * 1024 * 1024;

#[inline(always)]
pub fn maybe_grow<R, F: FnOnce() -> R>(f: F) -> R {
    stacker::maybe_grow(DEFAULT_RED_ZONE, DEFAULT_EXTRA_STACK, f)
}
