use std::fs::read_to_string;
use std::io;
use std::ops::Range;
use std::path::Path;

use ariadne::{Color, Label, Report, ReportKind, Source};
use pest::error::Error as PestError;
use pest::error::InputLocation;
use pest::Parser;
use pest_derive::Parser;
use thiserror::Error;

use crate::codegen::{Codegen, Target};
use crate::theory::abs::data::Term;
use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::theory::conc::elab::Elaborator;
use crate::theory::conc::load::{prelude_path, Import, Loaded, ModuleID};
use crate::theory::conc::resolve::Resolver;
use crate::theory::conc::trans::Trans;
use crate::theory::{Loc, Syntax, Var};
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
    Parsing(#[from] Box<PestError<Rule>>),

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

fn print_err(e: Error, file: &Path) -> Error {
    fn simple_message<'a>(
        e: &Error,
        loc: &Loc,
        msg: &'a str,
    ) -> (Range<usize>, &'a str, Option<String>) {
        (loc.start..loc.end, msg, Some(e.to_string()))
    }

    use Error::*;

    let source = match read_to_string(file) {
        Ok(s) => s,
        _ => unreachable!(),
    };

    let (range, title, msg) = match &e {
        IO(..) => (Range::default(), PARSER_FAILED, None),
        Parsing(e) => {
            let range = match e.location {
                InputLocation::Pos(start) => start..source.len(),
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
        | ExpectedReflectable(.., loc) => simple_message(&e, loc, CHECKER_FAILED),

        NonUnifiable(.., loc) | EffectNonUnifiable(.., loc) | NonRowSat(.., loc) => {
            simple_message(&e, loc, UNIFIER_FAILED)
        }

        UnsolvedMeta(.., loc) | NonErasable(.., loc) => simple_message(&e, loc, CODEGEN_FAILED),

        #[cfg(test)]
        CodegenTest => (Default::default(), CODEGEN_FAILED, None),
    };
    let file_str = file.to_string_lossy();
    let mut b = Report::build(ReportKind::Error, &file_str, range.start)
        .with_message(title)
        .with_code(1);
    if let Some(m) = msg {
        b = b.with_label(
            Label::new((&file_str, range))
                .with_message(m)
                .with_color(Color::Red),
        );
    }
    b.finish().print((&file_str, Source::from(source))).unwrap();
    e
}

#[derive(Parser)]
#[grammar = "theory/surf.pest"]
pub struct RowsParser;

pub const OUTDIR: &str = "dist";
pub const FILE_EXT: &str = "rows";

pub struct File<T: Syntax> {
    file: Box<Path>,
    imports: Vec<Import>,
    defs: Vec<Def<T>>,
}

pub struct Module<T: Syntax> {
    module: ModuleID,
    files: Vec<File<T>>,
    includes: Vec<Box<Path>>,
}

pub struct Compiler {
    path: Box<Path>,
    trans: Trans,
    loaded: Loaded,
    elab: Elaborator,
    codegen: Codegen,
}

enum Loadable {
    ViaID(ModuleID),
    ViaPath(Box<Path>),
}

impl Compiler {
    pub fn new(path: &Path, target: Box<dyn Target>) -> Self {
        let codegen = Codegen::new(target, path.join(OUTDIR).into_boxed_path());
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

        let (module_path, module) = match loadable {
            ViaID(m) => (m.to_source_path(self.path.as_ref()), Some(m)),
            ViaPath(p) => (p, None),
        };

        let mut unchecked = Vec::default();
        let mut includes = Vec::default();

        let entries = module_path
            .read_dir()
            .map_err(|e| Error::IO(module_path, e))?;
        for r in entries {
            let entry = r.unwrap();
            if entry.file_type().unwrap().is_dir() {
                continue;
            }
            let file = entry.path().into_boxed_path();
            if let Some(e) = file.extension() {
                if self.codegen.should_include(&file) {
                    includes.push(file);
                    continue;
                }

                if e != FILE_EXT {
                    continue;
                }

                unchecked.push(self.load_file(&file).map_err(|e| print_err(e, &file))?);
            }
        }

        let mut files = Vec::default();
        for f in unchecked {
            let path = f.file.clone();
            files.push(
                self.check_file(&module, f, is_ubiquitous)
                    .map_err(|e| print_err(e, &path))?,
            );
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

    fn load_file(&mut self, file: &Path) -> Result<File<Expr>, Error> {
        let src = read_to_string(file).map_err(|e| Error::IO(file.into(), e))?;
        let (imports, defs) = RowsParser::parse(Rule::file, src.as_ref())
            .map_err(Box::new)
            .map_err(Error::from)
            .map(|p| self.trans.file(p))?;
        imports
            .iter()
            .try_fold((), |_, i| self.load_module(i.module.clone()))?;
        Ok(File {
            file: file.into(),
            imports,
            defs,
        })
    }

    fn check_file(
        &mut self,
        module: &Option<ModuleID>,
        file: File<Expr>,
        is_ubiquitous: bool,
    ) -> Result<File<Term>, Error> {
        let File {
            file,
            mut imports,
            defs,
        } = file;
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
        Ok(File {
            file,
            imports,
            defs,
        })
    }
}

const DEFAULT_RED_ZONE: usize = 512 * 1024;
const DEFAULT_EXTRA_STACK: usize = 4 * 1024 * 1024;

#[inline(always)]
pub fn maybe_grow<R, F: FnOnce() -> R>(f: F) -> R {
    stacker::maybe_grow(DEFAULT_RED_ZONE, DEFAULT_EXTRA_STACK, f)
}
