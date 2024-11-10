use pest::iterators::Pair;
use pest::Span;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU64, Ordering};

use crate::theory::conc::data::{ArgInfo, Expr};
use crate::{Error, Rule};

pub mod abs;
pub mod conc;

#[derive(Default, Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct Loc {
    pub line: usize,
    pub col: usize,
    pub start: usize,
    pub end: usize,
}

impl Display for Loc {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(format!("{}:{}", self.line, self.col).as_str())
    }
}

impl<'a> From<Span<'a>> for Loc {
    fn from(span: Span) -> Self {
        let line_col = span.start_pos().line_col();
        Loc {
            line: line_col.0,
            col: line_col.1,
            start: span.start(),
            end: span.end(),
        }
    }
}

#[derive(Default, Debug)]
pub struct RawNameSet(HashSet<String>);

impl RawNameSet {
    pub fn var(&mut self, loc: Loc, v: &Var) -> Result<(), Error> {
        self.raw(loc, v.to_string())
    }

    pub fn raw(&mut self, loc: Loc, f: String) -> Result<(), Error> {
        if f.as_str() != UNBOUND && !self.0.insert(f) {
            return Err(Error::DuplicateName(loc));
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ID(u64);

impl ID {
    pub fn fresh() -> Var {
        Var::new(Self::default().0.to_string())
    }
}

impl Default for ID {
    fn default() -> Self {
        static NEXT_ID: AtomicU64 = AtomicU64::new(0);
        Self(NEXT_ID.fetch_add(1, Ordering::Relaxed))
    }
}

impl Display for ID {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

#[derive(Debug, Clone, Eq)]
pub struct Var {
    raw: String,
    id: ID,
}

pub const UNBOUND: &str = "_";

pub const TUPLED: &str = "__tupled";
pub const UNTUPLED_RHS_PREFIX: &str = "__untupled_";
pub const UNTUPLED_ENDS: &str = "__untupled___ends";

pub const LETS: &str = "__lets_";

pub const THIS: &str = "this";

pub const ITER: &str = "__it";
pub const ITER_RET: &str = "__r";

pub const ARRAY: &str = "Array";

pub const ASYNC: &str = "Async";
pub const AWAIT: &str = "__await__";
pub const AWAIT_MUL: &str = "__await_mul__";
pub const AWAIT_ALL: &str = "__await_all__";
pub const AWAIT_ANY: &str = "__await_any__";

pub const NAMESPACE_PREFIX: &str = "__namespace_";

pub const LIST: &str = "List";

pub const TYPEOF: &str = "Typeof";

impl Var {
    fn new<S: Into<String>>(name: S) -> Self {
        Self {
            raw: name.into(),
            id: Default::default(),
        }
    }

    pub fn unbound() -> Self {
        Self::new(UNBOUND)
    }

    pub fn tupled() -> Self {
        Self::new(TUPLED)
    }

    pub fn method(&self, m: Self) -> Self {
        Self::new(format!("{self}${m}"))
    }

    pub fn associated(&self, m: Self) -> Self {
        Self::new(format!("{self}${m}"))
    }

    pub fn ctor(&self) -> Self {
        Self::new(format!("{self}$new"))
    }

    pub fn default(&self) -> Self {
        Self::new(format!("{self}$default"))
    }

    pub fn this() -> Self {
        Self::new(THIS)
    }

    pub fn untupled_rhs(&self) -> Self {
        Self::new(format!("{UNTUPLED_RHS_PREFIX}{self}"))
    }

    pub fn untupled_ends() -> Self {
        Self::new(UNTUPLED_ENDS)
    }

    pub fn bind_let(&self) -> Self {
        Self::new(format!("{LETS}{self}"))
    }

    pub fn instance(&self, inst: &Expr) -> Self {
        Self::new(format!("{self}__for__{inst}"))
    }

    pub fn instance_fn(&self, i: &Self, inst: &Expr) -> Self {
        Self::new(format!("{i}__for__{inst}__{self}"))
    }

    pub fn implements_fn(&self, i: &Self) -> Self {
        Self::new(format!("{i}__implements__{self}"))
    }

    pub fn catch(&self) -> Self {
        Self::new(format!("catch__{}", self.id))
    }

    pub fn catch_fn(&self) -> Self {
        Self::new(format!("catch__{}__{self}", self.id))
    }

    pub fn iterator() -> Self {
        Self::new(ITER)
    }

    pub fn iteration_result() -> Self {
        Self::new(ITER_RET)
    }

    pub fn async_effect() -> Self {
        Self::new(ASYNC)
    }

    pub fn await_one() -> Self {
        Self::new(AWAIT)
    }

    pub fn await_mul() -> Self {
        Self::new(AWAIT_MUL)
    }

    pub fn await_all() -> Self {
        Self::new(AWAIT_ALL)
    }

    pub fn await_any() -> Self {
        Self::new(AWAIT_ANY)
    }

    pub fn namespace_class(&self) -> Self {
        Self::new(format!("{NAMESPACE_PREFIX}{self}"))
    }

    pub fn list() -> Self {
        Self::new(LIST)
    }

    pub fn r#typeof() -> Self {
        Self::new(TYPEOF)
    }

    pub fn as_str(&self) -> &str {
        self.raw.as_str()
    }
}

impl From<Pair<'_, Rule>> for Var {
    fn from(p: Pair<'_, Rule>) -> Self {
        Self::new(p.as_str())
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.raw.as_str())
    }
}

impl PartialEq<Self> for Var {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Hash for Var {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.0.hash(state)
    }
}

pub trait Syntax: Display {}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ParamInfo {
    Explicit,
    Implicit,
}

impl From<ParamInfo> for ArgInfo {
    fn from(info: ParamInfo) -> Self {
        use ArgInfo::*;
        use ParamInfo::*;
        match info {
            Explicit => UnnamedExplicit,
            Implicit => UnnamedImplicit,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Param<T: Syntax> {
    pub var: Var,
    pub info: ParamInfo,
    pub typ: Box<T>,
}

pub type Tele<T> = Vec<Param<T>>;

impl<T: Syntax> Param<T> {
    pub fn tele_to_string(tele: &Tele<T>) -> String {
        tele.iter()
            .map(|p| p.to_string())
            .collect::<Vec<_>>()
            .join(" ")
    }

    pub fn predicate(typ: T) -> Self {
        Self {
            var: Var::unbound(),
            info: ParamInfo::Implicit,
            typ: Box::new(typ),
        }
    }
}

impl<T: Syntax> Display for Param<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(
            match self.info {
                ParamInfo::Explicit => format!("({}: {})", self.var, self.typ),
                ParamInfo::Implicit => format!("{{{}: {}}}", self.var, self.typ),
            }
            .as_str(),
        )
    }
}

#[derive(Debug, Copy, Clone)]
pub enum VarKind {
    Reserved,
    Inside,
    Outside,
}

#[derive(Debug, Clone)]
pub struct ResolvedVar(pub VarKind, pub Var);

pub type NameMap = HashMap<String, ResolvedVar>;
