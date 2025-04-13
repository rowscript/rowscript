use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::mem::discriminant;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use pest::Span;
use ustr::{Ustr, UstrMap, UstrSet};

use crate::Error;
use crate::theory::conc::data::ArgInfo;
use crate::theory::surf::Pair;

pub mod abs;
pub mod conc;
pub mod surf;

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

impl From<Span<'_>> for Loc {
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

type Name = Arc<Ustr>;

fn id(n: &Name) -> usize {
    Arc::as_ptr(n) as _
}

#[derive(Default, Debug)]
pub struct RawNameSet(UstrSet);

impl RawNameSet {
    pub fn var(&mut self, loc: Loc, v: &Var) -> Result<(), Error> {
        self.raw(loc, *v.as_str())
    }

    pub fn raw(&mut self, loc: Loc, f: Ustr) -> Result<(), Error> {
        self.0
            .insert(f)
            .then_some(())
            .ok_or(Error::DuplicateName(loc))
    }
}

#[derive(Debug, Clone, Eq)]
pub enum Var {
    Bound(Name),
    Internal(usize),
    Unbound,
    Meta(Name),
}

impl Display for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bound(n) | Self::Meta(n) => Display::fmt(n, f),
            Self::Internal(id) => write!(f, "${id}"),
            Self::Unbound => unreachable!(),
        }
    }
}

impl PartialEq<Self> for Var {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bound(l), Self::Bound(r)) | (Self::Meta(l), Self::Meta(r)) => id(l) == id(r),
            (Self::Internal(l), Self::Internal(r)) => l == r,
            _ => false,
        }
    }
}

impl Hash for Var {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        match self {
            Self::Bound(n) | Self::Meta(n) => id(n).hash(state),
            Self::Internal(id) => id.hash(state),
            Self::Unbound => unreachable!(),
        }
    }
}

const META: &str = "_";

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
    fn new(name: &str) -> Self {
        Self::Bound(Arc::new(name.into()))
    }

    fn compound(name: &str) -> Self {
        Self::new(name)
    }

    pub fn internal() -> Self {
        static NEXT_ID: AtomicUsize = AtomicUsize::new(1);
        Self::Internal(NEXT_ID.fetch_add(1, Ordering::Relaxed))
    }

    pub fn unbound() -> Self {
        Self::Unbound
    }

    pub fn meta() -> Self {
        Self::Meta(Arc::new(META.into()))
    }

    pub fn is_unbound(&self) -> bool {
        matches!(self, Self::Unbound)
    }

    pub fn is_unnamed(&self) -> bool {
        match &self {
            Self::Bound(..) => false,
            Self::Internal(..) | Self::Unbound => true,
            Self::Meta(..) => unreachable!(),
        }
    }

    pub fn tupled() -> Self {
        Self::new(TUPLED)
    }

    pub fn method(&self, m: Self) -> Self {
        Self::compound(format!("{self}${m}").as_str())
    }

    pub fn associated(&self, m: Self) -> Self {
        Self::compound(format!("{self}${m}").as_str())
    }

    pub fn ctor(&self) -> Self {
        Self::compound(format!("{self}$new").as_str())
    }

    pub fn default(&self) -> Self {
        Self::compound(format!("{self}$default").as_str())
    }

    pub fn this() -> Self {
        Self::new(THIS)
    }

    pub fn untupled_rhs(&self) -> Self {
        Self::compound(format!("{UNTUPLED_RHS_PREFIX}{self}").as_str())
    }

    pub fn untupled_ends() -> Self {
        Self::new(UNTUPLED_ENDS)
    }

    pub fn bind_let(&self) -> Self {
        Self::compound(format!("{LETS}{self}").as_str())
    }

    pub fn catch(&self) -> Self {
        match self {
            Self::Meta(id) => Self::compound(format!("catch__{id}").as_str()),
            _ => unreachable!(),
        }
    }

    pub fn catch_fn(&self) -> Self {
        match self {
            Self::Bound(name) => Self::compound(format!("catch__{name}").as_str()),
            _ => unreachable!(),
        }
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
        Self::compound(format!("{NAMESPACE_PREFIX}{self}").as_str())
    }

    pub fn list() -> Self {
        Self::new(LIST)
    }

    pub fn r#typeof() -> Self {
        Self::new(TYPEOF)
    }

    pub fn as_str(&self) -> &Ustr {
        match self {
            Self::Bound(n) => n.as_ref(),
            _ => unreachable!(),
        }
    }
}

impl From<Pair> for Var {
    fn from(p: Pair) -> Self {
        Self::new(p.as_str())
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

pub type NameMap = UstrMap<ResolvedVar>;
