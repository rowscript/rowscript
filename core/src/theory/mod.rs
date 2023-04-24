use std::collections::HashSet;
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use pest::Span;

use crate::theory::conc::data::ArgInfo;
use crate::Error;

pub mod abs;
pub mod conc;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
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

type Name = Rc<String>;

#[derive(Default, Debug)]
pub struct RawNameSet(HashSet<String>);

impl RawNameSet {
    pub fn var(&mut self, loc: Loc, v: &Var) -> Result<(), Error> {
        self.raw(loc, v.to_string())
    }

    pub fn raw(&mut self, loc: Loc, f: String) -> Result<(), Error> {
        if !self.0.insert(f) {
            return Err(Error::DuplicateName(loc));
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Eq)]
pub struct Var {
    name: Name,
}

pub const TUPLED: &str = "_tupled";
pub const UNTUPLED_RHS: &str = "_untupled_";

pub const VPTR: &str = "__vptr";
pub const VTBL_LOOKUP: &str = "__vtblLookup";

pub const THIS: &str = "this";

impl Var {
    fn new<S: AsRef<str>>(name: S) -> Self {
        Self {
            name: Rc::new(name.as_ref().to_string()),
        }
    }

    pub fn unbound() -> Self {
        Self::new("_")
    }

    pub fn tupled() -> Self {
        Self::new(TUPLED)
    }

    pub fn this() -> Self {
        Self::new(THIS)
    }

    pub fn untupled_rhs(&self) -> Self {
        Self::new(format!("{UNTUPLED_RHS}{self}"))
    }

    pub fn method(&self, m: Self) -> Self {
        Self::new(format!("{self}__{m}"))
    }

    pub fn ctor(&self) -> Self {
        Self::new(format!("{self}__new"))
    }

    pub fn vptr() -> Self {
        Self::new(VPTR)
    }

    pub fn vptr_type(&self) -> Self {
        Self::new(format!("{self}__vptr"))
    }

    pub fn vptr_ctor(&self) -> Self {
        Self::new(format!("{self}__vptrNew"))
    }

    pub fn vtbl_type(&self) -> Self {
        Self::new(format!("{self}__vtbl"))
    }

    pub fn vtbl_lookup(&self) -> Self {
        Self::new(format!("{self}{VTBL_LOOKUP}"))
    }

    pub fn implements(&self, im: &Self) -> Self {
        Self::new(format!("{self}__for__{im}"))
    }

    pub fn implement_func(&self, i: &Self, im: &Self) -> Self {
        Self::new(format!("{i}__for__{im}__{self}"))
    }

    pub fn id(&self) -> usize {
        Rc::as_ptr(&self.name) as _
    }

    pub fn as_str(&self) -> &str {
        self.name.as_str()
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name.as_str())
    }
}

impl PartialEq<Self> for Var {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}

impl Hash for Var {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id().hash(state)
    }
}

#[derive(Debug, Default)]
pub struct VarGen(u64);

impl VarGen {
    pub fn fresh(&mut self) -> Var {
        self.0 += 1;
        Var::new(self.0.to_string())
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
