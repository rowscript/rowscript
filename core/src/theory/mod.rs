use std::collections::HashSet;
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use pest::iterators::Pair;
use pest::Span;

use crate::{Error, Rule};

pub mod abs;
pub mod conc;

#[derive(Debug, Copy, Clone)]
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

#[derive(Default)]
pub struct RawNameSet(HashSet<String>);

impl RawNameSet {
    pub fn var(&mut self, loc: Loc, v: &Var) -> Result<(), Error> {
        self.raw(loc, &v.to_string())
    }

    pub fn raw(&mut self, loc: Loc, f: &String) -> Result<(), Error> {
        if !self.0.insert(f.clone()) {
            return Err(Error::DuplicateName(loc));
        }
        Ok(())
    }
}

#[derive(Clone, Eq)]
pub struct Var {
    name: Name,
}

const VPTR: &str = "__vptr";

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
        Self::new("_tupled")
    }

    pub fn untupled_right(&self) -> Self {
        Self::new(format!("_untupled_{}", self.name))
    }

    pub fn method(&self, m: Self) -> Self {
        Self::new(format!("{}.{}", self.name, m.name))
    }

    pub fn ctor(&self) -> Self {
        Self::new(format!("{}.__new", self.name))
    }

    pub fn vptr() -> Self {
        Self::new(VPTR)
    }

    pub fn vptr_type(&self) -> Self {
        Self::new(format!("{}.__vptr", self.name))
    }

    pub fn vptr_ctor(&self) -> Self {
        Self::new(format!("{}.__vptrNew", self.name))
    }

    pub fn vtbl_type(&self) -> Self {
        Self::new(format!("{}.__vtbl", self.name))
    }

    pub fn vtbl_lookup(&self) -> Self {
        Self::new(format!("{}.__vtblLookup", self.name))
    }

    pub fn id(&self) -> usize {
        Rc::as_ptr(&self.name) as _
    }

    pub fn as_str(&self) -> &str {
        self.name.as_str()
    }

    pub fn to_string(&self) -> String {
        self.as_str().to_string()
    }
}

impl Debug for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(format!("Var(\"{}\", {})", self.name, self.id()).as_str())
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name.as_str())
    }
}

impl<'a> From<Pair<'a, Rule>> for Var {
    fn from(p: Pair<'a, Rule>) -> Self {
        Self::new(p.as_str())
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

#[derive(Debug)]
pub struct VarGen(&'static str, u32);

impl VarGen {
    pub fn user_meta() -> Self {
        Self("?u", Default::default())
    }

    pub fn inserted_meta() -> Self {
        Self("?i", Default::default())
    }

    pub fn fresh(&mut self) -> Var {
        self.1 += 1;
        Var::new(format!("{}{}", self.0, self.1))
    }
}

pub trait Syntax: Display {}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ParamInfo {
    Explicit,
    Implicit,
}

#[derive(Debug, Clone)]
pub struct Param<T: Syntax> {
    var: Var,
    info: ParamInfo,
    typ: Box<T>,
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
