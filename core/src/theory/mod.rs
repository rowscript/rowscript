use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};

use pest::iterators::Pair;
use pest::Span;
use uuid::Uuid;

use crate::Rule;

pub mod abs;
pub mod conc;

#[derive(Debug, Copy, Clone)]
pub struct LineCol {
    line: usize,
    col: usize,
}

impl Display for LineCol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(format!("{}:{}", self.line, self.col).as_str())
    }
}

impl<'a> From<Span<'a>> for LineCol {
    fn from(span: Span) -> Self {
        let line_col = span.start_pos().line_col();
        LineCol {
            line: line_col.0,
            col: line_col.1,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct LocalVar {
    id: Uuid,
    name: String,
}

impl Display for LocalVar {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name.as_str())
    }
}

impl<'a> From<Pair<'a, Rule>> for LocalVar {
    fn from(p: Pair<'a, Rule>) -> Self {
        Self::new(p.as_str())
    }
}

impl LocalVar {
    fn new(name: &str) -> Self {
        LocalVar {
            id: Uuid::new_v4(),
            name: name.to_string(),
        }
    }

    pub fn unbound() -> Self {
        Self::new("_")
    }

    pub fn tupled() -> Self {
        Self::new("_tupled")
    }
}

impl Hash for LocalVar {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state)
    }
}

pub trait Syntax {}

#[derive(Debug, Clone)]
pub struct Param<T: Syntax> {
    var: LocalVar,
    typ: Box<T>,
}
