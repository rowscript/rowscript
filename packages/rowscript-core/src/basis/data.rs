use std::fmt::Formatter;
use tree_sitter::Point;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ident {
    pub(crate) text: String,
    pub(crate) pt: Option<Point>,
}

impl Ident {
    pub fn new(text: String, pt: Point) -> Ident {
        Ident { text, pt: Some(pt) }
    }

    pub fn new_builtin(text: String) -> Ident {
        Ident { text, pt: None }
    }
}

impl std::fmt::Display for Ident {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.pt {
            Some(pt) => write!(f, "(ident {:?} '({} {}))", self.text, pt.row, pt.column),
            None => write!(f, "(ident {:?})", self.text),
        }
    }
}

pub type Ix = i64;
pub type Lvl = i64;
