use tree_sitter::{Node, Point, Tree};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident {
    pub pt: Point,
    pub text: String,
}
