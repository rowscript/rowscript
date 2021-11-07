use tree_sitter::Point;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident {
    pub pt: Point,
    pub text: String,
}
