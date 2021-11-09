use tree_sitter::Point;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident {
    text: String,
    pt: Option<Point>,
}

impl Ident {
    pub fn new(text: String, pt: Point) -> Ident {
        Ident { text, pt: Some(pt) }
    }

    pub fn new_builtin(text: String) -> Ident {
        Ident { text, pt: None }
    }
}
