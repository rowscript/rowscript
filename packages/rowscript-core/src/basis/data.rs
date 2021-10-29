use tree_sitter::{Node, Point, Tree};

/// Surface syntax.
pub struct Surf {
    src: String,
    pub tree: Tree,
}

impl Surf {
    pub fn new(src: String, tree: Tree) -> Self {
        Surf { src, tree }
    }

    pub fn text(&self, node: &Node) -> String {
        self.src[node.start_byte()..node.end_byte()].into()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident {
    pub pt: Point,
    pub text: String,
}
