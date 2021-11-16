use std::fmt::{Display, Formatter};
use tree_sitter::Node;

#[derive(Debug)]
pub struct Diag {
    line: usize,
    col: usize,
    msg: &'static str,
}

impl Diag {
    pub fn new(node: &Node, msg: &'static str) -> Diag {
        let pt = node.start_position();
        Diag {
            line: pt.row + 1,
            col: pt.column + 1,
            msg,
        }
    }

    pub fn new_string(node: &Node, msg: &'static str) -> String {
        Self::new(node, msg).to_string()
    }
}

impl Display for Diag {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.col, self.msg)
    }
}
