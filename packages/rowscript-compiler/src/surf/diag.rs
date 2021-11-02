use std::fmt::{Display, Formatter};
use tree_sitter::Node;

pub struct ErrInfo {
    line: usize,
    col: usize,
    msg: &'static str,
}

impl ErrInfo {
    pub fn new(node: &Node, msg: &'static str) -> ErrInfo {
        let pt = node.start_position();
        ErrInfo {
            line: pt.row + 1,
            col: pt.column + 1,
            msg,
        }
    }

    pub fn new_string(node: &Node, msg: &'static str) -> String {
        Self::new(node, msg).to_string()
    }
}

impl Display for ErrInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.col, self.msg)
    }
}
