use tree_sitter::{Language, Node, Parser, Tree};

use std::fmt::{Display, Formatter};

extern "C" {
    fn tree_sitter_rowscript() -> Language;
}

struct ErrInfo {
    line: usize,
    col: usize,
    msg: &'static str,
}

impl ErrInfo {
    fn new(node: &Node, msg: &'static str) -> ErrInfo {
        let pt = node.start_position();
        ErrInfo {
            line: pt.row + 1,
            col: pt.column + 1,
            msg,
        }
    }

    fn new_string(node: &Node, msg: &'static str) -> String {
        Self::new(node, msg).to_string()
    }
}

impl Display for ErrInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.col, self.msg)
    }
}

pub fn parse(src: String) -> Result<Tree, String> {
    let mut parser = Parser::new();
    let lang = unsafe { tree_sitter_rowscript() };
    parser.set_language(lang).unwrap();

    match parser.parse(src, None) {
        Some(tree) => {
            let node = tree.root_node();
            if node.has_error() {
                // TODO: Better error diagnostics.
                return Err(ErrInfo::new_string(&node, "syntax error"));
            }
            Ok(tree)
        }
        None => Err("parse error".to_string()),
    }
}

#[cfg(test)]
mod tests;
