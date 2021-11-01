use crate::parsing::diag::ErrInfo;
use crate::surf::Surf;
use std::fmt::{Display, Formatter};
use tree_sitter::{Language, Node, Parser, Tree};

mod diag;

extern "C" {
    fn tree_sitter_rowscript() -> Language;
}

pub fn parse(src: String) -> Result<Surf, String> {
    let mut parser = Parser::new();
    let lang = unsafe { tree_sitter_rowscript() };
    parser.set_language(lang).unwrap();

    match parser.parse(&src, None) {
        Some(tree) => {
            let node = tree.root_node();
            if node.has_error() {
                // TODO: Better error diagnostics.
                return Err(ErrInfo::new_string(&node, "syntax error"));
            }
            Ok(Surf::new(src, tree))
        }
        None => Err("parse error".to_string()),
    }
}

#[cfg(test)]
mod tests;
