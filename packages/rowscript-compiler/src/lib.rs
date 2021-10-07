use tree_sitter::{Language, Parser};

// pub mod surf;

extern "C" {
    fn tree_sitter_rowscript() -> Language;
}

pub fn parse() {
    let mut parser = Parser::new();
    let lang = unsafe { tree_sitter_rowscript() };
    parser.set_language(lang).unwrap();

    let source_code = "function foo(){}";
    let tree = parser.parse(source_code, None).unwrap();
    let root_node = tree.root_node();

    println!("{}", root_node.kind());
}

#[cfg(test)]
mod tests {
    use crate::parse;

    #[test]
    fn it_works() {
        parse();
    }
}
