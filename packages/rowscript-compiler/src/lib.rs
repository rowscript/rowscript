use tree_sitter::{Language, Parser};

extern "C" {
    fn tree_sitter_rowscript() -> Language;
}

pub fn build(src: String) {
    let mut parser = Parser::new();
    let lang = unsafe { tree_sitter_rowscript() };
    parser.set_language(lang).unwrap();

    let tree = parser.parse(src, None).unwrap();
    let root_node = tree.root_node();

    println!("{}", root_node.kind());
}

#[cfg(test)]
mod tests {
    use crate::build;

    #[test]
    fn it_works() {
        build("function foo(){}".to_string());
    }
}
