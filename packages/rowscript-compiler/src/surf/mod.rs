use crate::surf::diag::ErrInfo;
use rowscript_core::basis::data::Ident;
use rowscript_core::presyntax::data::Term::{Let, Unit, Var};
use rowscript_core::presyntax::data::{QualifiedType, Scheme, Term, Type};
use tree_sitter::{Language, Node, Parser, Tree};

mod diag;

#[cfg(test)]
mod tests;

extern "C" {
    fn tree_sitter_rowscript() -> Language;
}

/// Surface syntax.
#[derive(Debug)]
pub struct Surf {
    src: String,
    pub tree: Tree,
}

impl Surf {
    pub fn new(src: String) -> Result<Surf, String> {
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
                Ok(Surf { src, tree })
            }
            None => Err("parse error".to_string()),
        }
    }

    fn text(&self, node: &Node) -> String {
        self.src[node.start_byte()..node.end_byte()].into()
    }

    pub fn to_presyntax(&self) -> Result<Term, String> {
        self.program(self.tree.root_node())
    }

    fn program(&self, node: Node) -> Result<Term, String> {
        if node.kind() != "program" {
            return Err(format!(
                "syntax error on `program` node at {}",
                node.start_position()
            ));
        }

        node.children(&mut node.walk())
            .map(|n| self.declaration(n))
            .reduce(|a, b| match a {
                Ok(x) => match x {
                    Let(name, typ, exp, _) => match b {
                        Ok(y) => Ok(Let(name, typ, exp, Box::from(y))),
                        Err(_) => b,
                    },
                    _ => unreachable!(),
                },
                Err(_) => a,
            })
            .unwrap_or(Ok(Unit))
    }

    fn declaration(&self, node: Node) -> Result<Term, String> {
        if node.kind() != "declaration" {
            return Err(format!(
                "syntax error on `declaration` node at {}",
                node.start_position()
            ));
        }

        let decl = node.child(0).unwrap();
        match decl.kind() {
            "functionDeclaration" => self.fn_decl(decl),
            _ => unimplemented!(),
        }
    }

    fn fn_decl(&self, node: Node) -> Result<Term, String> {
        let name = node.child_by_field_name("name").unwrap();

        Ok(Let(
            Ident {
                pt: name.start_position(),
                text: self.text(&name),
            },
            // TODO
            Scheme {
                type_vars: vec![],
                row_vars: vec![],
                qualified: QualifiedType {
                    preds: vec![],
                    typ: Type::Unit,
                },
            },
            Box::new(Var(Ident {
                pt: node.start_position(),
                text: "x".into(),
            })),
            Box::from(Unit),
        ))
    }
}
