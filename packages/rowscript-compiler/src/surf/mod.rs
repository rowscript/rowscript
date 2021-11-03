use crate::surf::diag::ErrInfo;
use rowscript_core::basis::data::Ident;
use rowscript_core::presyntax::data::Term::{Let, Unit, Var};
use rowscript_core::presyntax::data::Type::Arr;
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

    fn ident(&self, node: &Node) -> Ident {
        Ident {
            pt: node.start_position(),
            text: self.text(node),
        }
    }

    pub fn to_presyntax(&self) -> Term {
        self.program(self.tree.root_node())
    }

    fn program(&self, node: Node) -> Term {
        node.children(&mut node.walk())
            .map(|n| self.declaration(n))
            .reduce(|a, b| match a {
                Let(name, typ, exp, _) => Let(name, typ, exp, Box::from(b)),
                _ => unreachable!(),
            })
            .unwrap_or(Unit)
    }

    fn declaration(&self, node: Node) -> Term {
        let decl = node.child(0).unwrap();
        match decl.kind() {
            "functionDeclaration" => self.fn_decl(decl),
            _ => unimplemented!(),
        }
    }

    fn fn_decl(&self, node: Node) -> Term {
        let name = node.child_by_field_name("name").unwrap();
        let (arg_type, arg_idents) = self.decl_sig(node.child_by_field_name("sig").unwrap());

        Let(
            self.ident(&name),
            Scheme {
                type_vars: node
                    .child_by_field_name("scheme")
                    .map(|n| {
                        n.named_children(&mut n.walk())
                            .map(|n| self.ident(&n))
                            .collect()
                    })
                    .unwrap_or(Default::default()),
                // TODO: Determine type/row variables.
                row_vars: vec![],
                qualified: QualifiedType {
                    preds: vec![],
                    typ: Arr(vec![
                        arg_type,
                        node.child_by_field_name("ret")
                            .map_or(Type::Unit, |n| self.type_expr(n)),
                    ]),
                },
            },
            // TODO
            Box::from(self.stmt_blk(node.child_by_field_name("body").unwrap())),
            Box::from(Unit),
        )
    }

    fn decl_sig(&self, node: Node) -> (Type, Vec<Ident>) {
        match node.named_child_count() {
            0 => (Type::Unit, Default::default()),
            1 => {
                let arg = node.named_child(0).unwrap();
                (self.type_expr(arg), vec![self.ident(&arg)])
            }
            _ => {
                let mut types = vec![];
                let mut args = vec![];
                node.named_children(&mut node.walk()).for_each(|n| {
                    let id = n.child(0).unwrap();
                    let typ = n.child(2).unwrap();
                    args.push(self.ident(&id));
                    types.push(self.type_expr(typ));
                });
                (Type::Tuple(types), args)
            }
        }
    }

    fn type_expr(&self, node: Node) -> Type {
        // TODO
        unimplemented!()
    }

    fn stmt_blk(&self, node: Node) -> Term {
        // TODO
        unimplemented!()
    }
}
