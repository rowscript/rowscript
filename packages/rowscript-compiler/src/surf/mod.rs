use crate::surf::diag::ErrInfo;
use rowscript_core::basis::data::Ident;
use rowscript_core::presyntax::data::Term::{Let, Unit, Var};
use rowscript_core::presyntax::data::{QualifiedType, Row, Scheme, Term, Type};
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

    fn ident(&self, node: Node) -> Ident {
        Ident {
            pt: node.start_position(),
            text: self.text(&node),
        }
    }

    pub fn to_presyntax(&self) -> Term {
        self.prog(self.tree.root_node())
    }

    fn prog(&self, node: Node) -> Term {
        node.children(&mut node.walk())
            .map(|n| self.decl(n))
            .reduce(|a, b| match a {
                Let(name, typ, exp, _) => Let(name, typ, exp, Box::from(b)),
                _ => unreachable!(),
            })
            .unwrap_or(Unit)
    }

    fn decl(&self, node: Node) -> Term {
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
            self.ident(name),
            Scheme {
                type_vars: node
                    .child_by_field_name("scheme")
                    .map(|n| {
                        n.named_children(&mut n.walk())
                            .map(|n| self.ident(n))
                            .collect()
                    })
                    .unwrap_or(Default::default()),
                // TODO: Determine type/row variables.
                row_vars: vec![],
                qualified: QualifiedType {
                    preds: vec![],
                    typ: Type::Arrow(vec![
                        arg_type,
                        node.child_by_field_name("ret")
                            .map_or(Type::Unit, |n| self.type_expr(n)),
                    ]),
                },
            },
            // TODO
            Box::from(self.stmt_blk(node.child_by_field_name("body").unwrap(), arg_idents)),
            Box::from(Unit),
        )
    }

    fn decl_sig(&self, node: Node) -> (Type, Vec<Ident>) {
        match node.named_child_count() {
            0 => (Type::Unit, Default::default()),
            1 => {
                let n = node.named_child(0).unwrap();
                let arg = n.named_child(0).unwrap();
                let typ = n.named_child(1).unwrap();
                (self.type_expr(typ), vec![self.ident(arg)])
            }
            _ => {
                let mut types = vec![];
                let mut args = vec![];
                node.named_children(&mut node.walk()).for_each(|n| {
                    let arg = n.named_child(0).unwrap();
                    let typ = n.named_child(1).unwrap();
                    args.push(self.ident(arg));
                    types.push(self.type_expr(typ));
                });
                (Type::Tuple(types), args)
            }
        }
    }

    fn type_expr(&self, node: Node) -> Type {
        match node.named_child_count() {
            1 => self.type_term(node.named_child(0).unwrap()),
            _ => Type::Arrow(
                node.named_children(&mut node.walk())
                    .map(|n| self.type_term(n))
                    .collect::<Vec<Type>>(),
            ),
        }
    }

    fn type_term(&self, node: Node) -> Type {
        let tm = node.child(0).unwrap();
        match tm.kind() {
            "recordType" => self.record_type(tm),
            "variantType" => self.variant_type(tm),
            "arrayType" => self.array_type(tm),
            "tupleType" => self.tuple_type(tm),
            "stringType" => Type::String,
            "numberType" => Type::Number,
            "booleanType" => Type::Boolean,
            "bigintType" => Type::BigInt,
            "identifier" => Type::Var(self.ident(tm)),
            _ => unreachable!(),
        }
    }

    fn record_type(&self, node: Node) -> Type {
        if node.child(0).unwrap().kind() == "{}" {
            return Type::Record(vec![], false);
        }
        if node.child(1).unwrap().kind() == "..." {
            return Type::Record(vec![], true);
        }
        let mut rows = vec![];
        for i in 0..node.named_child_count() {
            let ident = node.named_child(i).unwrap();
            let typ = node.named_child(i + 1).unwrap();
            rows.push(Row {
                label: self.ident(ident),
                typ: self.type_expr(typ),
            });
        }
        // FIXME: No `...` in the original paper! What you doing man?
        Type::Record(
            rows,
            node.child(node.child_count() - 2).unwrap().kind() == "...",
        )
    }

    fn variant_type(&self, node: Node) -> Type {
        // TODO
        unimplemented!()
    }

    fn array_type(&self, node: Node) -> Type {
        // TODO
        unimplemented!()
    }

    fn tuple_type(&self, node: Node) -> Type {
        // TODO
        unimplemented!()
    }

    fn stmt_blk(&self, node: Node, idents: Vec<Ident>) -> Term {
        // TODO
        unimplemented!()
    }
}
