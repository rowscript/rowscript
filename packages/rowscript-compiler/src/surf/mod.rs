use crate::surf::diag::ErrInfo;
use rowscript_core::basis::data::Ident;
use rowscript_core::presyntax::data::Term::{Abs, Let, Unit, Var};
use rowscript_core::presyntax::data::{QualifiedType, Row, Scheme, Term, Type};
use tree_sitter::{Language, Node, Parser, Tree};

mod diag;

#[cfg(test)]
mod tests;

extern "C" {
    fn tree_sitter_rowscript() -> Language;
}

macro_rules! row_type {
    ($self:ident,$e:expr,$node:ident) => {
        match $node.named_child_count() {
            0 => $e(Row::Labeled(vec![])),
            1 => $e(Row::Var($self.ident($node.named_child(0).unwrap()))),
            _ => {
                let mut rows = vec![];
                for i in 0..$node.named_child_count() / 2 {
                    let ident = $node.named_child(i).unwrap();
                    let typ = $node.named_child(i + 1).unwrap();
                    rows.push(($self.ident(ident), $self.type_expr(typ)));
                }
                $e(Row::Labeled(rows))
            }
        }
    };
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
        row_type!(self, Type::Record, node)
    }

    fn variant_type(&self, node: Node) -> Type {
        row_type!(self, Type::Variant, node)
    }

    fn array_type(&self, node: Node) -> Type {
        Type::Array(Box::from(self.type_expr(node.named_child(0).unwrap())))
    }

    fn tuple_type(&self, node: Node) -> Type {
        Type::Tuple(
            node.named_children(&mut node.walk())
                .map(|n| self.type_expr(n))
                .collect(),
        )
    }

    fn stmt_blk(&self, node: Node, idents: Vec<Ident>) -> Term {
        node.named_child(0)
            .map_or_else(|| Abs(idents, Box::from(Unit)), |n| self.stmt(n))
    }

    fn stmt(&self, node: Node) -> Term {
        let s = node.child(0).unwrap();
        match s.kind() {
            "lexicalDeclaration" => self.lex_decl(s),
            "ifStatement" => self.if_stmt(s),
            "switchStatement" => self.switch_stmt(s),
            "tryStatement" => self.try_stmt(s),
            "doStatement" => self.do_stmt(s),
            "returnStatement" => self.ret_stmt(s),
            "throwStatement" => self.throw_stmt(s),
            _ => unreachable!(),
        }
    }

    fn lex_decl(&self, node: Node) -> Term {
        // TODO
        unimplemented!()
    }

    fn if_stmt(&self, node: Node) -> Term {
        // TODO
        unimplemented!()
    }

    fn switch_stmt(&self, node: Node) -> Term {
        // TODO
        unimplemented!()
    }

    fn try_stmt(&self, node: Node) -> Term {
        // TODO
        unimplemented!()
    }

    fn do_stmt(&self, node: Node) -> Term {
        // TODO
        unimplemented!()
    }

    fn ret_stmt(&self, node: Node) -> Term {
        node.named_child(0).map_or(Unit, |n| self.expr(n))
    }

    fn throw_stmt(&self, node: Node) -> Term {
        // TODO
        unimplemented!()
    }

    fn expr(&self, node: Node) -> Term {
        // TODO
        unimplemented!()
    }
}
