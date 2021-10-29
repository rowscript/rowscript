use crate::basis::data::{Ident, Surf};
use crate::presyntax::Term::{Let, Unit, Var};
use tree_sitter::{Node, Tree};

type Label = Ident;

#[derive(Debug)]
pub enum Dir {
    L,
    R,
}

#[derive(Debug)]
pub struct Row {
    label: Label,
    typ: Type,
}

#[derive(Debug)]
pub enum Type {
    Var(Ident),
    Arr(Vec<Type>),
    Pi(Vec<Row>),
    Sigma(Vec<Row>),
    Row(Label, Box<Type>),

    Unit,
}

#[derive(Debug)]
pub enum Pred {
    Cont(Dir, Row, Row),
    Comb(Row, Row, Row),
}

#[derive(Debug)]
pub struct QualifiedType {
    preds: Vec<Pred>,
    typ: Type,
}

#[derive(Debug)]
pub struct Scheme {
    type_vars: Vec<Ident>,
    row_vars: Vec<Ident>,
    qualified: QualifiedType,
}

#[derive(Debug)]
pub enum Term {
    Var(Ident),

    Abs(Vec<Ident>, Box<Term>),
    App(Vec<Term>),

    Let(Ident, Scheme, Box<Term>, Box<Term>),

    Rec(Label, Box<Term>),
    Sel(Box<Term>, Label),

    Prj(Dir, Box<Term>),
    Cat(Vec<Term>),

    Inj(Dir, Box<Term>),
    Case(Vec<Term>),

    Unit,
}

/// Typechecking monad.
type TCM = Result<Term, String>;

impl Term {
    pub fn new(surf: Surf) -> TCM {
        Self::program(&surf, surf.tree.root_node())
    }

    fn program(surf: &Surf, node: Node) -> TCM {
        if node.kind() != "program" {
            return Err(format!(
                "syntax error on `program` node at {}",
                node.start_position()
            ));
        }

        node.children(&mut node.walk())
            .map(|n| Self::declaration(surf, n))
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

    fn declaration(surf: &Surf, node: Node) -> TCM {
        if node.kind() != "declaration" {
            return Err(format!(
                "syntax error on `declaration` node at {}",
                node.start_position()
            ));
        }

        let decl = node.child(0).unwrap();
        match decl.kind() {
            "functionDeclaration" => Self::fn_decl(surf, decl),
            _ => unimplemented!(),
        }
    }

    fn fn_decl(surf: &Surf, node: Node) -> TCM {
        let name = node.child_by_field_name("name").unwrap();

        Ok(Let(
            Ident {
                pt: name.start_position(),
                text: surf.text(&name),
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
