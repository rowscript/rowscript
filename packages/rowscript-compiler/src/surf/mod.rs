use crate::surf::diag::ErrInfo;
use crate::surf::SurfError::ParsingError;
use rowscript_core::basis::data::Ident;
use rowscript_core::presyntax::data::Term::{
    Abs, App, Array, Bool, Case, Cat, If, Let, Num, PrimRef, Rec, Sel, Str, Subs, TLet, Tuple,
    Unit, Var,
};
use rowscript_core::presyntax::data::{QualifiedType, Row, Scheme, Term, Type};
use std::collections::HashMap;
use thiserror::Error;
use tree_sitter::{Language, Node, Parser, Tree};

mod diag;

#[cfg(test)]
mod tests;

#[derive(Debug, Error)]
pub enum SurfError {
    #[error("Tree-sitter backend language error")]
    LanguageError(#[from] tree_sitter::LanguageError),
    #[error("General parsing error")]
    ParsingError(String),
    #[error("Syntax error")]
    SyntaxError { info: ErrInfo },
}

type SurfM<T> = Result<T, SurfError>;

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
                for i in (0..$node.named_child_count()).step_by(2) {
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
    tree: Tree,
}

impl Surf {
    pub fn new(src: String) -> SurfM<Surf> {
        let mut parser = Parser::new();
        let lang = unsafe { tree_sitter_rowscript() };
        parser.set_language(lang)?;
        parser
            .parse(&src, None)
            .ok_or(ParsingError("unexpected empty parsing tree".to_string()))
            .and_then(|tree| {
                let node = tree.root_node();
                if node.has_error() {
                    // TODO: Better error diagnostics.
                    let info = ErrInfo::new(&node, "syntax error");
                    return Err(SurfError::SyntaxError { info });
                }
                Ok(Surf { src, tree })
            })
    }

    fn text(&self, node: &Node) -> String {
        self.src[node.start_byte()..node.end_byte()].into()
    }

    fn ident(&self, node: Node) -> Ident {
        Ident::new(self.text(&node), node.start_position())
    }

    fn prim_ref(&self, node: Node) -> Term {
        PrimRef(self.ident(node), Scheme::Meta(node.start_position()))
    }

    fn expr_from_fields<const L: usize>(&self, node: Node, fields: [&str; L]) -> [Term; L] {
        fields.map(|name| self.expr(node.child_by_field_name(name).unwrap()))
    }

    pub fn to_presyntax(&self) -> Term {
        self.prog(self.tree.root_node())
    }

    fn prog(&self, node: Node) -> Term {
        node.children(&mut node.walk())
            .map(|n| self.decl(n))
            .collect::<Vec<_>>()
            .into_iter()
            .rfold(Unit, move |acc, a| match a {
                Let(name, typ, exp, _) => Let(name, typ, exp, Box::from(acc)),
                TLet(name, typ, _) => TLet(name, typ, Box::from(acc)),
                _ => unreachable!(),
            })
    }

    fn decl(&self, node: Node) -> Term {
        let decl = node.child(0).unwrap();
        match decl.kind() {
            "functionDeclaration" => self.fn_decl(decl),
            "classDeclaration" => todo!(),
            "typeAliasDeclaration" => self.type_alias_decl(decl),
            _ => unreachable!(),
        }
    }

    fn type_alias_decl(&self, node: Node) -> Term {
        let name = self.ident(node.child_by_field_name("name").unwrap());
        let typ = self.type_scheme(node.child_by_field_name("target").unwrap());
        TLet(name, typ, Box::from(Unit))
    }

    fn fn_decl(&self, node: Node) -> Term {
        let name = node.child_by_field_name("name").unwrap();
        let (arg_type, arg_idents) = self.decl_sig(node.child_by_field_name("sig").unwrap());

        Let(
            self.ident(name),
            Scheme::Scm {
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

    fn type_scheme(&self, node: Node) -> Scheme {
        // TODO: Determine type/row variables.
        let mut type_vars = vec![];
        if node.child_count() == 2 {
            let b = node.child(0).unwrap();
            type_vars = b
                .named_children(&mut b.walk())
                .map(|n| self.ident(n))
                .collect();
        }
        Scheme::Scm {
            type_vars,
            row_vars: vec![],
            qualified: QualifiedType {
                preds: vec![],
                typ: self.type_expr(node.children(&mut node.walk()).last().unwrap()),
            },
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
            "stringType" => Type::Str,
            "numberType" => Type::Num,
            "booleanType" => Type::Bool,
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
        let stmt = self.stmt(node.named_children(&mut node.walk()).last().unwrap());
        (0..node.named_child_count() - 1)
            .map(|i| node.named_child(i).unwrap())
            .map(|n| self.var_decl(n))
            .rfold(stmt, |acc, a| match a {
                Let(name, typ, exp, _) => Let(name, typ, exp, Box::from(acc)),
                _ => unreachable!(),
            })
    }

    fn var_decl(&self, node: Node) -> Term {
        Let(
            self.ident(node.child_by_field_name("name").unwrap()),
            node.child_by_field_name("type").map_or_else(
                || Scheme::Meta(node.start_position()),
                |n| Scheme::new_schemeless(self.type_expr(n)),
            ),
            Box::from(self.expr(node.child_by_field_name("value").unwrap())),
            Box::from(Unit),
        )
    }

    fn if_stmt(&self, node: Node) -> Term {
        let cond = node
            .child_by_field_name("cond")
            .unwrap()
            .named_child(0)
            .unwrap();
        let then = node.child_by_field_name("then").unwrap();
        let el = node.child_by_field_name("else").unwrap();
        If(
            Box::from(self.expr(cond)),
            Box::from(self.stmt_blk(then, vec![])),
            Box::from(self.stmt_blk(el, vec![])),
        )
    }

    fn switch_stmt(&self, node: Node) -> Term {
        let arg = self.expr(
            node.child_by_field_name("value")
                .unwrap()
                .named_child(0)
                .unwrap(),
        );
        let body = self.switch_body(node.child_by_field_name("body").unwrap());
        App(Box::from(body), Box::from(arg))
    }

    fn switch_body(&self, node: Node) -> Term {
        let mut cases = HashMap::new();
        let mut default = None;
        node.named_children(&mut node.walk())
            .for_each(|n| match n.kind() {
                "switchCase" => {
                    let (name, abs) = self.switch_case(n);
                    cases.insert(name, abs);
                }
                "switchDefault" => {
                    default = Some(self.stmt(n.named_child(0).unwrap()));
                }
                _ => unreachable!(),
            });
        Case(cases, Box::from(default))
    }

    fn switch_case(&self, node: Node) -> (Ident, Term) {
        let [lbl, var] =
            ["label", "variable"].map(|f| self.ident(node.child_by_field_name(f).unwrap()));
        let stmt = self.stmt(node.child_by_field_name("statement").unwrap());
        (lbl, Abs(vec![var], Box::from(stmt)))
    }

    fn try_stmt(&self, node: Node) -> Term {
        todo!()
    }

    fn do_stmt(&self, node: Node) -> Term {
        todo!()
    }

    fn ret_stmt(&self, node: Node) -> Term {
        node.named_child(0).map_or(Unit, |n| self.expr(n))
    }

    fn throw_stmt(&self, node: Node) -> Term {
        todo!()
    }

    fn expr(&self, node: Node) -> Term {
        let e = node.child(0).unwrap();
        match e.kind() {
            "primaryExpression" => self.primary_expr(e),
            "unaryExpression" => self.unary_expr(e),
            "binaryExpression" => self.binary_expr(e),
            "ternaryExpression" => self.ternary_expr(e),
            "newExpression" => self.new_expr(e),
            _ => unreachable!(),
        }
    }

    fn primary_expr(&self, node: Node) -> Term {
        let e = node.child(0).unwrap();
        match e.kind() {
            "subscriptExpression" => self.subs_expr(e),
            "memberExpression" => self.member_expr(e),
            "parenthesizedExpression" => self.expr(e.named_child(0).unwrap()),
            "identifier" => Var(self.ident(e)),
            "this" => todo!(),
            "super" => todo!(),
            "number" => Num(self.text(&e)),
            "string" | "regex" => Str(self.text(&e)),
            "false" => Bool(false),
            "true" => Bool(true),
            "object" => self.obj_expr(e),
            "array" => self.array_expr(e),
            "arrowFunction" => self.arrow_func(e),
            "callExpression" => self.call_expr(e),
            _ => unreachable!(),
        }
    }

    fn subs_expr(&self, node: Node) -> Term {
        let [o, i] = self
            .expr_from_fields(node, ["object", "index"])
            .map(Box::from);
        Subs(o, i)
    }

    fn member_expr(&self, node: Node) -> Term {
        let n = node.child_by_field_name("object").unwrap();
        Sel(
            Box::from(match n.kind() {
                "expression" => self.expr(n),
                "primaryExpression" => self.primary_expr(n),
                _ => unreachable!(),
            }),
            self.ident(node.child_by_field_name("property").unwrap()),
        )
    }

    fn obj_expr(&self, node: Node) -> Term {
        match node.named_child_count() {
            0 => Unit,
            1 => self.pair(node.named_child(0).unwrap()),
            _ => Cat(node
                .named_children(&mut node.walk())
                .map(|n| self.pair(n))
                .collect()),
        }
    }

    fn pair(&self, node: Node) -> Term {
        Rec(
            self.ident(node.child_by_field_name("key").unwrap()),
            Box::from(self.expr(node.child_by_field_name("value").unwrap())),
        )
    }

    fn array_expr(&self, node: Node) -> Term {
        Array(
            node.named_children(&mut node.walk())
                .map(|n| self.expr(n))
                .collect(),
        )
    }

    fn arrow_func(&self, node: Node) -> Term {
        let x = node.child_by_field_name("parameter").unwrap();
        let idents = x
            .named_children(&mut x.walk())
            .map(|n| self.ident(n))
            .collect();
        let body = node.child_by_field_name("body").unwrap();
        match body.kind() {
            "expression" => Abs(idents, Box::from(self.expr(body))),
            "statementBlock" => self.stmt_blk(body, idents),
            _ => unreachable!(),
        }
    }

    fn call_expr(&self, node: Node) -> Term {
        let x = node.child_by_field_name("arguments").unwrap();
        App(
            Box::from(self.expr(node.child_by_field_name("function").unwrap())),
            Box::from(match x.named_child_count() {
                0 => Unit,
                1 => self.expr(x.named_child(0).unwrap()),
                _ => Tuple(
                    x.named_children(&mut x.walk())
                        .map(|n| self.expr(n))
                        .collect(),
                ),
            }),
        )
    }

    fn unary_expr(&self, node: Node) -> Term {
        App(
            Box::from(self.prim_ref(node.child(0).unwrap())),
            Box::from(self.expr(node.child(1).unwrap())),
        )
    }

    fn binary_expr(&self, node: Node) -> Term {
        let [l, r] = self.expr_from_fields(node, ["left", "right"]);
        App(
            Box::from(self.prim_ref(node.child(1).unwrap())),
            Box::new(Tuple(vec![l, r])),
        )
    }

    fn ternary_expr(&self, node: Node) -> Term {
        let [c, t, e] = self
            .expr_from_fields(node, ["cond", "then", "else"])
            .map(Box::from);
        If(c, t, e)
    }

    fn new_expr(&self, node: Node) -> Term {
        todo!()
    }
}
