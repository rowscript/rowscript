use ustr::Ustr;

pub(crate) mod parser;

enum Expr {
    Number(Ustr),
    String(Ustr),
}
