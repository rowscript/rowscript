use ustr::Ustr;

mod parser;

enum Expr {
    Number(Ustr),
    String(Ustr),
}
