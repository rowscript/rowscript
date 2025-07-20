use ustr::Ustr;

#[allow(dead_code)]
mod syntax;

#[cfg(test)]
mod tests;

#[allow(dead_code)]
struct Uri(Ustr);

impl Default for Uri {
    fn default() -> Self {
        Self("<stdin>".into())
    }
}

#[allow(dead_code)]
#[derive(Default)]
struct Loc {
    uri: Uri,
}

#[allow(dead_code)]
enum Diag {
    SyntaxError(Loc),
}
