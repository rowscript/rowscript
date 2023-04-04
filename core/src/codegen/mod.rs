use std::fmt::{Arguments, Write};
use std::fs::write;
use std::path::PathBuf;

use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Def, Sigma};
use crate::Error;

#[cfg(feature = "codegen-es6")]
pub mod es6;
pub mod noop;

pub trait Target {
    fn filename(&self) -> &'static str;
    fn def(&self, f: &mut String, sigma: &Sigma, def: Def<Term>) -> Result<(), Error>;
}

pub struct Codegen<'a> {
    sigma: &'a Sigma,
    defs: Vec<Def<Term>>,
    path: PathBuf,
    target: Box<dyn Target>,
}

impl<'a> Codegen<'a> {
    pub fn new(
        sigma: &'a Sigma,
        defs: Vec<Def<Term>>,
        path: PathBuf,
        target: Box<dyn Target>,
    ) -> Self {
        Self {
            sigma,
            defs,
            path,
            target,
        }
    }

    pub fn package(self) -> Result<(), Error> {
        let mut buf = String::default();
        for def in self.defs {
            self.target.def(&mut buf, self.sigma, def)?;
        }
        if buf.is_empty() {
            return Ok(());
        }
        write(self.path.join(self.target.filename()), buf).map_err(Error::from)
    }
}

enum GuardKind {
    Brace,
}

impl GuardKind {
    fn left(&self) -> &'static str {
        match self {
            GuardKind::Brace => "{",
        }
    }

    fn right(&self) -> &'static str {
        match self {
            GuardKind::Brace => "}",
        }
    }
}

struct Guard<'a> {
    w: &'a mut GuardedWriter<'a>,
    k: GuardKind,
}

impl<'a> Guard<'a> {
    fn new(w: &'a mut GuardedWriter<'a>, k: GuardKind) -> Self {
        writeln!(w, "{}", k.left());
        w.indent();
        Self { w, k }
    }

    fn write_fmt(&mut self, args: Arguments) {
        self.w.write_fmt(args)
    }
}

impl<'a> Drop for Guard<'a> {
    fn drop(&mut self) {
        self.w.dedent();
        writeln!(self.w, "{}", self.k.right());
    }
}

struct GuardedWriter<'a> {
    f: &'a mut String,
    n: usize,
    indent: &'static str,
}

impl<'a> GuardedWriter<'a> {
    pub fn new(f: &'a mut String) -> Self {
        Self {
            f,
            n: Default::default(),
            indent: "  ",
        }
    }

    pub fn braces(&'a mut self) -> Guard<'a> {
        self.guard(GuardKind::Brace)
    }

    pub fn write_fmt(&mut self, args: Arguments) {
        if self.n > 0 {
            self.f
                .push_str(String::from(self.indent).repeat(self.n).as_str())
        }
        self.f.write_fmt(args).unwrap()
    }

    fn guard(&'a mut self, k: GuardKind) -> Guard<'a> {
        Guard::new(self, k)
    }

    fn indent(&mut self) {
        self.n += 1
    }

    fn dedent(&mut self) {
        if self.n == 0 {
            unreachable!()
        }
        self.n -= 1
    }
}

#[cfg(test)]
mod tests {
    use crate::codegen::GuardedWriter;

    #[test]
    fn test_guarded_writer() {
        let mut f = String::default();
        let mut w = GuardedWriter::new(&mut f);

        write!(w, "function f() ");
        {
            let mut g = w.braces();
            writeln!(g, "let a = 42;");
        }

        println!("{f}")
    }
}
