use std::fmt::Debug;

use crate::theory::{LineCol, LocalVar, Param, Syntax};

pub trait Def<T: Syntax>: Debug {
    fn loc(self) -> LineCol;
    fn name(self) -> LocalVar;
    fn tele(self) -> Vec<Param<T>>;
    fn ret(self) -> Box<T>;
}

#[derive(Debug)]
pub struct Fun<T: Syntax> {
    loc: LineCol,
    name: LocalVar,
    tele: Vec<Param<T>>,
    ret: Box<T>,
    body: Box<T>,
}

impl<T: Syntax> Fun<T> {
    pub fn new(
        loc: LineCol,
        name: LocalVar,
        tele: Vec<Param<T>>,
        ret: Box<T>,
        body: Box<T>,
    ) -> Self {
        Self {
            loc,
            name,
            tele,
            ret,
            body,
        }
    }
}

impl<T: Syntax + Debug> Def<T> for Fun<T> {
    fn loc(self) -> LineCol {
        self.loc
    }

    fn name(self) -> LocalVar {
        self.name
    }

    fn tele(self) -> Vec<Param<T>> {
        self.tele
    }

    fn ret(self) -> Box<T> {
        self.ret
    }
}
