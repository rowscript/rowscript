use crate::theory::base::{LineCol, LocalVar, Param, Syntax};

pub trait Def<T: Syntax> {
    fn source(self) -> LineCol;
    fn tele(self) -> [Param<T>];
    fn name(self) -> LocalVar;
    fn ret(self) -> Box<T>;
}
