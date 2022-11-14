use std::fmt::Debug;

use crate::theory::abs::def::Body::Fun;
use crate::theory::{LineCol, LocalVar, Param, Syntax};

#[derive(Debug)]
pub struct Def<T: Syntax> {
    pub loc: LineCol,
    pub name: LocalVar,
    pub tele: Vec<Param<T>>,
    pub ret: Box<T>,
    pub body: Body<T>,
}

#[derive(Debug)]
pub enum Body<T: Syntax> {
    Fun(Box<T>),
}

impl<T: Syntax> Def<T> {
    pub fn fun(
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
            body: Fun(body),
        }
    }
}
