use pest::iterators::Pair;

use crate::theory::abs::def::{Def, Fun};
use crate::theory::conc::data::Expr;
use crate::theory::conc::data::Expr::{Unit, TT};
use crate::theory::{LineCol, LocalVar};
use crate::{Driver, Rule};

pub struct Trans<'a> {
    file: &'a str,
}

impl<'a> From<Driver<'a>> for Trans<'a> {
    fn from(d: Driver<'a>) -> Self {
        Self { file: d.file }
    }
}

impl<'a> Trans<'a> {
    pub fn fn_def(&self, f: Pair<Rule>) -> Box<dyn Def<Expr>> {
        let loc = LineCol::from(f.as_span());
        let id = f.into_inner().next().unwrap();
        // TODO
        Box::new(Fun::new(
            loc,
            LocalVar::from(id),
            Default::default(),
            Box::new(Unit(loc)),
            Box::new(TT(loc)),
        ))
    }
}
