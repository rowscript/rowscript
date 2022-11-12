use pest::iterators::Pair;

use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::Rule;

pub struct Trans {
    file: String,
}

impl Trans {
    pub fn new(file: String) -> Self {
        Self { file }
    }

    pub fn fn_def(self, f: Pair<Rule>) -> Box<dyn Def<Expr>> {
        panic!("TODO")
    }
}
