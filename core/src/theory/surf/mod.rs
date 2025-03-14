use std::path::Path;

use pest::Parser as _;
use pest::iterators::{Pair as ParserPair, Pairs as ParserPairs};
use pest_derive::Parser as PestParser;

use crate::theory::abs::def::Def;
use crate::theory::conc::data::Expr;
use crate::theory::conc::load::Import;
use crate::theory::surf::trans::Trans;
use crate::{Error, Src, print_err};

mod trans;

pub type Pair = ParserPair<'static, Rule>;
pub type Pairs = ParserPairs<'static, Rule>;

#[derive(PestParser)]
#[grammar = "theory/surf/grammar.pest"]
struct RowsParser;

#[derive(Default, Clone)]
pub struct Parser {
    trans: Trans,
}

pub struct Parsed {
    pub imports: Box<[Import]>,
    pub defs: Box<[Def<Expr>]>,
}

impl Parser {
    pub fn parse(&mut self, path: &Path, src: Src) -> Result<Parsed, Error> {
        RowsParser::parse(Rule::file, src)
            .map_err(|e| print_err(Box::new(e).into(), path, src))
            .map(|p| self.trans.file(p))
    }
}
