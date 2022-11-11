use pest::error::Error;
use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "surf/rows.pest"]
pub struct Surf;

pub fn parse_text(text: &str) -> Result<(), Error<Rule>> {
    let file = Surf::parse(Rule::file, text)?.next().unwrap();
    Ok(())
}

#[cfg(test)]
mod tests;
