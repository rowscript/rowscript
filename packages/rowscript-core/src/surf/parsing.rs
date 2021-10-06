use pest::prec_climber::{Assoc, Operator, PrecClimber};
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "surf/grammar.pest"]
struct Surf;

#[allow(non_camel_case_types)]
#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Rule {
    program,

    primary_expression,
    binary_expression,
    ternary_expression,
    subscript_expression,
    member_expression,
    call_expression,
}

static PREC_CLIMBER: PrecClimber<Rule> = PrecClimber::new(vec![
    Operator::new(Rule::primary_expression, Assoc::Left),
    Operator::new(Rule::call_expression, Assoc::Left),
    Operator::new(Rule::member_expression, Assoc::Left)
        | Operator::new(Rule::subscript_expression, Assoc::Left),
    Operator::new(Rule::ternary_expression, Assoc::Right),
    Operator::new(Rule::binary_expression, Assoc::Left),
]);

fn parse() {
    // TODO

    let pairs = Surf::parse(Rule::program, "function(){}").unwrap_or_else(|e| panic!("{}", e));

    for pair in pairs {
        println!("Rule: {:?}", pair.as_rule());
        println!("Span: {:?}", pair.as_span());
        println!("Text: {}", pair.as_str());
    }
}

#[cfg(test)]
mod tests {
    use crate::surf::parsing::parse;

    #[test]
    fn it_works() {
        parse()
    }
}
