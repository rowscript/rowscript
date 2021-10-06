use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "surf/grammar.pest"]
struct Surf;

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
