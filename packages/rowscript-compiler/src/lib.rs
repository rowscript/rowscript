use crate::surf::Surf;

mod parsing;
mod surf;

pub fn build(src: String) -> Result<(), String> {
    parsing::parse(src).map(|s| s.to_presyntax()).map(|t| {
        dbg!(t);
    })
}
