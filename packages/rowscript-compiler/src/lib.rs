use crate::surf::Surf;
mod surf;

pub fn build(src: String) -> Result<(), String> {
    Surf::new(src).map(|s| s.to_presyntax()).map(|t| {
        dbg!(t);
    })
}
