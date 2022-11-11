use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "src/surf/rows.pest"]
pub struct Surf;

#[cfg(test)]
mod tests {
    use crate::surf::Surf;

    #[test]
    fn test_surf() {}
}
