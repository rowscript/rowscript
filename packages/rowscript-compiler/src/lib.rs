mod parsing;

pub fn build(src: String) -> Result<(), String> {
    parsing::parse(src)
}
