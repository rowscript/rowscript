use rowscript_core::presyntax::Term;

mod parsing;

pub fn build(src: String) -> Result<(), String> {
    parsing::parse(src).map(Term::new).map(|t| {
        dbg!(t);
    })
}
