use crate::codegen::Codegen;
use crate::Error;

#[derive(Default)]
pub struct Noop {}

impl Codegen for Noop {
    fn file(&self, _: &mut String) -> Result<(), Error> {
        Ok(())
    }
}
