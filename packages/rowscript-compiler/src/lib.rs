use crate::surf::Surf;
mod surf;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum CompilerError {
    #[error(transparent)]
    SurfError(#[from] surf::SurfError),
}

pub fn build(src: String) -> Result<(), CompilerError> {
    Surf::new(src)
        .map(|s| s.to_presyntax())
        .map(|t| {
            dbg!(t);
        })
        .map_err(Into::into)
}
