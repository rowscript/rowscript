use std::fmt::Debug;
use std::hash::{Hash, Hasher};

use uuid::Uuid;

#[derive(Debug)]
pub struct LocalVar {
    id: Uuid,
    name: String,
}

impl LocalVar {
    pub fn new(name: &str) -> Self {
        LocalVar {
            id: Uuid::new_v4(),
            name: name.to_string(),
        }
    }

    pub fn unbound() -> Self {
        Self::new("_")
    }
}

impl Hash for LocalVar {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state)
    }
}

#[derive(Debug)]
pub struct Param<T> {
    var: LocalVar,
    typ: Box<T>,
}
