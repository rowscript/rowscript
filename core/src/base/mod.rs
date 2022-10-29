use std::fmt::{format, Debug, Display, Formatter, Write};
use std::hash::{Hash, Hasher};

use uuid::Uuid;

pub struct LocalVar {
    id: Uuid,
    name: String,
}

impl Display for LocalVar {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name.as_str())
    }
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

pub struct Param<T: Display> {
    var: LocalVar,
    typ: T,
}

impl<T: Display> Display for Param<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(format!("({}: {})", self.var, self.typ).as_str())
    }
}
