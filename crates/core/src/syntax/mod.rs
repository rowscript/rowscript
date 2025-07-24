use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use ustr::Ustr;

use crate::Spanned;
use crate::semantics::{BuiltinType, Op};

pub(crate) mod parser;
pub(crate) mod resolver;

#[derive(Clone, Eq)]
pub(crate) struct Name(Rc<Ustr>);

impl Name {
    pub(crate) fn bound(n: Ustr) -> Self {
        Self(Rc::new(n))
    }

    pub(crate) fn unbound() -> Self {
        Self::bound("".into())
    }

    pub(crate) fn raw(&self) -> Ustr {
        *self.0
    }

    fn id(&self) -> usize {
        Rc::as_ptr(&self.0) as _
    }
}

impl Display for Name {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.0)
    }
}

impl Debug for Name {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}@{}", self.0, self.id())
    }
}

impl PartialEq for Name {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}

impl Hash for Name {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}

#[derive(Debug)]
pub(crate) enum Expr {
    // Naming.
    Name(Name),

    // Types.
    BuiltinType(BuiltinType),

    // Constants.
    Number(Ustr),
    String(Ustr),
    Boolean(bool),

    // Values.
    Call(Box<Spanned<Self>>, Box<[Spanned<Self>]>),
    BinaryOp(Box<Spanned<Self>>, Spanned<Op>, Box<Spanned<Self>>),
}

#[derive(Debug)]
pub(crate) enum Stmt {
    // Blocks.
    Func {
        doc: Box<[String]>,
        name: Name,
        params: Box<[Spanned<Param>]>,
        ret: Option<Spanned<Expr>>,
        body: Box<[Spanned<Self>]>,
    },

    // Expressions.
    Expr(Expr),

    // Binding.
    Assign {
        doc: Box<[String]>,
        name: Name,
        typ: Option<Spanned<Expr>>,
        rhs: Spanned<Expr>,
    },

    // Control.
    Return(Option<Spanned<Expr>>),
    If {
        then: Branch,
        elif: Box<[Branch]>,
        els: Option<Box<[Spanned<Self>]>>,
    },
}
#[derive(Debug)]
pub(crate) struct Param {
    name: Name,
    typ: Option<Spanned<Expr>>,
}

#[derive(Debug)]
pub(crate) struct Branch {
    cond: Spanned<Expr>,
    body: Box<[Spanned<Stmt>]>,
}
