use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use chumsky::prelude::SimpleSpan;
use ustr::Ustr;

use crate::semantics::BuiltinType;

pub(crate) mod parser;

type Span = SimpleSpan;

#[derive(Debug, Clone)]
pub(crate) struct Spanned<T> {
    pub(crate) span: Span,
    pub(crate) item: T,
}

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
    // Blocks.
    Func {
        doc: Option<String>,
        name: Name,
        params: Box<[Spanned<Param>]>,
        ret: Option<Box<Spanned<Self>>>,
        body: Box<[Spanned<Self>]>,
    },

    // Naming.
    Name(Name),

    // Binding.
    Assign(Name, Option<Box<Spanned<Self>>>, Box<Spanned<Self>>),

    // Types.
    BuiltinType(BuiltinType),

    // Constants.
    Number(Ustr),
    String(Ustr),
    Boolean(bool),

    // Values.
    Call(Box<Spanned<Self>>, Box<[Spanned<Self>]>),
    BinaryOp(Box<Spanned<Self>>, Spanned<Ustr>, Box<Spanned<Self>>),

    // Control.
    Return(Option<Box<Spanned<Self>>>),
    If {
        then: Box<Spanned<Branch>>,
        elif: Option<Box<[Spanned<Branch>]>>,
        els: Option<Box<Spanned<Branch>>>,
    },
}

#[derive(Debug)]
pub(crate) struct Param {
    name: Name,
    typ: Option<Expr>,
}

#[derive(Debug)]
pub(crate) struct Branch {
    cond: Expr,
    body: Box<[Expr]>,
}
