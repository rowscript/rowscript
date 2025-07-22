use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use chumsky::prelude::SimpleSpan;
use ustr::Ustr;

use crate::semantics::BuiltinType;

pub(crate) mod parser;

type Span = SimpleSpan;

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
enum Expr {
    // Blocks.
    Func {
        span: Span,
        doc: Option<String>,
        name: Name,
        params: Box<[Param]>,
        ret: Option<Box<Self>>,
        body: Box<[Self]>,
    },

    // Naming.
    Name(Span, Name),

    // Types.
    BuiltinType(Span, BuiltinType),

    // Constants.
    Number(Span, Ustr),
    String(Span, Ustr),

    // Values.
    Call {
        span: Span,
        func: Box<Self>,
        args: Box<[Self]>,
    },
    BinaryOp {
        span: Span,
        op: Ustr,
        lhs: Box<Self>,
        rhs: Box<Self>,
    },

    // Control.
    Return(Span, Option<Box<Self>>),
    If {
        span: Span,
        then: Box<Branch>,
        elif: Option<Box<[Branch]>>,
        els: Option<Box<Branch>>,
    },
}

#[derive(Debug)]
struct Param {
    span: Span,
    name: Name,
    typ: Option<Expr>,
}

#[derive(Debug)]
struct Branch {
    span: Span,
    cond: Expr,
    body: Box<[Expr]>,
}
