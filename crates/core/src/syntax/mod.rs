use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use chumsky::extra::ParserExtra;
use chumsky::input::{Input, MapExtra};
use strum::{Display, EnumString};
use ustr::Ustr;

use crate::syntax::parser::{Sym, Token};
use crate::{Span, Spanned};

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

#[derive(Debug, Eq, PartialEq, Copy, Clone, EnumString, Display)]
#[strum(serialize_all = "lowercase")]
pub(crate) enum BuiltinType {
    Unit,
    Bool,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Str,
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
    BinaryOp(Box<Spanned<Self>>, Sym, Box<Spanned<Self>>),
}

impl Expr {
    fn binary<'src, 'b, I, E>(
        lhs: Spanned<Self>,
        op: Token,
        rhs: Spanned<Self>,
        e: &mut MapExtra<'src, 'b, I, E>,
    ) -> Spanned<Self>
    where
        I: Input<'src, Span = Span>,
        E: ParserExtra<'src, I>,
    {
        let Token::Sym(sym) = op else {
            unreachable!();
        };
        Spanned {
            span: e.span(),
            item: Self::BinaryOp(Box::new(lhs), sym, Box::new(rhs)),
        }
    }
}

#[derive(Debug)]
pub(crate) enum Stmt {
    // Blocks.
    Func(Sig, Box<[Spanned<Self>]>),
    Fn(Sig, Spanned<Expr>),

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
pub(crate) struct Sig {
    doc: Box<[String]>,
    name: Name,
    params: Box<[Spanned<Param>]>,
    ret: Option<Spanned<Expr>>,
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
