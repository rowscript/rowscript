use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use chumsky::extra::ParserExtra;
use chumsky::input::{Input, MapExtra};
use ustr::Ustr;

use crate::semantics::BuiltinType;
use crate::semantics::builtin::Builtin;
use crate::syntax::parse::{Sym, Token};
use crate::{Span, Spanned};

pub(crate) mod parse;
pub(crate) mod resolve;

#[derive(Clone, Eq)]
pub struct Id(Rc<Ustr>);

impl Id {
    pub(crate) fn bound(n: Ustr) -> Self {
        Self(Rc::new(n))
    }

    #[allow(dead_code)]
    pub(crate) fn unbound() -> Self {
        Self::bound(Default::default())
    }

    pub(crate) fn raw(&self) -> Ustr {
        *self.0
    }

    fn id(&self) -> usize {
        Rc::as_ptr(&self.0) as _
    }
}

impl Display for Id {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.0)
    }
}

impl Debug for Id {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}@{}", self.0, self.id())
    }
}

impl PartialEq for Id {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}

impl Hash for Id {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}

#[derive(Debug, Clone)]
pub enum Ident {
    Id(Id),
    Idx(usize),
    Builtin(Builtin),
}

impl Ident {
    pub(crate) fn as_id(&self) -> &Id {
        let Self::Id(id) = self else { unreachable!() };
        id
    }

    pub(crate) fn as_id_mut(&mut self) -> &mut Id {
        let Self::Id(id) = self else { unreachable!() };
        id
    }

    pub(crate) fn as_idx(&self) -> usize {
        let Self::Idx(idx) = self else { unreachable!() };
        *idx
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    // Naming.
    Ident(Ident),

    // Types.
    BuiltinType(BuiltinType),

    // Constants.
    Unit,
    Number(f64),
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

#[derive(Debug, Clone)]
pub(crate) enum Stmt {
    // Expressions.
    Expr(Expr),

    // Binding.
    Assign {
        name: Spanned<Ident>,
        typ: Option<Spanned<Expr>>,
        rhs: Spanned<Expr>,
    },
    Update {
        name: Spanned<Ident>,
        rhs: Spanned<Expr>,
    },

    // Control.
    Return(Option<Spanned<Expr>>),
    If {
        then: Branch,
        elif: Box<[Branch]>,
        els: Option<(Span, Box<[Spanned<Self>]>)>,
    },
    While(Branch),
}

#[derive(Debug, Clone)]
pub(crate) struct Branch {
    pub(crate) span: Span,
    pub(crate) cond: Spanned<Expr>,
    pub(crate) body: Box<[Spanned<Stmt>]>,
}

#[derive(Debug)]
pub(crate) struct Sig {
    #[allow(dead_code)]
    pub(crate) doc: Box<[String]>,
    pub(crate) name: Id,
    pub(crate) params: Box<[Spanned<Param>]>,
    pub(crate) ret: Option<Spanned<Expr>>,
}

#[derive(Debug)]
pub(crate) struct Param {
    pub(crate) name: Ident,
    pub(crate) typ: Option<Spanned<Expr>>,
}

#[derive(Debug)]
pub(crate) enum Def {
    Func {
        sig: Sig,
        body: Box<[Spanned<Stmt>]>,
    },
}

#[derive(Default, Debug)]
pub(crate) struct File {
    pub(crate) defs: Box<[Spanned<Def>]>,
    pub(crate) main: Option<Id>,
}
