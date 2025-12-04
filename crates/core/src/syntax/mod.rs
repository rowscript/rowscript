pub(crate) mod parse;
pub(crate) mod resolve;

use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use chumsky::extra::ParserExtra;
use chumsky::input::{Input, MapExtra};
use ustr::Ustr;

use crate::semantics::builtin::Builtin;
use crate::semantics::{BuiltinType, Float, Integer, Type};
use crate::syntax::parse::{Sym, Token};
use crate::{Span, Spanned};

#[derive(Clone, Eq)]
pub struct Id(Rc<Ustr>);

impl Id {
    pub(crate) fn bound(n: Ustr) -> Self {
        Self(Rc::new(n))
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
    RefType(Box<Spanned<Self>>),

    // Constants.
    Unit,
    Integer(Integer),
    Float(Float),
    String(String),
    Boolean(bool),

    // Values.
    Call(Box<Spanned<Self>>, Box<[Spanned<Self>]>),
    BinaryOp(Box<Spanned<Self>>, Sym, Option<Type>, Box<Spanned<Self>>),
    UnaryOp(Box<Spanned<Self>>, Sym, Option<Type>),
    New(Box<Spanned<Self>>),
    Object(Box<Spanned<Self>>, Object),
    Access(Box<Spanned<Self>>, Access),
    Method(Box<Spanned<Self>>, Spanned<Ustr>, Box<[Spanned<Self>]>),

    // Typechecking-specific constructs, especially those are "readback" (a.k.a. "reified").
    StructType(Id),

    // VM-specific constructs.
    Ref(Rc<Self>),
    Struct(Box<[Self]>),
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
        let Token::Sym(sym) = op else { unreachable!() };
        Spanned::from_map_extra(Self::BinaryOp(Box::new(lhs), sym, None, Box::new(rhs)), e)
    }

    fn unary<'src, 'b, I, E>(
        op: Token,
        x: Spanned<Self>,
        e: &mut MapExtra<'src, 'b, I, E>,
    ) -> Spanned<Self>
    where
        I: Input<'src, Span = Span>,
        E: ParserExtra<'src, I>,
    {
        let Token::Sym(sym) = op else { unreachable!() };
        Spanned::from_map_extra(Self::UnaryOp(Box::new(x), sym, None), e)
    }
}

#[derive(Debug, Clone)]
pub enum Object {
    Unordered(Box<[(Spanned<Ustr>, Spanned<Expr>)]>),
    Ordered(Box<[Expr]>),
}

#[derive(Debug, Clone)]
pub enum Access {
    Named(Spanned<Ustr>),
    Indexed(usize),
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

#[derive(Default, Debug)]
pub(crate) struct File {
    pub(crate) decls: Box<[Spanned<Decl>]>,
    pub(crate) main: Option<Id>,
}

#[derive(Debug)]
pub(crate) struct Decl {
    #[allow(dead_code)]
    pub(crate) doc: Box<[String]>,
    pub(crate) sig: Sig,
    pub(crate) def: Def,
}

#[derive(Debug)]
pub(crate) enum Sig {
    Func(FuncSig),
    Static {
        name: Id,
        typ: Spanned<Expr>,
    },
    Struct {
        name: Id,
        members: Box<[Spanned<Member>]>,
    },
    Extends {
        target: Ident,
        methods: Box<[Spanned<MethodSig>]>,
    },
}

#[derive(Debug)]
pub(crate) struct FuncSig {
    pub(crate) name: Id,
    pub(crate) params: Box<[Spanned<Param>]>,
    pub(crate) ret: Option<Spanned<Expr>>,
}

#[derive(Debug)]
pub(crate) struct MethodSig {
    #[allow(dead_code)]
    pub(crate) doc: Box<[String]>,
    sig: FuncSig,
}

#[derive(Debug)]
pub(crate) enum Def {
    Func { body: Box<[Spanned<Stmt>]> },
    Static { rhs: Spanned<Expr> },
    Struct,
    Extends { bodies: Box<[Box<[Spanned<Stmt>]>]> },
}

#[derive(Debug)]
pub(crate) struct Param {
    pub(crate) name: Ident,
    pub(crate) typ: Option<Spanned<Expr>>,
}

#[derive(Debug)]
pub(crate) struct Member {
    #[allow(dead_code)]
    pub(crate) name: Ustr,
    pub(crate) typ: Spanned<Expr>,
}
