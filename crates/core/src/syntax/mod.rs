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

    pub(crate) fn this() -> Self {
        Self::bound("this".into())
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
    RefType(Box<Spanned<Self>>),

    // Constants.
    Unit,
    Integer(Integer),
    Float(Float),
    String(String),
    Boolean(bool),

    // Values.
    Call(Box<Spanned<Self>>, Vec<Spanned<Self>>),
    BinaryOp(Box<Spanned<Self>>, Sym, Option<Type>, Box<Spanned<Self>>),
    UnaryOp(Box<Spanned<Self>>, Sym, Option<Type>),
    New(Box<Spanned<Self>>),
    Object(Box<Spanned<Self>>, Object),
    Access(Box<Spanned<Self>>, Access),
    Method {
        callee: Box<Spanned<Self>>,
        target: Option<Id>,
        method: Spanned<Ident>,
        args: Vec<Spanned<Self>>,
    },

    // Resolving-specific constructs.
    ThisType(Box<Self>),

    // Typechecking-specific constructs, especially those are "readback" (a.k.a. "reified").
    StructType(Id),

    // VM-specific constructs.
    Ref(Rc<Self>),
    Struct(Vec<Self>),
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
    Unordered(Vec<(Spanned<Ustr>, Spanned<Expr>)>),
    Ordered(Vec<Expr>),
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
        elif: Vec<Branch>,
        els: Option<(Span, Vec<Spanned<Self>>)>,
    },
    While(Branch),
}

#[derive(Debug, Clone)]
pub(crate) struct Branch {
    pub(crate) span: Span,
    pub(crate) cond: Spanned<Expr>,
    pub(crate) body: Vec<Spanned<Stmt>>,
}

#[derive(Default, Debug)]
pub(crate) struct File {
    pub(crate) decls: Vec<Spanned<Decl>>,
    pub(crate) main: Option<Id>,
}

#[derive(Debug)]
pub(crate) struct Decl {
    #[allow(dead_code)]
    pub(crate) doc: Vec<String>,
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
        members: Vec<Spanned<Member>>,
    },
    Extends {
        target: Ident,
        methods: Vec<Spanned<MethodSig>>,
    },
}

#[derive(Debug)]
pub(crate) struct FuncSig {
    pub(crate) name: Id,
    pub(crate) params: Vec<Spanned<Param>>,
    pub(crate) ret: Option<Spanned<Expr>>,
}

#[derive(Debug)]
pub(crate) struct MethodSig {
    #[allow(dead_code)]
    pub(crate) doc: Vec<String>,
    pub(crate) sig: FuncSig,
}

#[derive(Debug)]
pub(crate) enum Def {
    Func { body: Vec<Spanned<Stmt>> },
    Static { rhs: Spanned<Expr> },
    Struct,
    Extends { bodies: Vec<Vec<Spanned<Stmt>>> },
}

#[derive(Debug)]
pub(crate) struct Param {
    pub(crate) name: Ident,
    pub(crate) typ: Spanned<Expr>,
}

#[derive(Debug)]
pub(crate) struct Member {
    #[allow(dead_code)]
    pub(crate) name: Ustr,
    pub(crate) typ: Spanned<Expr>,
}
