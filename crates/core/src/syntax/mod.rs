use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use std::vec::IntoIter;

use chumsky::extra::ParserExtra;
use chumsky::input::{Input, MapExtra};
use strum::{Display, EnumString};
use ustr::Ustr;

use crate::syntax::parse::{Sym, Token};
use crate::{Span, Spanned};

pub(crate) mod parse;
pub(crate) mod resolve;

#[derive(Clone, Eq)]
pub(crate) struct Name(Rc<Ustr>);

impl Name {
    pub(crate) fn bound(n: Ustr) -> Self {
        Self(Rc::new(n))
    }

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
    Type,
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

impl BuiltinType {
    pub(crate) fn is_number(&self) -> bool {
        matches!(
            self,
            Self::I8
                | Self::I16
                | Self::I32
                | Self::I64
                | Self::U8
                | Self::U16
                | Self::U32
                | Self::U64
                | Self::F32
                | Self::F64
        )
    }
}

#[derive(Debug, Clone)]
pub(crate) enum Expr {
    // Naming.
    Name(Name),

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

#[derive(Debug)]
pub(crate) enum Stmt {
    // Blocks.
    Func {
        short: bool,
        sig: Sig,
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
    Update {
        name: Spanned<Name>,
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

#[derive(Debug)]
pub(crate) struct Sig {
    pub(crate) doc: Box<[String]>,
    pub(crate) name: Name,
    pub(crate) params: Box<[Spanned<Param>]>,
    pub(crate) ret: Option<Spanned<Expr>>,
}

#[derive(Debug)]
pub(crate) struct Param {
    pub(crate) name: Name,
    pub(crate) typ: Option<Spanned<Expr>>,
}

#[derive(Debug)]
pub(crate) struct Branch {
    pub(crate) span: Span,
    pub(crate) cond: Spanned<Expr>,
    pub(crate) body: Box<[Spanned<Stmt>]>,
}

pub(crate) struct Shadowed<K: Eq + Hash, V>(Vec<(K, Option<V>)>);

impl<K: Eq + Hash, V> Default for Shadowed<K, V> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<K: Eq + Hash, V> Shadowed<K, V> {
    pub(crate) fn push(&mut self, k: K, v: Option<V>) {
        self.0.push((k, v));
    }

    pub(crate) fn into_iter(self) -> IntoIter<(K, Option<V>)> {
        self.0.into_iter()
    }

    pub(crate) fn clear(self, locals: &mut HashMap<K, V>) {
        self.into_iter().for_each(|(raw, name)| {
            match name {
                None => locals.remove(&raw),
                Some(old) => locals.insert(raw, old),
            };
        })
    }
}
