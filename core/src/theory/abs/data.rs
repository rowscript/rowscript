use std::collections::HashMap;
use std::fmt::{Display, Formatter};

use crate::theory::abs::data::Term::{Lam, Pi};
use crate::theory::conc::data::ArgInfo;
use crate::theory::conc::load::ModuleID;
use crate::theory::{Param, ParamInfo, Syntax, Tele, Var};

pub type Spine = Vec<(ParamInfo, Term)>;

#[derive(Debug, Copy, Clone)]
pub enum Dir {
    Le,
    Ge,
}

impl Display for Dir {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Dir::Le => "<:",
            Dir::Ge => ":>",
        })
    }
}

pub type FieldMap = HashMap<String, Term>;
pub type CaseMap = HashMap<String, (Var, Term)>;

#[derive(Debug, Clone)]
pub enum MetaKind {
    UserMeta,
    InsertedMeta,
}

impl Display for MetaKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use MetaKind::*;
        f.write_str(match self {
            UserMeta => "?u",
            InsertedMeta => "?i",
        })
    }
}

#[derive(Debug, Clone)]
pub enum Term {
    Ref(Var),
    Qualified(ModuleID, Var),
    Extern(Var),
    MetaRef(MetaKind, Var, Spine),
    Undef(Var),

    Let(Param<Self>, Box<Self>, Box<Self>),

    Univ,

    Pi(Param<Self>, Box<Self>),
    Lam(Param<Self>, Box<Self>),
    App(Box<Self>, ArgInfo, Box<Self>),

    Sigma(Param<Self>, Box<Self>),
    Tuple(Box<Self>, Box<Self>),
    TupleLet(Param<Self>, Param<Self>, Box<Self>, Box<Self>),

    Unit,
    TT,
    UnitLet(Box<Self>, Box<Self>),

    Boolean,
    False,
    True,
    If(Box<Self>, Box<Self>, Box<Self>),

    String,
    Str(String),

    Number,
    Num(f64),
    NumAdd(Box<Self>, Box<Self>),
    NumSub(Box<Self>, Box<Self>),

    BigInt,
    Big(String),

    Row,
    Fields(FieldMap),
    Combine(Box<Self>, Box<Self>),

    RowOrd(Box<Self>, Dir, Box<Self>),
    RowSat,

    RowEq(Box<Self>, Box<Self>),
    RowRefl,

    Object(Box<Self>),
    Obj(Box<Self>),
    Concat(Box<Self>, Box<Self>),
    Access(Box<Self>, String),
    Downcast(Box<Self>, Box<Self>),
    Down(Box<Self>, Box<Self>),

    Enum(Box<Self>),
    Variant(Box<Self>),
    Upcast(Box<Self>),
    Up(Box<Self>, Box<Self>, Box<Self>),
    Switch(Box<Self>, CaseMap),
    Unionify(Box<Self>),

    Vptr(Var, Vec<Self>),
    Vp(String, Vec<Self>),
    Lookup(Box<Self>),

    Find(Box<Self>, Var, Var),
    ImplementsOf(Box<Self>, Var),
    ImplementsSat,

    Reflected(Box<Self>),
}

impl Term {
    pub fn lam(tele: &Tele<Term>, tm: Term) -> Term {
        tele.iter().rfold(tm, |b, p| Lam(p.clone(), Box::new(b)))
    }

    pub fn pi(tele: &Tele<Term>, tm: Term) -> Term {
        tele.iter().rfold(tm, |b, p| Pi(p.clone(), Box::new(b)))
    }

    pub fn tele_to_spine(tele: &Tele<Term>) -> Spine {
        tele.iter()
            .map(|p| (p.info, Self::Ref(p.var.clone())))
            .collect()
    }
}

impl Syntax for Term {}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Term::*;
        f.write_str(
            match self {
                Ref(r) => r.to_string(),
                Extern(r) => r.to_string(),
                Qualified(m, r) => format!("{m}::{r}"),
                MetaRef(k, r, sp) => {
                    let mut s = vec![format!("{k}{r}")];
                    s.extend(
                        sp.iter()
                            .map(|(i, tm)| match i {
                                ParamInfo::Explicit => tm.to_string(),
                                ParamInfo::Implicit => format!("{{{tm}}}"),
                            })
                            .collect::<Vec<_>>(),
                    );
                    format!("({})", s.join(" "))
                }
                Undef(r) => r.to_string(),
                Let(p, a, b) => format!("let {p} = {a};\n\t{b}"),
                Univ => "type".to_string(),
                Pi(p, b) => format!("{p} -> {b}"),
                Lam(p, b) => format!("{p} => {b}"),
                App(f, _, x) => format!("({f} {x})"),
                Sigma(p, b) => format!("{p} * {b}"),
                Tuple(a, b) => format!("({a}, {b})"),
                TupleLet(p, q, a, b) => format!("let ({p}, {q}) = {a};\n\t{b}"),
                Unit => "unit".to_string(),
                TT => "()".to_string(),
                UnitLet(a, b) => format!("let _ = {a};\n\t{b}"),
                Boolean => "boolean".to_string(),
                False => "false".to_string(),
                True => "true".to_string(),
                If(p, t, e) => format!("if {p} {{ {t} }} else {{ {e} }}"),
                String => "string".to_string(),
                Str(v) => format!("\"{v}\""),
                Number => "number".to_string(),
                Num(v) => v.to_string(),
                NumAdd(a, b) => format!("{a} + {b}"),
                NumSub(a, b) => format!("{a} - {b}"),
                BigInt => "bigint".to_string(),
                Big(v) => v.clone(),
                Row => "row".to_string(),
                Fields(fields) => format!(
                    "({})",
                    fields
                        .iter()
                        .map(|(f, typ)| format!("{f}: {typ}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                Combine(a, b) => format!("{a} + {b}"),
                RowOrd(a, d, b) => format!("{a} {d} {b}"),
                RowSat => "sat".to_string(),
                RowEq(a, b) => format!("{a} = {b}"),
                RowRefl => "refl".to_string(),
                Object(r) => format!("{{{r}}}"),
                Obj(r) => format!("{{{r}}}"),
                Concat(a, b) => format!("{a}...{b}"),
                Access(a, n) => format!("{a}.{n}"),
                Downcast(a, _) => format!("downcast<{a}>"),
                Down(a, _) => format!("{{...{a}}}"),
                Enum(r) => format!("[{r}]"),
                Variant(r) => format!("[{r}]"),
                Upcast(a) => format!("upcast<{a}>"),
                Up(a, _, _) => format!("[...{a}]"),
                Switch(a, cs) => {
                    format!(
                        "switch ({a}) {{\n{}\n}}",
                        cs.iter()
                            .map(|(n, (v, e))| format!("\tcase {n}({v}): {e}"))
                            .collect::<Vec<_>>()
                            .join("\n")
                    )
                }
                Unionify(a) => format!("unionify({a})"),
                Vptr(r, ts) => format!(
                    "vptr@{r}<{}>",
                    ts.iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                Vp(r, ts) => format!(
                    "vptr@{r}({})",
                    ts.iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                Lookup(a) => format!("lookup({a})",),
                Find(ty, i, f) => format!("{i}.{f}<{ty}>"),
                ImplementsOf(t, i) => format!("{t} implementsOf {i}"),
                ImplementsSat => "implementsSat".to_string(),
                Reflected(a) => format!("Reflected<{a}>"),
            }
            .as_str(),
        )
    }
}
