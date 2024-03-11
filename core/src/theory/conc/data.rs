use std::fmt::{Display, Formatter};

use crate::theory::abs::data::Dir;
use crate::theory::conc::load::ModuleID;
use crate::theory::{Loc, Param, Syntax, Tele, Var};

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ArgInfo {
    UnnamedExplicit,
    UnnamedImplicit,
    NamedImplicit(Var),
}

#[derive(Debug, Clone)]
pub enum Expr {
    Unresolved(Loc, Option<ModuleID>, Var),
    Resolved(Loc, Var),
    Imported(Loc, Var),
    Qualified(Loc, ModuleID, Var),

    Hole(Loc),
    InsertedHole(Loc),

    Local(Loc, Var, Option<Box<Self>>, Box<Self>, Box<Self>),
    WorSet(Loc, Var, Option<Box<Self>>, Box<Self>),
    WorUpdate(Loc, Var, Box<Self>),
    While(Loc, Box<Self>, Box<Self>, Box<Self>),
    Guard(Loc, Box<Self>, Box<Self>, Box<Self>),
    Return(Loc, Box<Self>),
    Continue(Loc),
    Break(Loc),

    Univ(Loc),

    Pi(Loc, Param<Self>, Box<Self>),
    TupledLam(Loc, Vec<Self>, Box<Self>),
    AnnoLam(Loc, Param<Self>, Box<Self>),
    Lam(Loc, Var, Box<Self>),
    App(Loc, Box<Self>, ArgInfo, Box<Self>),
    RevApp(Loc, Box<Self>, Box<Self>),

    Sigma(Loc, Param<Self>, Box<Self>),
    Tuple(Loc, Box<Self>, Box<Self>),
    TupleLocal(Loc, Var, Var, Box<Self>, Box<Self>),
    AnnoTupleLocal(Loc, Param<Self>, Param<Self>, Box<Self>, Box<Self>),

    Unit(Loc),
    TT(Loc),
    UnitLocal(Loc, Box<Self>, Box<Self>),

    Boolean(Loc),
    False(Loc),
    True(Loc),
    If(Loc, Box<Self>, Box<Self>, Box<Self>),

    String(Loc),
    Str(Loc, String),

    Number(Loc),
    Num(Loc, String),

    BigInt(Loc),
    Big(Loc, String),

    Arr(Loc, Vec<Self>),

    Row(Loc),
    Fields(Loc, Vec<(String, Self)>),
    Combine(Loc, Box<Self>, Box<Self>),

    RowOrd(Loc, Box<Self>, Dir, Box<Self>),
    RowEq(Loc, Box<Self>, Box<Self>),

    Object(Loc, Box<Self>),
    Obj(Loc, Box<Self>),
    Concat(Loc, Box<Self>, Box<Self>),
    Access(Loc, String),
    Downcast(Loc, Box<Self>),

    Enum(Loc, Box<Self>),
    Variant(Loc, String, Box<Self>),
    Upcast(Loc, Box<Self>),
    Switch(Loc, Box<Self>, Vec<(String, Var, Self)>),

    Constraint(Loc, Box<Self>),
    Find(Loc, Var, Var),
    ImplementsOf(Loc, Box<Self>),
}

impl Expr {
    pub fn pi(tele: &Tele<Expr>, e: Expr) -> Expr {
        use Expr::*;
        tele.iter()
            .rfold(e, |b, p| Pi(b.loc(), p.clone(), Box::new(b)))
    }

    pub fn resolved(self) -> Var {
        use Expr::*;
        match self {
            Resolved(_, r) => r,
            _ => unreachable!(),
        }
    }

    pub fn loc(&self) -> Loc {
        use Expr::*;
        *match self {
            Unresolved(loc, ..) => loc,
            Resolved(loc, ..) => loc,
            Imported(loc, ..) => loc,
            Qualified(loc, ..) => loc,
            Hole(loc) => loc,
            InsertedHole(loc) => loc,
            Local(loc, ..) => loc,
            WorSet(loc, ..) => loc,
            While(loc, ..) => loc,
            Guard(loc, ..) => loc,
            Return(loc, ..) => loc,
            Continue(loc) => loc,
            Break(loc) => loc,
            WorUpdate(loc, ..) => loc,
            Univ(loc) => loc,
            Pi(loc, ..) => loc,
            TupledLam(loc, ..) => loc,
            AnnoLam(loc, ..) => loc,
            Lam(loc, ..) => loc,
            App(loc, ..) => loc,
            RevApp(loc, ..) => loc,
            Sigma(loc, ..) => loc,
            Tuple(loc, ..) => loc,
            TupleLocal(loc, ..) => loc,
            AnnoTupleLocal(loc, ..) => loc,
            Unit(loc) => loc,
            TT(loc) => loc,
            UnitLocal(loc, ..) => loc,
            Boolean(loc) => loc,
            False(loc) => loc,
            True(loc) => loc,
            If(loc, ..) => loc,
            String(loc) => loc,
            Str(loc, ..) => loc,
            Number(loc) => loc,
            Num(loc, ..) => loc,
            BigInt(loc) => loc,
            Big(loc, ..) => loc,
            Arr(loc, ..) => loc,
            Row(loc) => loc,
            Fields(loc, ..) => loc,
            Combine(loc, ..) => loc,
            RowOrd(loc, ..) => loc,
            RowEq(loc, ..) => loc,
            Object(loc, ..) => loc,
            Obj(loc, ..) => loc,
            Concat(loc, ..) => loc,
            Access(loc, ..) => loc,
            Downcast(loc, ..) => loc,
            Enum(loc, ..) => loc,
            Variant(loc, ..) => loc,
            Upcast(loc, ..) => loc,
            Switch(loc, ..) => loc,
            Constraint(loc, ..) => loc,
            Find(loc, ..) => loc,
            ImplementsOf(loc, ..) => loc,
        }
    }

    pub fn wrap_tuple_locals(loc: Loc, x: &Var, vars: Vec<Self>, b: Self) -> Self {
        use Expr::*;

        let mut untupled_vars = Vec::default();
        for x in vars.iter().rev() {
            untupled_vars.push(match x {
                Unresolved(l, _, r) => Unresolved(*l, None, r.untupled_rhs()),
                _ => unreachable!(),
            });
        }
        untupled_vars.push(Unresolved(loc, None, x.clone()));

        let mut wrapped = b;
        for (i, v) in vars.into_iter().rev().enumerate() {
            let (loc, lhs, rhs) = match (v, untupled_vars.get(i).unwrap()) {
                (Unresolved(loc, _, lhs), Unresolved(_, _, rhs)) => (loc, lhs, rhs),
                _ => unreachable!(),
            };
            let tm = untupled_vars.get(i + 1).unwrap();
            wrapped = TupleLocal(
                loc,
                lhs,
                rhs.clone(),
                Box::new(tm.clone()),
                Box::new(wrapped),
            );
        }

        wrapped
    }

    pub fn holed_app(f: Self) -> Self {
        use ArgInfo::*;
        use Expr::*;
        let loc = f.loc();
        App(
            loc,
            Box::new(f),
            UnnamedImplicit,
            Box::new(InsertedHole(loc)),
        )
    }
}

impl Syntax for Expr {}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use ArgInfo::*;
        use Expr::*;

        f.write_str(
            match self {
                Unresolved(_, m, r) => match m {
                    Some(m) => format!("{m}::{r}"),
                    None => r.to_string(),
                },
                Resolved(_, r) => r.to_string(),
                Imported(_, r) => r.to_string(),
                Qualified(_, m, r) => format!("{m}::{r}"),
                Hole(_) => "?".to_string(),
                InsertedHole(_) => "?i".to_string(),
                Local(_, v, typ, a, b) => {
                    if let Some(ty) = typ {
                        format!("const {v}: {ty} = {a};\n\t{b}")
                    } else {
                        format!("const {v} = {a};\n\t{b}")
                    }
                }
                WorSet(_, v, typ, a) => {
                    if let Some(ty) = typ {
                        format!("worldSet({v}, {ty}, {a})")
                    } else {
                        format!("worldSet({v}, {a})")
                    }
                }
                WorUpdate(_, a, v) => format!("worldUpdate({a}, {v})"),
                While(_, p, b, r) => format!("while ({p}) {{\n\t{b}\n}}\n{r}"),
                Guard(_, p, b, r) => format!("if ({p}) {{\n\t{b}\n}}\n{r}"),
                Return(_, a) => format!("return {a}"),
                Continue(_) => "continue".to_string(),
                Break(_) => "break".to_string(),
                Univ(_) => "type".to_string(),
                Pi(_, p, b) => format!("{p} -> {b}"),
                TupledLam(_, vs, b) => format!(
                    "({}) => {b}",
                    vs.iter()
                        .map(|v| v.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                AnnoLam(_, p, b) => format!("{p} => {b}"),
                Lam(_, v, b) => format!("{v} => {b}"),
                App(_, f, i, x) => match i {
                    UnnamedExplicit => format!("({f} {x})"),
                    UnnamedImplicit => format!("({f} {{{x}}})"),
                    NamedImplicit(r) => format!("({f} {{{r} = {x}}})"),
                },
                RevApp(_, f, x) => format!("({x}.{f})"),
                Sigma(_, p, b) => format!("{p} * {b}"),
                Tuple(_, a, b) => format!("({a}, {b})"),
                TupleLocal(_, x, y, a, b) => format!("const ({x}, {y}) = {a};\n\t{b}"),
                AnnoTupleLocal(_, p, q, a, b) => format!("const {p}, {q} = {a};\n\t{b}"),
                Unit(_) => "unit".to_string(),
                TT(_) => "()".to_string(),
                UnitLocal(_, a, b) => format!("{a};\n\t{b}"),
                Boolean(_) => "boolean".to_string(),
                False(_) => "false".to_string(),
                True(_) => "true".to_string(),
                If(_, p, t, e) => format!("if {p} {{ {t} }} else {{ {e} }}"),
                String(_) => "string".to_string(),
                Str(_, v) => format!("\"{v}\""),
                Number(_) => "number".to_string(),
                Num(_, v) => v.clone(),
                BigInt(_) => "bigint".to_string(),
                Big(_, v) => v.clone(),
                Arr(_, xs) => format!(
                    "[{}]",
                    xs.iter()
                        .map(|x| x.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                Row(_) => "row".to_string(),
                Fields(_, fields) => format!(
                    "({})",
                    fields
                        .iter()
                        .map(|(n, t)| format!("{n}: {t}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                Combine(_, a, b) => format!("{a} + {b}"),
                RowOrd(_, a, dir, b) => format!("{a} {dir} {b}"),
                RowEq(_, a, b) => format!("{a} = {b}"),
                Object(_, r) => format!("{{{r}}}"),
                Obj(_, r) => format!("{{{r}}}"),
                Concat(_, a, b) => format!("{a}...{b}"),
                Access(_, n) => format!(".{n}"),
                Downcast(_, a) => format!("{{...{a}}}"),
                Enum(_, r) => format!("[{r}]"),
                Variant(_, n, a) => format!("{n}({a})"),
                Upcast(_, a) => format!("[...{a}]"),
                Switch(_, a, cs) => format!(
                    "switch ({a}) {{\n{}\n}}",
                    cs.iter()
                        .map(|(n, v, e)| format!("\tcase {n}({v}): {e}"))
                        .collect::<Vec<_>>()
                        .join("\n")
                ),
                Constraint(_, r) => r.to_string(),
                Find(_, i, f) => format!("{i}.{f}"),
                ImplementsOf(_, a) => a.to_string(),
            }
            .as_str(),
        )
    }
}
