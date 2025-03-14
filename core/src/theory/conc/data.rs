use crate::Src;
use crate::theory::abs::def::Def;
use crate::theory::conc::load::ModuleID;
use crate::theory::{Loc, Param, Syntax, Tele, Var};
use std::fmt::{Display, Formatter};

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

    Const(Loc, Var, Option<Box<Self>>, Box<Self>, Box<Self>),
    Let(Loc, Var, Option<Box<Self>>, Box<Self>, Box<Self>),
    Update(Loc, Var, Box<Self>, Box<Self>),
    While(Loc, Box<Self>, Box<Self>, Box<Self>),
    Fori(Loc, Box<Self>, Box<Self>),
    Guard(Loc, Box<Self>, Box<Self>, Option<Box<Self>>, Box<Self>),
    Return(Loc, Box<Self>),
    Continue(Loc),
    Break(Loc),

    Univ(Loc),

    Pi(Loc, Param<Self>, Box<Self>),
    TupledLam(Loc, Vec<Self>, Box<Self>),
    Lam(Loc, Var, Box<Self>),
    App(Loc, Box<Self>, ArgInfo, Box<Self>),
    RevApp(Loc, Box<Self>, Vec<Self>, Box<Self>),

    Sigma(Loc, Param<Self>, Box<Self>),
    Tuple(Loc, Box<Self>, Box<Self>),
    TupleBind(Loc, Var, Var, Box<Self>, Box<Self>),

    Unit(Loc),
    TT(Loc),
    UnitBind(Loc, Box<Self>, Box<Self>),

    Boolean(Loc),
    False(Loc),
    True(Loc),
    If(Loc, Box<Self>, Box<Self>, Box<Self>),

    String(Loc),
    Str(Loc, Src),

    Number(Loc),
    Num(Loc, Src),

    BigInt(Loc),
    Big(Loc, Src),

    Arr(Loc, Vec<Self>),

    Kv(Loc, Vec<(Self, Self)>),

    Row(Loc),
    Rowkey(Loc),
    At(Loc, Box<Self>, Box<Self>),
    Associate(Loc, Box<Self>, Src),
    Fields(Loc, Vec<(Src, Self)>),
    Combine(Loc, Box<Self>, Box<Self>),

    RowOrd(Loc, Box<Self>, Box<Self>),
    RowEq(Loc, Box<Self>, Box<Self>),

    Object(Loc, Box<Self>),
    Obj(Loc, Box<Self>),
    Concat(Loc, Box<Self>, Box<Self>),
    Cat(Loc, Box<Self>, Box<Self>),
    Access(Loc, Src),
    Downcast(Loc, Box<Self>),

    Enum(Loc, Box<Self>),
    Variant(Loc, Src, Box<Self>),
    Upcast(Loc, Box<Self>),
    UpcastTo(Loc, Box<Self>, Box<Self>),
    Switch(
        Loc,
        Box<Self>,
        Vec<(Src, Var, Self)>,
        Option<(Var, Box<Self>)>,
    ),

    Unionify(Loc, Box<Self>),
    Union(Loc, Box<Self>, Box<Self>),

    Instanceof(Loc, Box<Self>),

    Varargs(Loc, Box<Self>),
    AnonVarargs(Loc, Box<Self>),
    Spread(Loc, Box<Self>),
    AnonSpread(Loc),

    Typeof(Loc, Box<Self>),
    Keyof(Loc, Box<Self>),

    Pure(Loc),
    Effect(Loc, Vec<Self>),
    EmitAsync(Loc, Box<Self>),
    TryCatch(Loc, Box<Self>, Vec<Catch>),
}

impl Expr {
    pub fn pi(tele: &Tele<Expr>, e: Expr) -> Expr {
        use Expr::*;
        tele.iter()
            .rfold(e, |b, p| Pi(b.loc(), p.clone(), Box::new(b)))
    }

    pub fn resolved(self) -> Var {
        match self {
            Expr::Resolved(_, r) => r,
            _ => unreachable!(),
        }
    }

    pub fn loc(&self) -> Loc {
        use Expr::*;
        *match self {
            Unresolved(loc, ..)
            | Resolved(loc, ..)
            | Imported(loc, ..)
            | Qualified(loc, ..)
            | Hole(loc)
            | InsertedHole(loc)
            | Const(loc, ..)
            | Let(loc, ..)
            | Update(loc, ..)
            | While(loc, ..)
            | Fori(loc, ..)
            | Guard(loc, ..)
            | Return(loc, ..)
            | Continue(loc)
            | Break(loc)
            | Univ(loc)
            | Pi(loc, ..)
            | TupledLam(loc, ..)
            | Lam(loc, ..)
            | App(loc, ..)
            | RevApp(loc, ..)
            | Sigma(loc, ..)
            | Tuple(loc, ..)
            | TupleBind(loc, ..)
            | Unit(loc)
            | TT(loc)
            | UnitBind(loc, ..)
            | Boolean(loc)
            | False(loc)
            | True(loc)
            | If(loc, ..)
            | String(loc)
            | Str(loc, ..)
            | Number(loc)
            | Num(loc, ..)
            | BigInt(loc)
            | Big(loc, ..)
            | Arr(loc, ..)
            | Kv(loc, ..)
            | Row(loc)
            | Rowkey(loc)
            | At(loc, ..)
            | Associate(loc, ..)
            | Fields(loc, ..)
            | Combine(loc, ..)
            | RowOrd(loc, ..)
            | RowEq(loc, ..)
            | Object(loc, ..)
            | Obj(loc, ..)
            | Concat(loc, ..)
            | Cat(loc, ..)
            | Access(loc, ..)
            | Downcast(loc, ..)
            | Enum(loc, ..)
            | Variant(loc, ..)
            | Upcast(loc, ..)
            | UpcastTo(loc, ..)
            | Switch(loc, ..)
            | Unionify(loc, ..)
            | Union(loc, ..)
            | Instanceof(loc, ..)
            | Varargs(loc, ..)
            | AnonVarargs(loc, ..)
            | Spread(loc, ..)
            | AnonSpread(loc)
            | Typeof(loc, ..)
            | Keyof(loc, ..)
            | Pure(loc)
            | Effect(loc, ..)
            | EmitAsync(loc, ..)
            | TryCatch(loc, ..) => loc,
        }
    }

    pub fn wrap_tuple_binds(loc: Loc, tupled: Var, vars: Vec<Self>, b: Self) -> Self {
        Self::wrap_expr_tuple_binds(Expr::Unresolved(loc, None, tupled), vars, b)
    }

    pub fn wrap_expr_tuple_binds(tupled: Self, vars: Vec<Self>, b: Self) -> Self {
        use Expr::*;

        let mut untupled_rhs = Vec::default();
        for (i, x) in vars.iter().rev().enumerate() {
            untupled_rhs.push(match x {
                Unresolved(l, _, r) => Unresolved(
                    *l,
                    None,
                    if i == 0 {
                        Var::untupled_ends()
                    } else {
                        r.untupled_rhs()
                    },
                ),
                _ => unreachable!(),
            });
        }
        untupled_rhs.push(tupled);

        let mut wrapped = b;
        for (i, v) in vars.into_iter().rev().enumerate() {
            let (loc, lhs, rhs) = match (v, untupled_rhs.get(i).unwrap()) {
                (Unresolved(loc, _, lhs), Unresolved(_, _, rhs)) => (loc, lhs, rhs),
                _ => unreachable!(),
            };
            let tm = untupled_rhs.get(i + 1).unwrap();
            wrapped = TupleBind(
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

    pub fn async_effect(loc: Loc) -> Self {
        use Expr::*;
        Effect(loc, vec![Unresolved(loc, None, Var::async_effect())])
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
                Const(_, v, typ, a, b) => {
                    if let Some(ty) = typ {
                        format!("const {v}: {ty} = {a};\n\t{b}")
                    } else {
                        format!("const {v} = {a};\n\t{b}")
                    }
                }
                Let(_, v, typ, a, b) => {
                    if let Some(ty) = typ {
                        format!("let {v}: {ty} = {a};\n\t{b}")
                    } else {
                        format!("let {v} = {a};\n\t{b}")
                    }
                }
                Update(_, a, v, b) => format!("{a} = {v};\n\t{b}"),
                While(_, p, b, r) => format!("while ({p}) {{\n\t{b}\n}}\n{r}"),
                Fori(_, b, r) => format!("for {{ {b} }}\n{r}"),
                Guard(_, p, b, e, r) => {
                    if let Some(e) = e {
                        format!("if ({p}) {{\n\t{b}\n}} else {{\n\t{e}}}\n{r}")
                    } else {
                        format!("if ({p}) {{\n\t{b}\n}}\n{r}")
                    }
                }
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
                Lam(_, v, b) => format!("{v} => {b}"),
                App(_, f, i, x) => match i {
                    UnnamedExplicit => format!("({f} {x})"),
                    UnnamedImplicit => format!("({f} {{{x}}})"),
                    NamedImplicit(r) => format!("({f} {{{r} = {x}}})"),
                },
                RevApp(_, f, tys, x) => {
                    if tys.is_empty() {
                        format!("({x}.{f})")
                    } else {
                        format!(
                            "({x}.{f}<{}>",
                            tys.iter()
                                .map(|t| t.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    }
                }
                Sigma(_, p, b) => format!("{p} * {b}"),
                Tuple(_, a, b) => format!("[{a}, {b}]"),
                TupleBind(_, x, y, a, b) => format!("const [{x}, {y}] = {a};\n\t{b}"),
                Unit(_) => "unit".to_string(),
                TT(_) => "()".to_string(),
                UnitBind(_, a, b) => format!("{a};\n\t{b}"),
                Boolean(_) => "boolean".to_string(),
                False(_) => "false".to_string(),
                True(_) => "true".to_string(),
                If(_, p, t, e) => format!("{p} ? {t} : {e}"),
                String(_) => "string".to_string(),
                Str(_, v) => v.to_string(),
                Number(_) => "number".to_string(),
                Num(_, v) => v.to_string(),
                BigInt(_) => "bigint".to_string(),
                Big(_, v) => v.to_string(),
                Arr(_, xs) => format!(
                    "[{}]",
                    xs.iter()
                        .map(|x| x.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                Kv(_, xs) => format!(
                    "{{{}}}",
                    xs.iter()
                        .map(|(k, v)| format!("{k}: {v}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                Row(_) => "row".to_string(),
                Rowkey(_) => "rowkey".to_string(),
                At(_, a, k) => format!("{a} @ {k}"),
                Associate(_, a, n) => format!("{a}::{n}"),
                Fields(_, fields) => format!(
                    "({})",
                    fields
                        .iter()
                        .map(|(n, t)| format!("{n}: {t}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                Combine(_, a, b) => format!("{a} + {b}"),
                RowOrd(_, a, b) => format!("{a} keyof {b}"),
                RowEq(_, a, b) => format!("{a} = {b}"),
                Object(_, r) | Obj(_, r) => format!("{{{r}}}"),
                Concat(_, a, b) => format!("{a} & {b}"),
                Cat(_, a, b) => format!("{a}...{b}"),
                Access(_, n) => format!(".{n}"),
                Downcast(_, a) => format!("{{...{a}}}"),
                Enum(_, r) => format!("[{r}]"),
                Variant(_, n, a) => format!("{n}({a})"),
                Upcast(_, a) => format!("[...{a}]"),
                UpcastTo(_, a, t) => format!("{t}::{a}"),
                Switch(_, a, cs, d) => {
                    write!(f, "switch ({a}) {{")?;
                    for (n, v, e) in cs {
                        writeln!(f, "\tcase {n}({v}): {e}")?;
                    }
                    if let Some((v, e)) = d {
                        writeln!(f, "\tcase {v}: {e}")?;
                    }
                    return write!(f, "}}");
                }
                Unionify(_, a) => format!("{a}!"),
                Union(_, a, b) => format!("{a} | {b}"),
                Instanceof(_, a) => a.to_string(),
                Varargs(_, t) => format!("...Array<{t}>"),
                AnonVarargs(_, t) => format!("...{t}"),
                Spread(_, a) => format!("...{a}"),
                AnonSpread(..) => "...".to_string(),
                Typeof(_, a) => format!("typeof {a}"),
                Keyof(_, a) => format!("keyof {a}"),
                Pure(_) => "pure".to_string(),
                Effect(_, a) => a
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" | "),
                EmitAsync(_, a) => format!("await {a}"),
                TryCatch(_, body, catches) => format!(
                    "try {{\n\t{body}\n}}\n{}",
                    catches
                        .iter()
                        .map(|c| format!("catch ({})", c.i))
                        .collect::<Vec<_>>()
                        .join("\n")
                ),
            }
            .as_str(),
        )
    }
}

#[derive(Debug, Clone)]
pub struct Catch {
    pub i: Expr,
    pub inst_ty: Expr,
    pub inst_fns: Vec<(Src, Def<Expr>)>,
}
