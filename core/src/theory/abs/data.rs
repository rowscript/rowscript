use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};

use crate::theory::abs::def::{Body, Sigma};
use crate::theory::conc::data::ArgInfo;
use crate::theory::conc::load::ModuleID;
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::{Param, ParamInfo, Syntax, Tele, Var};

pub type Spine = Vec<(ParamInfo, Term)>;

pub type FieldMap = HashMap<String, Term>;
pub type FieldSet = HashSet<Var>;
pub type CaseMap = HashMap<String, (Var, Term)>;
pub type CaseDefault = Option<(Var, Box<Term>)>;

#[derive(Debug, Clone, Eq, PartialEq)]
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
    Mu(Var),

    Const(Param<Self>, Box<Self>, Box<Self>),
    Let(Param<Self>, Box<Self>, Box<Self>),
    Update(Var, Box<Self>, Box<Self>),
    While(Box<Self>, Box<Self>, Box<Self>),
    Fori(Box<Self>, Box<Self>),
    Guard(Box<Self>, Box<Self>, Option<Box<Self>>, Box<Self>),
    Return(Box<Self>),
    Continue,
    Break,

    Univ,

    Pi {
        param: Param<Self>,
        eff: Box<Self>,
        body: Box<Self>,
    },
    Lam(Param<Self>, Box<Self>),
    App(Box<Self>, ArgInfo, Box<Self>),

    Sigma(Param<Self>, Box<Self>),
    Tuple(Box<Self>, Box<Self>),
    TupleBind(Param<Self>, Param<Self>, Box<Self>, Box<Self>),

    Unit,
    TT,
    UnitBind(Box<Self>, Box<Self>),

    Boolean,
    False,
    True,
    If(Box<Self>, Box<Self>, Box<Self>),
    BoolOr(Box<Self>, Box<Self>),
    BoolAnd(Box<Self>, Box<Self>),
    BoolNot(Box<Self>),
    BoolEq(Box<Self>, Box<Self>),
    BoolNeq(Box<Self>, Box<Self>),

    String,
    Str(String),
    StrAdd(Box<Self>, Box<Self>),
    StrEq(Box<Self>, Box<Self>),
    StrNeq(Box<Self>, Box<Self>),

    Number,
    Num(f64),
    NumAdd(Box<Self>, Box<Self>),
    NumSub(Box<Self>, Box<Self>),
    NumMul(Box<Self>, Box<Self>),
    NumDiv(Box<Self>, Box<Self>),
    NumMod(Box<Self>, Box<Self>),
    NumEq(Box<Self>, Box<Self>),
    NumNeq(Box<Self>, Box<Self>),
    NumLe(Box<Self>, Box<Self>),
    NumGe(Box<Self>, Box<Self>),
    NumLt(Box<Self>, Box<Self>),
    NumGt(Box<Self>, Box<Self>),
    NumNeg(Box<Self>),
    NumToStr(Box<Self>),

    Bigint,
    Big(String),
    BigintToStr(Box<Self>),

    ArrayIterator(Box<Self>),
    ArrIterNext(Box<Self>),
    Array(Box<Self>),
    Arr(Vec<Self>),
    ArrLength(Box<Self>),
    ArrPush(Box<Self>, Box<Self>),
    ArrForeach(Box<Self>, Box<Self>),
    ArrAt(Box<Self>, Box<Self>),
    ArrInsert(Box<Self>, Box<Self>, Box<Self>),
    ArrIter(Box<Self>),

    MapIterator(Box<Self>),
    MapIterNext(Box<Self>),
    Map(Box<Self>, Box<Self>),
    Kv(Vec<(Self, Self)>),
    MapHas(Box<Self>, Box<Self>),
    MapGet(Box<Self>, Box<Self>),
    MapSet(Box<Self>, Box<Self>, Box<Self>),
    MapDelete(Box<Self>, Box<Self>),
    MapClear(Box<Self>),
    MapIter(Box<Self>),

    Row,
    Rowkey,
    Rk(String),
    RkToStr(Box<Self>),
    AtResult {
        fields_ty: Box<Self>,
        key: Box<Self>,
    },
    At(Box<Self>, Box<Self>),
    Fields(FieldMap),
    Associate(Box<Self>, String),
    Combine(bool, Box<Self>, Box<Self>),

    RowOrd(Box<Self>, Box<Self>),
    RowSat,

    RowEq(Box<Self>, Box<Self>),
    RowRefl,

    Object(Box<Self>),
    Obj(Box<Self>),
    Concat(Box<Self>, Box<Self>),
    Cat(Box<Self>, Box<Self>),
    Access(Box<Self>, String),
    Downcast(Box<Self>, Box<Self>),
    Down(Box<Self>, Box<Self>),

    Enum(Box<Self>),
    Variant(Box<Self>),
    Upcast(Box<Self>),
    Disjoint(Box<Self>, Box<Self>),
    Up(Box<Self>, Box<Self>, Box<Self>),
    Switch(Box<Self>, CaseMap, CaseDefault),
    Unionify(Box<Self>),

    Find {
        instance_ty: Box<Self>,
        interface: Var,
        interface_fn: Var,
    },
    Instanceof(Box<Self>, Var),
    InstanceofSat,

    Varargs(Box<Self>),
    AnonVarargs(Box<Self>),
    Spread(Box<Self>),

    Typeof(Box<Self>),
    Keyof(Box<Self>),
    Discriminants(Box<Self>),

    Cls {
        class: Var,
        type_args: Vec<Self>,
        associated: HashMap<String, Self>,
        object: Box<Self>,
    },

    Panic(Box<Self>),
    ConsoleLog(Box<Self>),
    SetTimeout(Box<Self>, Box<Self>, Box<Self>),
    JSONStringify(Box<Self>),

    Pure,
    Effect(FieldSet),
    EmitAsync(Box<Self>),
}

pub struct PartialClass {
    pub applied_types: Box<[Term]>,
    pub type_params: Box<[Term]>,
    pub associated: HashMap<String, Var>,
    pub methods: HashMap<String, Var>,
}

impl Term {
    pub fn lam(tele: &Tele<Self>, tm: Self) -> Self {
        tele.iter()
            .rfold(tm, |b, p| Self::Lam(p.clone(), Box::new(b)))
    }

    pub fn pi(tele: &Tele<Self>, eff: Self, tm: Self) -> Self {
        tele.iter().rfold(tm, |b, p| Self::Pi {
            param: p.clone(),
            eff: Box::new(if p.info == Explicit {
                eff.clone()
            } else {
                Self::Pure
            }),
            body: Box::new(b),
        })
    }

    pub fn tele_to_spine(tele: &Tele<Self>) -> Spine {
        tele.iter()
            .map(|p| (p.info, Self::Ref(p.var.clone())))
            .collect()
    }

    pub fn bool(v: bool) -> Self {
        if v {
            Self::True
        } else {
            Self::False
        }
    }

    pub fn class_methods(&self, sigma: &Sigma) -> Option<PartialClass> {
        use Body::*;
        use Term::*;

        let mut x = self;
        loop {
            let (params, associated, methods) = match x {
                Cls {
                    class, type_args, ..
                } => match &sigma.get(class).unwrap().body {
                    Class {
                        associated,
                        methods,
                        ..
                    } => (type_args.clone(), associated.clone(), methods.clone()),
                    _ => unreachable!(),
                },
                Varargs(tm) | Pi { body: tm, .. } | Lam(.., tm) => {
                    x = tm.as_ref();
                    continue;
                }
                _ => return None,
            };
            let mut applied = Vec::default();
            for arg in params.iter() {
                if matches!(arg, Ref(..)) {
                    continue;
                }
                applied.push(arg.clone())
            }
            let applied_types = applied.into_boxed_slice();
            let type_params = params.into_boxed_slice();
            return Some(PartialClass {
                applied_types,
                type_params,
                associated,
                methods,
            });
        }
    }

    pub fn auto_implicit(&self) -> Option<Self> {
        use Term::*;
        match self {
            RowEq(..) => Some(RowRefl),
            RowOrd(..) => Some(RowSat),
            Instanceof(..) => Some(InstanceofSat),
            _ => None,
        }
    }

    pub fn is_unsolved(&self) -> bool {
        use Term::*;
        let tm = match self {
            Object(a) | Enum(a) => a.as_ref(),
            tm => tm,
        };
        matches!(tm, MetaRef(..) | Ref(..) | AtResult { .. })
    }

    fn is_solved_auto_implicit(&self) -> bool {
        use Term::*;
        match self {
            RowEq(a, b) | RowOrd(a, b) => !a.is_unsolved() && !b.is_unsolved(),
            Instanceof(a, ..) => !a.is_unsolved(),
            _ => false,
        }
    }

    pub fn unwrap_solved_implicit_lambda(tm: Self, ty: Self) -> (Self, Self) {
        use Term::*;
        match (tm, ty) {
            (Lam(p, b), Pi { body, .. })
                if p.info == Implicit && p.typ.is_solved_auto_implicit() =>
            {
                (*b, *body)
            }
            ret => ret,
        }
    }

    pub fn async_effect(v: Var) -> Self {
        use Term::*;
        Effect(FieldSet::from([v]))
    }

    pub fn is_binder(&self) -> bool {
        use Term::*;
        matches!(
            self,
            Const(..)
                | Let(..)
                | Update(..)
                | While(..)
                | Fori(..)
                | Guard(..)
                | TupleBind(..)
                | UnitBind(..)
        )
    }

    pub fn has_mu(&self) -> bool {
        use Term::*;
        let mut tm = self;
        loop {
            match tm {
                App(f, ..) => {
                    tm = f.as_ref();
                    continue;
                }
                Mu(..) => return true,
                _ => return false,
            }
        }
    }

    fn list_empty() -> Self {
        use Term::*;
        Variant(Box::new(Fields(FieldMap::from([(
            "Empty".to_string(),
            TT,
        )]))))
    }

    fn list_append(value: Self, list: Self) -> Self {
        use Term::*;
        Variant(Box::new(Fields(FieldMap::from([(
            "Append".to_string(),
            Obj(Box::new(Fields(FieldMap::from([
                ("value".to_string(), value),
                ("list".to_string(), list),
            ])))),
        )]))))
    }

    pub fn rowkey_list(m: FieldMap) -> Self {
        use Term::*;
        m.into_keys()
            .fold(Self::list_empty(), |ret, k| Self::list_append(Rk(k), ret))
    }
}

impl Syntax for Term {}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Term::*;
        f.write_str(
            match self {
                Ref(r) | Extern(r) | Undef(r) => r.to_string(),
                Qualified(m, r) => format!("{m}::{r}"),
                Mu(r) => format!("mu({r})"),
                MetaRef(k, r, ..) => format!("{k}{r}"),
                Const(p, a, b) => format!("const {p} = {a};\n\t{b}"),
                Let(p, a, b) => format!("let {p} = {a};\n\t{b}"),
                Update(v, a, b) => format!("{v} = {a};\n\t{b}"),
                While(p, b, r) => format!("while ({p}) {{\n\t{b}}}\n{r}"),
                Fori(b, r) => format!("for {{ {b} }}\n{r}"),
                Guard(p, b, e, r) => {
                    if let Some(e) = e {
                        format!("if ({p}) {{\n\t{b}}} else {{\n\t{e}}}\n{r}")
                    } else {
                        format!("if ({p}) {{\n\t{b}}}\n{r}")
                    }
                }
                Return(a) => format!("return {a}"),
                Continue => "continue".to_string(),
                Break => "break".to_string(),
                Univ => "type".to_string(),
                Pi { param, eff, body } => match eff.as_ref() {
                    Pure => format!("{param} -> {body}"),
                    e => format!("{param} -> {e} {body}"),
                },
                Lam(p, b) => format!("{p} => {b}"),
                App(f, _, x) => format!("({f} {x})"),
                Sigma(p, b) => format!("{p} * {b}"),
                Tuple(a, b) => format!("[{a}, {b}]"),
                TupleBind(p, q, a, b) => format!("const [{p}, {q}] = {a};\n\t{b}"),
                Unit => "unit".to_string(),
                TT => "()".to_string(),
                UnitBind(a, b) => format!("{a};\n\t{b}"),
                Boolean => "boolean".to_string(),
                False => "false".to_string(),
                True => "true".to_string(),
                If(p, t, e) => format!("if {p} {{ {t} }} else {{ {e} }}"),
                BoolOr(a, b) => format!("{a} || {b}"),
                BoolAnd(a, b) => format!("{a} && {b}"),
                BoolNot(a) => format!("!{a}"),
                BoolEq(a, b) => format!("{a} == {b}"),
                BoolNeq(a, b) => format!("{a} != {b}"),
                String => "string".to_string(),
                Str(v) => v.clone(),
                StrAdd(a, b) => format!("{a} + {b}"),
                StrEq(a, b) => format!("{a} == {b}"),
                StrNeq(a, b) => format!("{a} != {b}"),
                Number => "number".to_string(),
                Num(v) => v.to_string(),
                NumAdd(a, b) => format!("{a} + {b}"),
                NumSub(a, b) => format!("{a} - {b}"),
                NumMul(a, b) => format!("{a} * {b}"),
                NumDiv(a, b) => format!("{a} / {b}"),
                NumMod(a, b) => format!("{a} % {b}"),
                NumEq(a, b) => format!("{a} == {b}"),
                NumNeq(a, b) => format!("{a} != {b}"),
                NumLe(a, b) => format!("{a} <= {b}"),
                NumGe(a, b) => format!("{a} >= {b}"),
                NumLt(a, b) => format!("{a} < {b}"),
                NumGt(a, b) => format!("{a} > {b}"),
                NumNeg(a) => format!("-{a}"),
                NumToStr(a) | BigintToStr(a) | RkToStr(a) => format!("{a}.toString()"),
                Bigint => "bigint".to_string(),
                Big(v) => v.clone(),
                ArrayIterator(t) => format!("NativeArrayIterator<{t}>"),
                ArrIterNext(it) => format!("{it}.next()"),
                Array(t) => format!("NativeArray<{t}>"),
                Arr(xs) => format!(
                    "[{}]",
                    xs.iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                ArrLength(a) => format!("{a}.length"),
                ArrPush(a, v) => format!("{a}.push({v})"),
                ArrForeach(a, f) => format!("{a}.forEach({f})"),
                ArrAt(a, i) => format!("{a}.at({i})"),
                ArrInsert(a, i, v) => format!("{a}.insert({i}, {v})"),
                ArrIter(a) => format!("{a}.iter()"),
                MapIterator(t) => format!("NativeMapIterator<{t}>"),
                MapIterNext(it) => format!("{it}.next()"),
                Map(k, v) => format!("NativeMap<{k}, {v}>"),
                Kv(xs) => format!(
                    "{{{}}}",
                    xs.iter()
                        .map(|(k, v)| format!("{k}: {v}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                MapHas(m, k) => format!("{m}.has({k})"),
                MapGet(m, k) => format!("{m}.get({k})"),
                MapSet(m, k, v) => format!("{m}.set({k}, {v})"),
                MapDelete(m, k) => format!("{m}.delete({k})"),
                MapClear(m) => format!("{m}.clear()"),
                MapIter(m) => format!("{m}.iter()"),
                Row => "row".to_string(),
                Rowkey => "rowkey".to_string(),
                Rk(k) => k.clone(),
                AtResult { key, .. } => format!("?.{key}"),
                At(a, k) => format!("{a}[{k}]"),
                Fields(fields) => format!(
                    "({})",
                    fields
                        .iter()
                        .map(|(f, typ)| format!("{f}: {typ}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                Associate(a, n) => format!("{a}::{n}"),
                Combine(inplace, a, b) => {
                    if *inplace {
                        format!("{a} += {b}")
                    } else {
                        format!("{a} + {b}")
                    }
                }
                RowOrd(a, b) => format!("{a} keyof {b}"),
                RowSat => "sat".to_string(),
                RowEq(a, b) => format!("{a} = {b}"),
                RowRefl => "refl".to_string(),
                Object(r) => format!("{{{r}}}"),
                Obj(r) => format!("{{{r}}}"),
                Concat(a, b) | Cat(a, b) => format!("{a}...{b}"),
                Access(a, n) => format!("{a}.{n}"),
                Downcast(a, _) => format!("downcast<{a}>"),
                Down(a, _) => format!("{{...{a}}}"),
                Enum(r) => format!("[{r}]"),
                Variant(r) => format!("[{r}]"),
                Upcast(a) => format!("upcast<{a}>"),
                Disjoint(a, b) => format!("disjoint<{a}, {b}>"),
                Up(a, _, _) => format!("[...{a}]"),
                Switch(a, cs, d) => {
                    writeln!(f, "switch ({a}) {{")?;
                    for (n, (v, e)) in cs {
                        writeln!(f, "\tcase {n}({v}): {e}")?;
                    }
                    if let Some((v, e)) = d {
                        writeln!(f, "\tcase {v}: {e}")?;
                    }
                    return write!(f, "}}");
                }
                Unionify(a) => format!("unionify({a})"),
                Find {
                    instance_ty,
                    interface,
                    interface_fn,
                    ..
                } => format!("{interface}.{interface_fn}<{instance_ty}>"),
                Instanceof(t, i) => format!("{t} instanceof {i}"),
                InstanceofSat => "instanceofSat".to_string(),
                Varargs(t) => format!("...Array<{t}>"),
                AnonVarargs(t) => format!("...{t}"),
                Spread(a) => format!("...{a}"),
                Typeof(ty) => format!("typeof<{ty}>()"),
                Keyof(o) => format!("keyof<{o}>()"),
                Discriminants(ty) => format!("discriminants<{ty}>()"),
                Cls { class, .. } => format!("class {class}"),
                Panic(a) => format!("panic({a})"),
                ConsoleLog(m) => format!("console.log({m})"),
                SetTimeout(f, d, x) => format!("setTimeout({f}, {d}, {x})"),
                JSONStringify(a) => format!("JSON.stringify({a})"),
                Pure => "pure".to_string(),
                Effect(a) => a
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" | "),
                EmitAsync(a) => format!("await {a}"),
            }
            .as_str(),
        )
    }
}
