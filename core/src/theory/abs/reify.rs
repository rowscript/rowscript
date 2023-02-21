use crate::theory::abs::data::Term;
use crate::theory::conc::data::ArgInfo::UnnamedExplicit;
use crate::theory::conc::data::Expr;
use crate::theory::{Loc, Param};

pub fn reify(loc: Loc, tm: Box<Term>) -> Box<Expr> {
    use Term::*;
    Box::new(match *tm {
        Ref(x) => Expr::Resolved(loc, x),
        MetaRef(x, _) => Expr::Resolved(loc, x),
        Undef(x) => Expr::Resolved(loc, x),
        Let(p, a, b) => Expr::Let(
            loc,
            p.var,
            Some(reify(loc, p.typ)),
            reify(loc, a),
            reify(loc, b),
        ),
        Univ => Expr::Univ(loc),
        Pi(p, b) => Expr::Pi(loc, param(loc, p), reify(loc, b)),
        Lam(p, b) => Expr::Lam(loc, p.var, reify(loc, b)),
        App(f, x) => Expr::App(loc, reify(loc, f), UnnamedExplicit, reify(loc, x)),
        Sigma(p, b) => Expr::Sigma(loc, param(loc, p), reify(loc, b)),
        Tuple(a, b) => Expr::Tuple(loc, reify(loc, a), reify(loc, b)),
        TupleLet(p, q, a, b) => Expr::TupleLet(loc, p.var, q.var, reify(loc, a), reify(loc, b)),
        Unit => Expr::Unit(loc),
        TT => Expr::TT(loc),
        UnitLet(a, b) => Expr::UnitLet(loc, reify(loc, a), reify(loc, b)),
        Boolean => Expr::Boolean(loc),
        False => Expr::False(loc),
        True => Expr::True(loc),
        If(p, t, e) => Expr::If(loc, reify(loc, p), reify(loc, t), reify(loc, e)),
        String => Expr::String(loc),
        Str(v) => Expr::Str(loc, v),
        Number => Expr::Number(loc),
        Num(r, _) => Expr::Num(loc, r),
        BigInt => Expr::BigInt(loc),
        Big(v) => Expr::Big(loc, v),
        Row => Expr::Row(loc),
        Fields(f) => Expr::Fields(
            loc,
            f.into_iter()
                .map(|(s, tm)| (s, *reify(loc, Box::new(tm))))
                .collect(),
        ),
        Combine(a, b) => Expr::Combine(loc, reify(loc, a), reify(loc, b)),
        RowOrd(a, d, b) => Expr::RowOrd(loc, reify(loc, a), d, reify(loc, b)),
        RowSat => unreachable!(),
        RowEq(a, b) => Expr::RowEq(loc, reify(loc, a), reify(loc, b)),
        RowRefl => unreachable!(),
        Object(r) => Expr::Object(loc, reify(loc, r)),
        Obj(a) => Expr::Obj(loc, reify(loc, a)),
        Concat(a, b) => Expr::Concat(loc, reify(loc, a), reify(loc, b)),
        Access(a, n) => Expr::App(
            loc,
            Box::new(Expr::Access(loc, n)),
            UnnamedExplicit,
            reify(loc, a),
        ),
        Downcast(a, _) => Expr::Downcast(loc, reify(loc, a)),
        Enum(r) => Expr::Enum(loc, reify(loc, r)),
        Variant(_) => todo!("should use Fields here"),
        Upcast(a, _) => Expr::Upcast(loc, reify(loc, a)),
        Switch(a, cs) => Expr::Switch(
            loc,
            reify(loc, a),
            cs.into_iter()
                .map(|(c, (v, tm))| (c, v, *reify(loc, Box::new(tm))))
                .collect(),
        ),
        Vptr(r) => Expr::Vptr(loc, r),
        InterfaceRef(r) => Expr::InterfaceRef(loc, r),
    })
}

fn param(loc: Loc, p: Param<Term>) -> Param<Expr> {
    Param {
        var: p.var,
        info: p.info,
        typ: reify(loc, p.typ),
    }
}
