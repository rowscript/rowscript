use crate::theory::abs::data::Term;

pub fn noinline(tm: &Term) -> bool {
    use Term::*;
    match tm {
        Fields(fields) => {
            for tm in fields.values() {
                if noinline(tm) {
                    return true;
                }
            }
            false
        }
        Switch(a, b, d) => {
            if noinline(a) {
                return true;
            }
            for (_, a) in b.values() {
                if noinline(a) {
                    return true;
                }
            }
            if let Some((_, tm)) = d {
                if noinline(tm) {
                    return true;
                }
            }
            false
        }
        Guard(p, a, e, b) => {
            let mut fold = noinline(p) || noinline(a) || noinline(b);
            if let Some(e) = e {
                fold = fold || noinline(e);
            }
            fold
        }

        While(a, b, c) | If(a, b, c) => noinline(a) || noinline(b) || noinline(c),

        Const(_, a, b)
        | Fori(a, b)
        | App(a, _, b)
        | Tuple(a, b)
        | TupleBind(.., a, b)
        | UnitBind(a, b)
        | BoolOr(a, b)
        | BoolAnd(a, b)
        | BoolEq(a, b)
        | BoolNeq(a, b)
        | StrAdd(a, b)
        | StrEq(a, b)
        | StrNeq(a, b)
        | NumAdd(a, b)
        | NumSub(a, b)
        | NumMul(a, b)
        | NumDiv(a, b)
        | NumMod(a, b)
        | NumEq(a, b)
        | NumNeq(a, b)
        | NumLe(a, b)
        | NumGe(a, b)
        | NumLt(a, b)
        | NumGt(a, b)
        | Combine(.., a, b)
        | Concat(a, b)
        | At(a, b) => noinline(a) || noinline(b),

        Lam(.., a)
        | BoolNot(a)
        | NumNeg(a)
        | NumToStr(a)
        | BigintToStr(a)
        | RkToStr(a)
        | Obj(a)
        | Access(a, ..)
        | Down(a, ..)
        | Variant(a)
        | Up(a, ..)
        | Spread(a) => noinline(a),

        Extern(..) | Let(..) | Update(..) | Return(..) | Continue | Break | ArrIterNext(..)
        | Arr(..) | ArrLength(..) | ArrPush(..) | ArrForeach(..) | ArrAt(..) | ArrInsert(..)
        | ArrIter(..) | MapIterNext(..) | Kv(..) | MapHas(..) | MapGet(..) | MapSet(..)
        | MapDelete(..) | MapClear(..) | MapIter(..) | Unionify(..) | Panic(..)
        | ConsoleLog(..) | SetTimeout(..) | JSONStringify(..) | EmitAsync(..) => true,

        Ref(..)
        | MetaRef(..)
        | Qualified(..)
        | Undef(..)
        | Mu(..)
        | Univ
        | Pi { .. }
        | Sigma(..)
        | Unit
        | TT
        | Boolean
        | False
        | True
        | String
        | Str(..)
        | Number
        | Num(..)
        | Bigint
        | Big(..)
        | ArrayIterator(..)
        | Array(..)
        | MapIterator(..)
        | Map(..)
        | Row
        | Rowkey
        | Rk(..)
        | Associate(..)
        | RowOrd(..)
        | RowSat
        | RowEq(..)
        | RowRefl
        | Object(..)
        | Downcast(..)
        | Enum(..)
        | Upcast(..)
        | Disjoint(..)
        | Find { .. }
        | Instanceof(..)
        | InstanceofSat
        | Varargs(..)
        | AnonVarargs(..)
        | Typeof(..)
        | Keyof(..)
        | Cls { .. }
        | Pure
        | Effect(..) => false,
    }
}
