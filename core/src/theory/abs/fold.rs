use crate::theory::abs::data::Term;

pub fn should_fold(tm: &Term) -> bool {
    use Term::*;
    match tm {
        Fields(fields) => {
            for tm in fields.values() {
                if should_fold(tm) {
                    return true;
                }
            }
            false
        }
        Switch(a, b, d) => {
            if should_fold(a) {
                return true;
            }
            for (_, a) in b.values() {
                if should_fold(a) {
                    return true;
                }
            }
            if let Some((_, tm)) = d {
                if should_fold(tm) {
                    return true;
                }
            }
            false
        }
        Guard(p, a, e, b) => {
            let mut fold = should_fold(p) || should_fold(a) || should_fold(b);
            if let Some(e) = e {
                fold = fold || should_fold(e);
            }
            fold
        }

        While(a, b, c) | If(a, b, c) => should_fold(a) || should_fold(b) || should_fold(c),

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
        | Concat(a, b) => should_fold(a) || should_fold(b),

        Lam(.., a)
        | BoolNot(a)
        | NumNeg(a)
        | NumToStr(a)
        | Obj(a)
        | Access(a, ..)
        | Down(a, ..)
        | Variant(a)
        | Up(a, ..)
        | Find(a, ..)
        | Spread(a) => should_fold(a),

        Extern(..) | MetaRef(..) | Undef(..) | Let(..) | Update(..) | Return(..) | Continue
        | Break | ArrIterNext(..) | Arr(..) | ArrLength(..) | ArrPush(..) | ArrForeach(..)
        | ArrAt(..) | ArrInsert(..) | ArrIter(..) | MapIterNext(..) | Kv(..) | MapHas(..)
        | MapGet(..) | MapSet(..) | MapDelete(..) | MapClear(..) | MapIter(..) | Unionify(..)
        | ErrorThrow(..) | ConsoleLog(..) | SetTimeout(..) | EmitAsync(..) => true,

        Ref(..)
        | Qualified(..)
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
        | BigInt
        | Big(..)
        | ArrayIterator(..)
        | Array(..)
        | MapIterator(..)
        | Map(..)
        | Row
        | Associate(..)
        | RowOrd(..)
        | RowSat
        | RowEq(..)
        | RowRefl
        | Object(..)
        | Downcast(..)
        | Enum(..)
        | Upcast(..)
        | Instanceof(..)
        | InstanceofSat
        | Varargs(..)
        | AnonVarargs(..)
        | Reflected(..)
        | Cls { .. }
        | Pure
        | Effect(..) => false,
    }
}
