use crate::theory::abs::data::Term;

pub fn has_side_effect(tm: &Term) -> bool {
    use Term::*;
    match tm {
        Fields(fields) => {
            for tm in fields.values() {
                if has_side_effect(tm) {
                    return true;
                }
            }
            false
        }
        Switch(a, b, d) => {
            if has_side_effect(a) {
                return true;
            }
            for (_, a) in b.values() {
                if has_side_effect(a) {
                    return true;
                }
            }
            if let Some((_, tm)) = d {
                if has_side_effect(tm) {
                    return true;
                }
            }
            false
        }
        Guard(p, a, e, b) => {
            let mut has_effect = has_side_effect(p) || has_side_effect(a) || has_side_effect(b);
            if let Some(e) = e {
                has_effect = has_effect || has_side_effect(e);
            }
            has_effect
        }

        While(a, b, c) | If(a, b, c) => {
            has_side_effect(a) || has_side_effect(b) || has_side_effect(c)
        }

        Local(_, a, b)
        | Fori(a, b)
        | App(a, _, b)
        | Tuple(a, b)
        | TupleLocal(.., a, b)
        | UnitLocal(a, b)
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
        | Concat(a, b) => has_side_effect(a) || has_side_effect(b),

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
        | Spread(a) => has_side_effect(a),

        Extern(..) | MetaRef(..) | Undef(..) | LocalSet(..) | LocalUpdate(..) | Return(..)
        | Continue | Break | ArrIterNext(..) | Arr(..) | ArrLength(..) | ArrPush(..)
        | ArrForeach(..) | ArrAt(..) | ArrInsert(..) | ArrIter(..) | MapIterNext(..) | Kv(..)
        | MapHas(..) | MapGet(..) | MapSet(..) | MapDelete(..) | MapClear(..) | MapIter(..)
        | Unionify(..) | ErrorThrow(..) | ConsoleLog(..) => true,

        Ref(..)
        | Qualified(..)
        | Univ
        | Pi(..)
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
        | ImplementsOf(..)
        | ImplementsSat
        | VarArr(..)
        | Reflected(..)
        | Cls { .. } => false,
    }
}
