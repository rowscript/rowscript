use crate::theory::abs::data::Term;

pub fn has_side_effect(tm: &Term) -> bool {
    use Term::*;
    match tm {
        Local(_, a, b) => has_side_effect(a) || has_side_effect(b),
        While(p, b, r) => has_side_effect(p) || has_side_effect(b) || has_side_effect(r),
        Fori(b, r) => has_side_effect(b) || has_side_effect(r),
        Guard(p, b, r) => has_side_effect(p) || has_side_effect(b) || has_side_effect(r),
        Lam(_, b) => has_side_effect(b),
        App(f, _, x) => has_side_effect(f) || has_side_effect(x),
        Tuple(a, b) => has_side_effect(a) || has_side_effect(b),
        TupleLocal(_, _, a, b) => has_side_effect(a) || has_side_effect(b),
        UnitLocal(a, b) => has_side_effect(a) || has_side_effect(b),
        If(p, a, b) => has_side_effect(p) || has_side_effect(a) || has_side_effect(b),
        BoolOr(a, b) => has_side_effect(a) || has_side_effect(b),
        BoolAnd(a, b) => has_side_effect(a) || has_side_effect(b),
        BoolNot(a) => has_side_effect(a),
        NumAdd(a, b) => has_side_effect(a) || has_side_effect(b),
        NumSub(a, b) => has_side_effect(a) || has_side_effect(b),
        NumMul(a, b) => has_side_effect(a) || has_side_effect(b),
        NumDiv(a, b) => has_side_effect(a) || has_side_effect(b),
        NumMod(a, b) => has_side_effect(a) || has_side_effect(b),
        NumEq(a, b) => has_side_effect(a) || has_side_effect(b),
        NumNeq(a, b) => has_side_effect(a) || has_side_effect(b),
        NumLe(a, b) => has_side_effect(a) || has_side_effect(b),
        NumGe(a, b) => has_side_effect(a) || has_side_effect(b),
        NumLt(a, b) => has_side_effect(a) || has_side_effect(b),
        NumGt(a, b) => has_side_effect(a) || has_side_effect(b),
        Fields(fields) => {
            for tm in fields.values() {
                if has_side_effect(tm) {
                    return true;
                }
            }
            false
        }
        Combine(_, a, b) => has_side_effect(a) || has_side_effect(b),
        Obj(a) => has_side_effect(a),
        Concat(a, b) => has_side_effect(a) || has_side_effect(b),
        Access(a, _) => has_side_effect(a),
        Down(a, _) => has_side_effect(a),
        Variant(a) => has_side_effect(a),
        Up(a, ..) => has_side_effect(a),
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
        Find(a, ..) => has_side_effect(a),

        Extern(..) | MetaRef(..) | LocalSet(..) | LocalUpdate(..) | Return(..) | Continue
        | Break | ArrIter(..) | ArrIterNext(..) | Arr(..) | ArrLength(..) | ArrPush(..)
        | ArrForeach(..) | ArrAt(..) | ArrInsert(..) | Kv(..) | MapHas(..) | MapGet(..)
        | MapSet(..) | MapDelete(..) | MapClear(..) | Unionify(..) | ErrorThrow(..)
        | ConsoleLog(..) => true,

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
        | Reflected(..)
        | Cls { .. } => false,

        Undef(..) => unreachable!(),
    }
}
