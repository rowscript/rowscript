use crate::theory::abs::data::Term;
use crate::theory::abs::def::Sigma;

pub fn noinline(sigma: &Sigma, tm: &Term) -> bool {
    use Term::*;
    match tm {
        MetaRef(_, v, _) => {
            let tm = sigma.get(v).unwrap().to_term(v.clone());
            noinline(sigma, &tm)
        }
        Fields(fields) => {
            for tm in fields.values() {
                if noinline(sigma, tm) {
                    return true;
                }
            }
            false
        }
        Switch(a, b, d) => {
            if noinline(sigma, a) {
                return true;
            }
            for (_, a) in b.values() {
                if noinline(sigma, a) {
                    return true;
                }
            }
            if let Some((_, tm)) = d {
                if noinline(sigma, tm) {
                    return true;
                }
            }
            false
        }
        Guard(p, a, e, b) => {
            let mut fold = noinline(sigma, p) || noinline(sigma, a) || noinline(sigma, b);
            if let Some(e) = e {
                fold = fold || noinline(sigma, e);
            }
            fold
        }

        While(a, b, c) | If(a, b, c) => {
            noinline(sigma, a) || noinline(sigma, b) || noinline(sigma, c)
        }

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
        | Concat(a, b) => noinline(sigma, a) || noinline(sigma, b),

        Lam(.., a)
        | BoolNot(a)
        | NumNeg(a)
        | NumToStr(a)
        | Obj(a)
        | Access(a, ..)
        | Down(a, ..)
        | Variant(a)
        | Up(a, ..)
        | Spread(a)
        | Reflect(.., a) => noinline(sigma, a),

        Extern(..)
        | Let(..)
        | Update(..)
        | Return(..)
        | Continue
        | Break
        | ArrIterNext(..)
        | Arr(..)
        | ArrLength(..)
        | ArrPush(..)
        | ArrForeach(..)
        | ArrAt(..)
        | ArrInsert(..)
        | ArrIter(..)
        | MapIterNext(..)
        | Kv(..)
        | MapHas(..)
        | MapGet(..)
        | MapSet(..)
        | MapDelete(..)
        | MapClear(..)
        | MapIter(..)
        | Unionify(..)
        | Find { .. }
        | Panic(..)
        | ConsoleLog(..)
        | SetTimeout(..)
        | EmitAsync(..) => true,

        Ref(..)
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
