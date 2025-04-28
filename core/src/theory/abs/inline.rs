use crate::theory::abs::data::Term;

pub fn noinline(tm: &Term) -> bool {
    use Term::*;
    match tm {
        Fields(fields) => fields.values().all(noinline),
        Switch(a, b, d) => {
            let is_a = noinline(a);
            let is_b = b.values().all(|(_, a)| noinline(a));
            let is_d = d.iter().all(|(_, tm)| noinline(tm));
            is_a && is_b && is_d
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
        | At(a, b)
        | Combine(.., a, b)
        | Cat(a, b) => noinline(a) || noinline(b),

        BoolNot(a)
        | StrToLowerCase(a)
        | NumNeg(a)
        | NumToStr(a)
        | BigintToStr(a)
        | RkToStr(a)
        | Obj(a)
        | Access(a, ..)
        | Down(a, ..)
        | Variant(a)
        | Up(a, ..)
        | Spread(a)
        | JSONStringify(a) => noinline(a),

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
        | Panic(..)
        | ConsoleLog(..)
        | ConsoleAssert(..)
        | SetTimeout(..)
        | EmitAsync(..)
        | HtmlElementAddEventListener(..)
        | DocumentGetElementById(..) => true,

        Ref(..)
        | MetaRef(..)
        | Qualified(..)
        | Undef(..)
        | Mu(..)
        | Univ
        | Pi { .. }
        | Lam(..)
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
        | AtResult { .. }
        | Associate(..)
        | RowOrd(..)
        | RowSat
        | RowEq(..)
        | RowRefl
        | Object(..)
        | Concat(..)
        | Downcast(..)
        | Enum(..)
        | Upcast(..)
        | Disjoint(..)
        | Union(..)
        | Find { .. }
        | Interface { .. }
        | InstanceofSat
        | Varargs(..)
        | AnonVarargs(..)
        | Typeof(..)
        | Keyof(..)
        | Discriminants(..)
        | Cls { .. }
        | Pure
        | Effect(..) => false,
    }
}
