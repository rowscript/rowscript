use crate::basis::data::Ident;

type Label = Ident;

enum Dir {
    L,
    R,
}

struct Row {
    label: Label,
    typ: Type,
}

enum Type {
    Var(Ident),
    Arr(Vec<Type>),
    Pi(Vec<Row>),
    Sigma(Vec<Row>),
    Row(Label, Type),
}

enum Pred {
    Cont(Dir, Row, Row),
    Comb(Row, Row, Row),
}

struct QualifiedType {
    preds: Vec<Pred>,
    typ: Type,
}

struct Scheme {
    type_vars: Vec<Ident>,
    row_vars: Vec<Ident>,
    qualified: QualifiedType,
}

enum Term {
    Var(Ident),

    Abs(Vec<Ident>, Term),
    App(Vec<Term>),

    Let(Ident, Scheme, Term, Term),

    Rec(Label, Term),
    Sel(Term, Label),

    Prj(Dir, Term),
    Cat(Vec<Term>),

    Inj(Dir, Term),
    Case(Vec<Term>),
}
