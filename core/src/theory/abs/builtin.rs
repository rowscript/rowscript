use crate::theory::abs::data::Term;
use crate::theory::abs::def::{Body, Def, Sigma};

use crate::theory::conc::resolve::{NameMap, ResolvedVar, VarKind};
use crate::theory::ParamInfo::{Explicit, Implicit};
use crate::theory::{Param, Tele, Var};

fn implicit(var: Var, typ: Term) -> Param<Term> {
    Param {
        var,
        info: Implicit,
        typ: Box::new(typ),
    }
}

fn explicit(var: Var, typ: Term) -> Param<Term> {
    Param {
        var,
        info: Explicit,
        typ: Box::new(typ),
    }
}

fn tuple_params<const N: usize>(var: Var, tele: [Param<Term>; N]) -> Tele<Term> {
    let mut ty = Term::Unit;
    for x in tele.into_iter().rev() {
        ty = Term::Sigma(x, Box::new(ty));
    }
    vec![Param {
        var,
        info: Explicit,
        typ: Box::new(ty),
    }]
}

#[derive(Debug)]
pub struct Builtins {
    pub ubiquitous: NameMap,

    pub unionify: Var,

    pub reflect: Var,

    pub number_add: Var,
    pub number_sub: Var,
    pub number_eq: Var,
    pub number_neq: Var,
    pub number_le: Var,
    pub number_ge: Var,
    pub number_lt: Var,
    pub number_gt: Var,

    pub boolean_or: Var,
    pub boolean_and: Var,
    pub boolean_not: Var,
}

impl Builtins {
    pub fn new(sigma: &mut Sigma) -> Self {
        let mut ret = Self {
            ubiquitous: NameMap::default(),
            unionify: Var::new("unionify"),
            reflect: Var::new("Reflected"),
            number_add: Var::new("number#__add__"),
            number_sub: Var::new("number#__sub__"),
            number_le: Var::new("number#__le__"),
            number_eq: Var::new("number#__eq__"),
            number_neq: Var::new("number#__neq__"),
            number_ge: Var::new("number#__ge__"),
            number_lt: Var::new("number#__lt__"),
            number_gt: Var::new("number#__gt__"),
            boolean_or: Var::new("boolean#__or__"),
            boolean_and: Var::new("boolean#__and__"),
            boolean_not: Var::new("boolean#__not__"),
        };
        ret.insert_unionify(sigma);
        ret.insert_reflect(sigma);
        ret.insert_number_add(sigma);
        ret.insert_number_sub(sigma);
        ret.insert_number_eq(sigma);
        ret.insert_number_neq(sigma);
        ret.insert_number_le(sigma);
        ret.insert_number_ge(sigma);
        ret.insert_number_lt(sigma);
        ret.insert_number_gt(sigma);
        ret.insert_boolean_or(sigma);
        ret.insert_boolean_and(sigma);
        ret.insert_boolean_not(sigma);
        ret
    }

    fn insert_def(&mut self, sigma: &mut Sigma, def: Def<Term>) {
        self.ubiquitous.insert(
            def.name.to_string(),
            ResolvedVar(VarKind::InModule, def.name.clone()),
        );
        sigma.insert(def.name.clone(), def);
    }

    fn insert_unionify(&mut self, sigma: &mut Sigma) {
        let r = Var::new("'R");
        let a_ty = Term::Enum(Box::new(Term::Ref(r.clone())));
        let tupled = Var::tupled();
        let mut tele = vec![implicit(r, Term::Row)];
        let tupled_tele = tuple_params(tupled.clone(), [explicit(Var::new("a"), a_ty.clone())]);
        let untupled_a = Var::new("a");
        let body = Body::Fn(Term::TupleLet(
            explicit(untupled_a.clone(), a_ty.clone()),
            explicit(Var::unbound(), Term::Unit),
            Box::new(Term::Ref(tupled)),
            Box::new(Term::Unionify(Box::new(Term::Ref(untupled_a)))),
        ));
        tele.extend(tupled_tele);
        self.insert_def(
            sigma,
            Def {
                loc: Default::default(),
                name: self.unionify.clone(),
                tele,
                ret: Box::new(a_ty),
                body,
            },
        )
    }

    fn insert_reflect(&mut self, sigma: &mut Sigma) {
        let t = Var::new("T");
        self.insert_def(
            sigma,
            Def {
                loc: Default::default(),
                name: self.reflect.clone(),
                tele: vec![implicit(t.clone(), Term::Univ)],
                ret: Box::new(Term::Univ),
                body: Body::Fn(Term::Reflected(Box::new(Term::Ref(t)))),
            },
        )
    }

    fn insert_number_add(&mut self, sigma: &mut Sigma) {
        let b = Var::new("b");
        let tupled = Var::tupled();
        let untupled_a = Var::new("a");
        let untupled_a_rhs = Var::new("a").untupled_rhs();
        let untupled_b = Var::new("b");
        let body = Body::Fn(Term::TupleLet(
            explicit(untupled_a.clone(), Term::Number),
            explicit(
                untupled_a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLet(
                explicit(untupled_b.clone(), Term::Number),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(untupled_a_rhs)),
                Box::new(Term::NumAdd(
                    Box::new(Term::Ref(untupled_a)),
                    Box::new(Term::Ref(untupled_b)),
                )),
            )),
        ));
        self.insert_def(
            sigma,
            Def {
                loc: Default::default(),
                name: self.number_add.clone(),
                tele: tuple_params(
                    tupled,
                    [
                        explicit(Var::new("a"), Term::Number),
                        explicit(b, Term::Number),
                    ],
                ),
                ret: Box::new(Term::Number),
                body,
            },
        )
    }

    fn insert_number_sub(&mut self, sigma: &mut Sigma) {
        let b = Var::new("b");
        let tupled = Var::tupled();
        let untupled_a = Var::new("a");
        let untupled_a_rhs = Var::new("a").untupled_rhs();
        let untupled_b = Var::new("b");
        let body = Body::Fn(Term::TupleLet(
            explicit(untupled_a.clone(), Term::Number),
            explicit(
                untupled_a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLet(
                explicit(untupled_b.clone(), Term::Number),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(untupled_a_rhs)),
                Box::new(Term::NumSub(
                    Box::new(Term::Ref(untupled_a)),
                    Box::new(Term::Ref(untupled_b)),
                )),
            )),
        ));
        self.insert_def(
            sigma,
            Def {
                loc: Default::default(),
                name: Var::new("number#__sub__"),
                tele: tuple_params(
                    tupled,
                    [
                        explicit(Var::new("a"), Term::Number),
                        explicit(b, Term::Number),
                    ],
                ),
                ret: Box::new(Term::Number),
                body,
            },
        )
    }

    fn insert_number_eq(&mut self, sigma: &mut Sigma) {
        let b = Var::new("b");
        let tupled = Var::tupled();
        let untupled_a = Var::new("a");
        let untupled_a_rhs = Var::new("a").untupled_rhs();
        let untupled_b = Var::new("b");
        let body = Body::Fn(Term::TupleLet(
            explicit(untupled_a.clone(), Term::Number),
            explicit(
                untupled_a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLet(
                explicit(untupled_b.clone(), Term::Number),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(untupled_a_rhs)),
                Box::new(Term::NumEq(
                    Box::new(Term::Ref(untupled_a)),
                    Box::new(Term::Ref(untupled_b)),
                )),
            )),
        ));
        self.insert_def(
            sigma,
            Def {
                loc: Default::default(),
                name: Var::new("number#__eq__"),
                tele: tuple_params(
                    tupled,
                    [
                        explicit(Var::new("a"), Term::Number),
                        explicit(b, Term::Number),
                    ],
                ),
                ret: Box::new(Term::Boolean),
                body,
            },
        )
    }

    fn insert_number_neq(&mut self, sigma: &mut Sigma) {
        let b = Var::new("b");
        let tupled = Var::tupled();
        let untupled_a = Var::new("a");
        let untupled_a_rhs = Var::new("a").untupled_rhs();
        let untupled_b = Var::new("b");
        let body = Body::Fn(Term::TupleLet(
            explicit(untupled_a.clone(), Term::Number),
            explicit(
                untupled_a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLet(
                explicit(untupled_b.clone(), Term::Number),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(untupled_a_rhs)),
                Box::new(Term::NumNeq(
                    Box::new(Term::Ref(untupled_a)),
                    Box::new(Term::Ref(untupled_b)),
                )),
            )),
        ));
        self.insert_def(
            sigma,
            Def {
                loc: Default::default(),
                name: Var::new("number#__neq__"),
                tele: tuple_params(
                    tupled,
                    [
                        explicit(Var::new("a"), Term::Number),
                        explicit(b, Term::Number),
                    ],
                ),
                ret: Box::new(Term::Boolean),
                body,
            },
        )
    }

    fn insert_number_le(&mut self, sigma: &mut Sigma) {
        let b = Var::new("b");
        let tupled = Var::tupled();
        let untupled_a = Var::new("a");
        let untupled_a_rhs = Var::new("a").untupled_rhs();
        let untupled_b = Var::new("b");
        let body = Body::Fn(Term::TupleLet(
            explicit(untupled_a.clone(), Term::Number),
            explicit(
                untupled_a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLet(
                explicit(untupled_b.clone(), Term::Number),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(untupled_a_rhs)),
                Box::new(Term::NumLe(
                    Box::new(Term::Ref(untupled_a)),
                    Box::new(Term::Ref(untupled_b)),
                )),
            )),
        ));
        self.insert_def(
            sigma,
            Def {
                loc: Default::default(),
                name: Var::new("number#__le__"),
                tele: tuple_params(
                    tupled,
                    [
                        explicit(Var::new("a"), Term::Number),
                        explicit(b, Term::Number),
                    ],
                ),
                ret: Box::new(Term::Boolean),
                body,
            },
        )
    }

    fn insert_number_ge(&mut self, sigma: &mut Sigma) {
        let b = Var::new("b");
        let tupled = Var::tupled();
        let untupled_a = Var::new("a");
        let untupled_a_rhs = Var::new("a").untupled_rhs();
        let untupled_b = Var::new("b");
        let body = Body::Fn(Term::TupleLet(
            explicit(untupled_a.clone(), Term::Number),
            explicit(
                untupled_a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLet(
                explicit(untupled_b.clone(), Term::Number),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(untupled_a_rhs)),
                Box::new(Term::NumGe(
                    Box::new(Term::Ref(untupled_a)),
                    Box::new(Term::Ref(untupled_b)),
                )),
            )),
        ));
        self.insert_def(
            sigma,
            Def {
                loc: Default::default(),
                name: Var::new("number#__ge__"),
                tele: tuple_params(
                    tupled,
                    [
                        explicit(Var::new("a"), Term::Number),
                        explicit(b, Term::Number),
                    ],
                ),
                ret: Box::new(Term::Boolean),
                body,
            },
        )
    }

    fn insert_number_lt(&mut self, sigma: &mut Sigma) {
        let b = Var::new("b");
        let tupled = Var::tupled();
        let untupled_a = Var::new("a");
        let untupled_a_rhs = Var::new("a").untupled_rhs();
        let untupled_b = Var::new("b");
        let body = Body::Fn(Term::TupleLet(
            explicit(untupled_a.clone(), Term::Number),
            explicit(
                untupled_a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLet(
                explicit(untupled_b.clone(), Term::Number),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(untupled_a_rhs)),
                Box::new(Term::NumLt(
                    Box::new(Term::Ref(untupled_a)),
                    Box::new(Term::Ref(untupled_b)),
                )),
            )),
        ));
        self.insert_def(
            sigma,
            Def {
                loc: Default::default(),
                name: Var::new("number#__lt__"),
                tele: tuple_params(
                    tupled,
                    [
                        explicit(Var::new("a"), Term::Number),
                        explicit(b, Term::Number),
                    ],
                ),
                ret: Box::new(Term::Boolean),
                body,
            },
        )
    }

    fn insert_number_gt(&mut self, sigma: &mut Sigma) {
        let b = Var::new("b");
        let tupled = Var::tupled();
        let untupled_a = Var::new("a");
        let untupled_a_rhs = Var::new("a").untupled_rhs();
        let untupled_b = Var::new("b");
        let body = Body::Fn(Term::TupleLet(
            explicit(untupled_a.clone(), Term::Number),
            explicit(
                untupled_a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Number), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLet(
                explicit(untupled_b.clone(), Term::Number),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(untupled_a_rhs)),
                Box::new(Term::NumGt(
                    Box::new(Term::Ref(untupled_a)),
                    Box::new(Term::Ref(untupled_b)),
                )),
            )),
        ));
        self.insert_def(
            sigma,
            Def {
                loc: Default::default(),
                name: Var::new("number#__gt__"),
                tele: tuple_params(
                    tupled,
                    [
                        explicit(Var::new("a"), Term::Number),
                        explicit(b, Term::Number),
                    ],
                ),
                ret: Box::new(Term::Boolean),
                body,
            },
        )
    }

    fn insert_boolean_or(&mut self, sigma: &mut Sigma) {
        let b = Var::new("b");
        let tupled = Var::tupled();
        let untupled_a = Var::new("a");
        let untupled_a_rhs = Var::new("a").untupled_rhs();
        let untupled_b = Var::new("b");
        let body = Body::Fn(Term::TupleLet(
            explicit(untupled_a.clone(), Term::Boolean),
            explicit(
                untupled_a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Boolean), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLet(
                explicit(untupled_b.clone(), Term::Boolean),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(untupled_a_rhs)),
                Box::new(Term::BoolOr(
                    Box::new(Term::Ref(untupled_a)),
                    Box::new(Term::Ref(untupled_b)),
                )),
            )),
        ));
        self.insert_def(
            sigma,
            Def {
                loc: Default::default(),
                name: Var::new("boolean#__or__"),
                tele: tuple_params(
                    tupled,
                    [
                        explicit(Var::new("a"), Term::Boolean),
                        explicit(b, Term::Boolean),
                    ],
                ),
                ret: Box::new(Term::Boolean),
                body,
            },
        )
    }

    fn insert_boolean_and(&mut self, sigma: &mut Sigma) {
        let b = Var::new("b");
        let tupled = Var::tupled();
        let untupled_a = Var::new("a");
        let untupled_a_rhs = Var::new("a").untupled_rhs();
        let untupled_b = Var::new("b");
        let body = Body::Fn(Term::TupleLet(
            explicit(untupled_a.clone(), Term::Boolean),
            explicit(
                untupled_a_rhs.clone(),
                Term::Sigma(explicit(b.clone(), Term::Boolean), Box::new(Term::Unit)),
            ),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::TupleLet(
                explicit(untupled_b.clone(), Term::Boolean),
                explicit(Var::unbound(), Term::Unit),
                Box::new(Term::Ref(untupled_a_rhs)),
                Box::new(Term::BoolAnd(
                    Box::new(Term::Ref(untupled_a)),
                    Box::new(Term::Ref(untupled_b)),
                )),
            )),
        ));
        self.insert_def(
            sigma,
            Def {
                loc: Default::default(),
                name: Var::new("boolean#__and__"),
                tele: tuple_params(
                    tupled,
                    [
                        explicit(Var::new("a"), Term::Boolean),
                        explicit(b, Term::Boolean),
                    ],
                ),
                ret: Box::new(Term::Boolean),
                body,
            },
        )
    }

    fn insert_boolean_not(&mut self, sigma: &mut Sigma) {
        let tupled = Var::tupled();
        let untupled_a = Var::new("a");
        let untupled_a_rhs = Var::new("a").untupled_rhs();
        let body = Body::Fn(Term::TupleLet(
            explicit(untupled_a.clone(), Term::Boolean),
            explicit(untupled_a_rhs.clone(), Term::Unit),
            Box::new(Term::Ref(tupled.clone())),
            Box::new(Term::BoolNot(Box::new(Term::Ref(untupled_a)))),
        ));
        self.insert_def(
            sigma,
            Def {
                loc: Default::default(),
                name: Var::new("boolean#__not__"),
                tele: tuple_params(tupled, [explicit(Var::new("a"), Term::Boolean)]),
                ret: Box::new(Term::Boolean),
                body,
            },
        )
    }
}
