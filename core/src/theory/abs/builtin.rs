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
}

impl Builtins {
    pub fn new(sigma: &mut Sigma) -> Self {
        let mut ret = Self {
            ubiquitous: NameMap::default(),
            unionify: Var::new("unionify"),
            reflect: Var::new("Reflected"),
            number_add: Var::new("number#__add__"),
            number_sub: Var::new("number#__sub__"),
        };
        ret.insert_unionify(sigma);
        ret.insert_reflect(sigma);
        ret.insert_number_add(sigma);
        ret.insert_number_sub(sigma);
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
}
