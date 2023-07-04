use crate::theory::abs::builtin::Builtins;
use crate::theory::abs::data::{FieldMap, Term};
use crate::theory::{Loc, Param, ParamInfo, Var};
use crate::Error;
use crate::Error::ExpectedReflectable;

const PROP_NAME: &str = "name";
const PROP_KIND: &str = "kind";
const PROP_VALUE: &str = "value";
const PROP_PROPS: &str = "props";
const PROP_VARIANTS: &str = "variants";

pub struct Reflector<'a> {
    builtins: &'a Builtins,
    loc: Loc,
}

impl<'a> Reflector<'a> {
    pub fn new(builtins: &'a Builtins, loc: Loc) -> Self {
        Self { builtins, loc }
    }

    pub fn reflect(&self, ty: Term, has_value: bool) -> Result<Box<Term>, Error> {
        use Term::*;
        Ok(match ty {
            Object(f) => self.reflect_object(*f, has_value)?,
            Enum(f) => self.reflect_enum(*f, has_value)?,

            Unit => self.reflect_simple(Unit),
            Boolean => self.reflect_simple(Boolean),
            String => self.reflect_simple(String),
            Number => self.reflect_simple(Number),
            BigInt => self.reflect_simple(BigInt),

            // TODO: Reflect (higher-)kinded functions.
            a => Box::new(Reflect(Box::new(a))),
        })
    }

    fn rep_kind(&self) -> Term {
        Term::Undef(self.builtins.ubiquitous.get("RepKind").unwrap().1.clone())
    }

    fn reflect_object(&self, fields: Term, has_value: bool) -> Result<Box<Term>, Error> {
        use Term::*;
        let fields = match fields {
            Fields(fields) => fields,
            a => return Err(ExpectedReflectable(a, self.loc)),
        };
        let mut ret = FieldMap::from([(PROP_KIND.to_string(), self.rep_kind())]);
        if has_value {
            ret.insert(
                PROP_VALUE.to_string(),
                Object(Box::new(Fields(fields.clone()))),
            );
        }
        let mut props = FieldMap::new();
        for (name, ty) in fields {
            props.insert(
                name,
                Object(Box::new(Fields(FieldMap::from([
                    (PROP_NAME.to_string(), String),
                    (PROP_KIND.to_string(), *self.reflect_field_type(ty)?),
                ])))),
            );
        }
        ret.insert(PROP_PROPS.to_string(), Object(Box::new(Fields(props))));
        Ok(Box::new(Object(Box::new(Fields(ret)))))
    }

    fn prefix_field(mut name: String, prefix: &str) -> String {
        name.insert_str(name.find('_').map_or(0, |x| x + 1), prefix);
        name
    }

    fn reflect_enum(&self, fields: Term, has_value: bool) -> Result<Box<Term>, Error> {
        use Term::*;
        let fields = match fields {
            Fields(fields) => fields,
            a => return Err(ExpectedReflectable(a, self.loc)),
        };
        let mut ret = FieldMap::from([(PROP_KIND.to_string(), self.rep_kind())]);
        if has_value {
            ret.insert(
                PROP_VALUE.to_string(),
                Enum(Box::new(Fields(fields.clone()))),
            );
        }
        let mut variants = FieldMap::new();
        for (name, ty) in fields {
            variants.insert(
                Self::prefix_field(name, "case"),
                Object(Box::new(Fields(FieldMap::from([
                    (PROP_NAME.to_string(), String),
                    (PROP_KIND.to_string(), *self.reflect_field_type(ty)?),
                ])))),
            );
        }
        ret.insert(
            PROP_VARIANTS.to_string(),
            Object(Box::new(Fields(variants))),
        );
        Ok(Box::new(Object(Box::new(Fields(ret)))))
    }

    fn reflect_field_type(&self, ty: Term) -> Result<Box<Term>, Error> {
        use Term::*;
        Ok(match ty {
            Unit | Boolean | String | Number | BigInt => Box::new(self.rep_kind()),
            a => self.reflect(a, false)?,
        })
    }

    fn reflect_simple(&self, ty: Term) -> Box<Term> {
        use Term::*;
        Box::new(Object(Box::new(Fields(FieldMap::from([
            (PROP_KIND.to_string(), self.rep_kind()),
            (PROP_VALUE.to_string(), ty),
        ])))))
    }

    pub fn generate(&self, ty: Term) -> Box<Term> {
        use Term::*;
        let tupled = Var::tupled();
        let x = Var::new("x");
        Box::new(Lam(
            Param {
                var: tupled.clone(),
                info: ParamInfo::Explicit,
                typ: Box::new(Sigma(
                    Param {
                        var: Var::unbound(),
                        info: ParamInfo::Explicit,
                        typ: Box::new(ty.clone()),
                    },
                    Box::new(Unit),
                )),
            },
            Box::new(TupleLet(
                Param {
                    var: x.clone(),
                    info: ParamInfo::Explicit,
                    typ: Box::new(ty.clone()),
                },
                Param {
                    var: Var::unbound(),
                    info: ParamInfo::Explicit,
                    typ: Box::new(Unit),
                },
                Box::new(Ref(tupled)),
                self.generate_body(Some(x), ty),
            )),
        ))
    }

    fn generate_body(&self, x: Option<Var>, ty: Term) -> Box<Term> {
        use Term::*;
        match ty {
            Object(f) => self.generate_object(x, *f),
            Enum(_f) => todo!(),
            ty => self.generate_simple(x, ty),
        }
    }

    fn generate_object(&self, x: Option<Var>, fields: Term) -> Box<Term> {
        use Term::*;
        let fields = match fields {
            Fields(fields) => fields,
            _ => unreachable!(),
        };
        let mut ret = FieldMap::from([(
            PROP_KIND.to_string(),
            Variant(Box::new(Fields(FieldMap::from([(
                "RepKindObject".to_string(),
                TT,
            )])))),
        )]);
        if let Some(x) = x {
            ret.insert(PROP_VALUE.to_string(), Ref(x));
        }
        let mut props = FieldMap::new();
        for (name, ty) in fields {
            props.insert(
                name.clone(),
                Obj(Box::new(Fields(FieldMap::from([
                    (PROP_NAME.to_string(), Str(name)),
                    (PROP_KIND.to_string(), *self.generate_body(None, ty)),
                ])))),
            );
        }
        ret.insert(PROP_PROPS.to_string(), Obj(Box::new(Fields(props))));
        Box::new(Obj(Box::new(Fields(ret))))
    }

    fn generate_simple(&self, x: Option<Var>, ty: Term) -> Box<Term> {
        use Term::*;
        let k = Variant(Box::new(Fields(FieldMap::from([(
            match ty {
                Unit => "RepKindUnit",
                Boolean => "RepKindBoolean",
                String => "RepKindString",
                Number => "RepKindNumber",
                BigInt => "RepKindBigint",
                _ => unreachable!(),
            }
            .to_string(),
            TT,
        )]))));
        Box::new(match x {
            None => k,
            Some(x) => Obj(Box::new(Fields(FieldMap::from([
                (PROP_KIND.to_string(), k),
                (PROP_VALUE.to_string(), Ref(x)),
            ])))),
        })
    }
}
