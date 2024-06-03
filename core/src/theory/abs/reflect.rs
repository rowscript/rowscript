use crate::theory::abs::data::{FieldMap, Term};
use crate::theory::conc::data::ArgInfo::UnnamedImplicit;
use crate::theory::NameMap;
use crate::theory::{Loc, Param, ParamInfo, Var};
use crate::Error;
use crate::Error::ExpectedReflectable;

const PROP_NAME: &str = "name";
const PROP_KIND: &str = "kind";
const PROP_VALUE: &str = "value";
const PROP_PROPS: &str = "props";
const PROP_VARIANTS: &str = "variants";

pub struct Reflector<'a> {
    ubiquitous: &'a NameMap,
    loc: Loc,
}

impl<'a> Reflector<'a> {
    pub fn new(ubiquitous: &'a NameMap, loc: Loc) -> Self {
        Self { ubiquitous, loc }
    }

    fn rep_kind(&self) -> Term {
        Term::Ref(self.ubiquitous.get("RepKind").unwrap().1.clone())
    }

    fn reflected_app(&self, ty: Term) -> Term {
        use Term::*;
        App(
            Box::new(Ref(self.ubiquitous.get("Reflected").unwrap().1.clone())),
            UnnamedImplicit,
            Box::new(ty),
        )
    }

    fn prefix_field(mut name: String, prefix: &str) -> String {
        name.insert_str(name.find('_').map_or(0, |x| x + 1), prefix);
        name
    }

    pub fn reflected(&self, ty: Term, has_value: bool) -> Result<Box<Term>, Error> {
        use Term::*;
        Ok(match ty {
            Upcast(ty) => self.reflected(*ty, has_value)?,

            Object(f) => self.reflected_object(*f, has_value)?,
            Enum(f) => self.reflected_enum(*f, has_value)?,

            Unit => self.reflected_simple(Unit, has_value),
            Boolean => self.reflected_simple(Boolean, has_value),
            String => self.reflected_simple(String, has_value),
            Number => self.reflected_simple(Number, has_value),
            BigInt => self.reflected_simple(BigInt, has_value),

            a => Box::new(Reflected(Box::new(a))),
        })
    }

    fn reflected_object(&self, fields: Term, has_value: bool) -> Result<Box<Term>, Error> {
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
                    (PROP_KIND.to_string(), *self.reflected(ty, false)?),
                ])))),
            );
        }
        ret.insert(PROP_PROPS.to_string(), Object(Box::new(Fields(props))));
        Ok(Box::new(Object(Box::new(Fields(ret)))))
    }

    fn reflected_enum(&self, fields: Term, has_value: bool) -> Result<Box<Term>, Error> {
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
                    (PROP_KIND.to_string(), *self.reflected(ty, false)?),
                ])))),
            );
        }
        ret.insert(
            PROP_VARIANTS.to_string(),
            Object(Box::new(Fields(variants))),
        );
        Ok(Box::new(Object(Box::new(Fields(ret)))))
    }

    fn reflected_simple(&self, ty: Term, has_value: bool) -> Box<Term> {
        use Term::*;
        let k = self.rep_kind();
        Box::new(match has_value {
            false => k,
            true => Object(Box::new(Fields(FieldMap::from([
                (PROP_KIND.to_string(), k),
                (PROP_VALUE.to_string(), ty),
            ])))),
        })
    }

    pub fn reflect(&self, ty: Term) -> Result<Box<Term>, Error> {
        use Term::*;
        let tupled = Var::tupled();
        let x = Var::new("x");
        Ok(Box::new(Lam(
            Self::tupled_param(tupled.clone(), ty.clone()),
            Default::default(),
            Box::new(TupleBind(
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
                self.reflect_body(Some(x), ty)?,
            )),
        )))
    }

    fn reflect_body(&self, x: Option<Var>, ty: Term) -> Result<Box<Term>, Error> {
        use Term::*;
        match ty {
            Upcast(ty) => self.reflect_body(x, *ty),
            Object(f) => self.reflect_obj(x, *f),
            Enum(f) => self.reflect_variant(x, *f),
            ty => Ok(self.reflect_simple(x, ty)),
        }
    }

    fn reflect_obj(&self, x: Option<Var>, fields: Term) -> Result<Box<Term>, Error> {
        use Term::*;
        let fields = match fields {
            Fields(fields) => fields,
            a => return Err(ExpectedReflectable(a, self.loc)),
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
            props.insert(name.clone(), self.reflect_field_info(name, ty)?);
        }
        ret.insert(PROP_PROPS.to_string(), Obj(Box::new(Fields(props))));
        Ok(Box::new(Obj(Box::new(Fields(ret)))))
    }

    fn reflect_variant(&self, x: Option<Var>, fields: Term) -> Result<Box<Term>, Error> {
        use Term::*;
        let fields = match fields {
            Fields(fields) => fields,
            a => return Err(ExpectedReflectable(a, self.loc)),
        };
        let mut ret = FieldMap::from([(
            PROP_KIND.to_string(),
            Variant(Box::new(Fields(FieldMap::from([(
                "RepKindEnum".to_string(),
                TT,
            )])))),
        )]);
        if let Some(x) = x {
            ret.insert(PROP_VALUE.to_string(), Ref(x));
        }
        let mut variants = FieldMap::new();
        for (name, ty) in fields {
            variants.insert(
                Self::prefix_field(name.clone(), "case"),
                self.reflect_field_info(name, ty)?,
            );
        }
        ret.insert(PROP_VARIANTS.to_string(), Obj(Box::new(Fields(variants))));
        Ok(Box::new(Obj(Box::new(Fields(ret)))))
    }

    fn reflect_field_info(&self, name: String, ty: Term) -> Result<Term, Error> {
        use Term::*;
        Ok(Obj(Box::new(Fields(FieldMap::from([
            (PROP_NAME.to_string(), Str(name)),
            (PROP_KIND.to_string(), *self.reflect_body(None, ty)?),
        ])))))
    }

    fn reflect_simple(&self, x: Option<Var>, ty: Term) -> Box<Term> {
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

    pub fn unreflect(&self, ty: Term) -> Box<Term> {
        use Term::*;
        let ty = self.reflected_app(ty);
        let tupled = Var::tupled();
        let x = Var::new("x");
        Box::new(Lam(
            Self::tupled_param(tupled.clone(), ty.clone()),
            Default::default(),
            Box::new(TupleBind(
                Param {
                    var: x.clone(),
                    info: ParamInfo::Explicit,
                    typ: Box::new(ty),
                },
                Param {
                    var: Var::unbound(),
                    info: ParamInfo::Explicit,
                    typ: Box::new(Unit),
                },
                Box::new(Ref(tupled)),
                Box::new(Access(Box::new(Ref(x)), PROP_VALUE.to_string())),
            )),
        ))
    }

    fn tupled_param(var: Var, ty: Term) -> Param<Term> {
        use Term::*;
        Param {
            var,
            info: ParamInfo::Explicit,
            typ: Box::new(Sigma(
                Param {
                    var: Var::unbound(),
                    info: ParamInfo::Explicit,
                    typ: Box::new(ty),
                },
                Box::new(Unit),
            )),
        }
    }
}
