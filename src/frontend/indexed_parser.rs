use super::*;
use crate::indexed::{
    self, BoundApplication, BoundIndex, Constraint, DeclarationBody, ObjectType, PackageShape,
    Primitive,
};

impl Parser {
    fn indexed_coefficient(&mut self) -> Result<indexed::CoefficientKind, Diagnostic> {
        let token = self.peek().clone();
        match self.indexed_tag()?.as_str() {
            "real" => Ok(indexed::CoefficientKind::Real),
            "complex" => Ok(indexed::CoefficientKind::Complex),
            _ => Err(diagnostic(
                "E_TYPE",
                "expected ideal coefficient kind real or complex",
                token.span,
            )),
        }
    }

    fn indexed_representation(&mut self) -> Result<indexed::Representation, Diagnostic> {
        let token = self.peek().clone();
        match self.indexed_tag()?.as_str() {
            "affine_descriptor" => Ok(indexed::Representation::AffineDescriptor),
            "scalar_base" => {
                self.expect("(")?;
                let token = self.peek().clone();
                let setting = match self.indexed_tag()?.as_str() {
                    "scheme" => indexed::GeometricSetting::Scheme,
                    "smooth" => indexed::GeometricSetting::Smooth,
                    _ => {
                        return Err(diagnostic(
                            "E_TYPE",
                            "expected scheme or smooth setting",
                            token.span,
                        ));
                    }
                };
                self.expect(",")?;
                let coefficient = self.indexed_coefficient()?;
                self.expect(")")?;
                Ok(indexed::Representation::ScalarBase {
                    setting,
                    coefficient,
                })
            }
            "linear_descriptor" => {
                self.expect("(")?;
                let base = self.type_path()?;
                self.expect(",")?;
                let coefficient = self.indexed_coefficient()?;
                self.expect(")")?;
                Ok(indexed::Representation::LinearDescriptor { base, coefficient })
            }
            _ => Err(diagnostic(
                "E_TYPE",
                "unsupported concrete object representation",
                token.span,
            )),
        }
    }

    // Keep the ordinary recursive prefix parser's frame small. The existing
    // source-depth limit must diagnose excessive nesting before stack exhaustion.
    pub(super) fn indexed_pack(&mut self) -> Result<ExprKind, Diagnostic> {
        self.indexed = true;
        let package = Box::new(self.ty()?);
        self.expect("{")?;
        self.expect("witness")?;
        self.expect(":")?;
        let witness = Box::new(self.expression(0)?);
        self.expect(",")?;
        self.expect("fields")?;
        self.expect(":")?;
        let fields = self.indexed_list("[", "]", |p| p.expression(0))?;
        self.consume(",");
        self.expect("}")?;
        Ok(ExprKind::IndexedPack {
            package,
            witness,
            fields,
        })
    }

    pub(super) fn indexed_list<T>(
        &mut self,
        open: &str,
        close: &str,
        mut item: impl FnMut(&mut Self) -> Result<T, Diagnostic>,
    ) -> Result<Vec<T>, Diagnostic> {
        self.expect(open)?;
        let mut values = Vec::new();
        if !self.consume(close) {
            loop {
                values.push(item(self)?);
                if self.consume(close) {
                    break;
                }
                self.expect(",")?;
                if self.consume(close) {
                    break;
                }
            }
        }
        Ok(values)
    }

    fn indexed_tag(&mut self) -> Result<String, Diagnostic> {
        let token = self.advance();
        match token.kind {
            TokenKind::Name(name) => Ok(name),
            _ => Err(diagnostic(
                "E_PARSE",
                "expected an indexed contract kind",
                token.span,
            )),
        }
    }

    fn indexed_object_type(&mut self) -> Result<ObjectType, Diagnostic> {
        self.expect("(")?;
        let domain = self.type_path()?;
        self.expect(",")?;
        let marker = self.type_path()?;
        self.expect(")")?;
        Ok(ObjectType { domain, marker })
    }

    fn indexed_parameter(&mut self) -> Result<indexed::Parameter, Diagnostic> {
        let span = self.peek().span;
        match self.indexed_tag()?.as_str() {
            "domain" => Ok(indexed::Parameter::Domain),
            "marker" => Ok(indexed::Parameter::Marker),
            "natural" => Ok(indexed::Parameter::Natural),
            "object" => {
                self.expect("(")?;
                let domain = self.type_path()?;
                self.expect(")")?;
                Ok(indexed::Parameter::Object { domain })
            }
            _ => Err(diagnostic(
                "E_TYPE",
                "index parameters use domain, marker, natural, or object(Classification)",
                span,
            )),
        }
    }

    fn indexed_slot(&mut self) -> Result<u32, Diagnostic> {
        let token = self.advance();
        match token.kind {
            TokenKind::Number(value) => value.parse().map_err(|_| {
                diagnostic(
                    "E_LIMIT",
                    "constraint slot exceeds the supported range",
                    token.span,
                )
            }),
            _ => Err(diagnostic(
                "E_PARSE",
                "constraint slot requires an unsigned integer",
                token.span,
            )),
        }
    }

    fn indexed_constraint(&mut self) -> Result<Constraint, Diagnostic> {
        let span = self.peek().span;
        let kind = self.indexed_tag()?;
        self.expect("(")?;
        let left = self.indexed_slot()?;
        self.expect(",")?;
        let right = self.indexed_slot()?;
        self.expect(")")?;
        match kind.as_str() {
            "same_object" => Ok(Constraint::SameObject { left, right }),
            "same_base" => Ok(Constraint::SameBase { left, right }),
            "over" => Ok(Constraint::Over {
                object: left,
                marker: right,
            }),
            _ => Err(diagnostic("E_TYPE", "unknown indexed constraint", span)),
        }
    }

    fn indexed_bound(&mut self) -> Result<BoundIndex, Diagnostic> {
        if let TokenKind::Number(value) = self.peek().kind.clone() {
            self.advance();
            return Ok(BoundIndex::Natural { value });
        }
        let span = self.peek().span;
        let kind = self.indexed_tag()?;
        if kind == "witness" {
            return Ok(BoundIndex::Witness);
        }
        self.expect("(")?;
        let declaration = self.type_path()?;
        self.expect(")")?;
        match kind.as_str() {
            "global" => Ok(BoundIndex::Global { declaration }),
            "domain" => Ok(BoundIndex::Domain { declaration }),
            "marker" => Ok(BoundIndex::Marker { declaration }),
            _ => Err(diagnostic(
                "E_TYPE",
                "package indices use witness, global(...), domain(...), marker(...), or a natural literal",
                span,
            )),
        }
    }

    fn indexed_case(&mut self) -> Result<PackageShape, Diagnostic> {
        self.expect("case")?;
        let witness_type = self.indexed_object_type()?;
        self.expect("{")?;
        let mut fields = Vec::new();
        while !self.consume("}") {
            let family = self.type_path()?;
            let indices = self.indexed_list("(", ")", Self::indexed_bound)?;
            self.expect(";")?;
            fields.push(BoundApplication { family, indices });
        }
        Ok(PackageShape {
            witness_type,
            fields,
        })
    }

    fn indexed_primitive(&mut self) -> Result<Primitive, Diagnostic> {
        let span = self.peek().span;
        let op = self.indexed_tag()?;
        self.expect("(")?;
        let binding = match op.as_str() {
            "descriptor" => Primitive::Descriptor {
                implementation: self.type_path()?,
            },
            "global" => Primitive::Global {
                declaration: self.type_path()?,
            },
            "origin" => {
                let domain = self.indexed_object_type()?;
                self.expect(",")?;
                let point_family = self.type_path()?;
                self.expect(",")?;
                Primitive::Origin {
                    domain,
                    point_family,
                    base_object: self.type_path()?,
                }
            }
            "identity" => {
                let domain = self.indexed_object_type()?;
                self.expect(",")?;
                Primitive::Identity {
                    domain,
                    map_family: self.type_path()?,
                }
            }
            "dimension" => Primitive::Dimension {
                domain: self.indexed_object_type()?,
            },
            "compose" => Primitive::Compose {
                map_family: self.type_path()?,
            },
            "apply" => {
                let map_family = self.type_path()?;
                self.expect(",")?;
                Primitive::Apply {
                    map_family,
                    point_family: self.type_path()?,
                }
            }
            _ => {
                return Err(diagnostic(
                    "E_TYPE",
                    "unknown indexed primitive contract",
                    span,
                ));
            }
        };
        self.expect(")")?;
        Ok(binding)
    }

    pub(super) fn indexed_declaration(&mut self) -> Result<indexed::Declaration, Diagnostic> {
        self.indexed = true;
        let start = self.expect("indexed")?.span;
        let kind = self.indexed_tag()?;
        let (name, name_span) = self.name()?;
        if name.starts_with("__vastitas_") {
            return Err(diagnostic(
                "E_RESERVED",
                "the `__vastitas_` prefix is reserved",
                name_span,
            ));
        }
        let body = match kind.as_str() {
            "marker" => DeclarationBody::Marker,
            "implementation" => {
                self.expect("(")?;
                let marker = self.type_path()?;
                self.expect(",")?;
                let representation = self.indexed_representation()?;
                self.expect(")")?;
                self.expect("capabilities")?;
                let capabilities = self.indexed_list("(", ")", |parser| {
                    let token = parser.peek().clone();
                    match parser.indexed_tag()?.as_str() {
                        "origin" => Ok(indexed::Capability::Origin),
                        "dimension" => Ok(indexed::Capability::Dimension),
                        _ => Err(diagnostic(
                            "E_TYPE",
                            "unsupported implementation capability",
                            token.span,
                        )),
                    }
                })?;
                DeclarationBody::Implementation {
                    marker,
                    representation,
                    capabilities,
                }
            }
            "classification" => {
                self.expect("{")?;
                self.expect("parents")?;
                let parents = self.indexed_list("(", ")", Self::type_path)?;
                self.expect(";")?;
                self.expect("domain")?;
                let domain = self.indexed_list("(", ")", Self::type_path)?;
                self.expect(";")?;
                self.expect("}")?;
                DeclarationBody::Classification { parents, domain }
            }
            "global" => {
                self.expect("(")?;
                let implementation = self.type_path()?;
                self.expect(")")?;
                DeclarationBody::Global { implementation }
            }
            "family" => {
                let parameters = self.indexed_list("(", ")", Self::indexed_parameter)?;
                self.expect("=")?;
                let span = self.peek().span;
                let representation = match self.indexed_tag()?.as_str() {
                    "token" => indexed::FamilyRepresentation::Token,
                    "point" => indexed::FamilyRepresentation::Point,
                    "morphism" => indexed::FamilyRepresentation::Morphism,
                    _ => {
                        return Err(diagnostic(
                            "E_TYPE",
                            "family representation requires token, point, or morphism",
                            span,
                        ));
                    }
                };
                self.expect("constraints")?;
                let constraints = self.indexed_list("(", ")", Self::indexed_constraint)?;
                DeclarationBody::Family {
                    parameters,
                    constraints,
                    representation,
                }
            }
            "package" => {
                self.expect("{")?;
                let mut cases = Vec::new();
                while !self.consume("}") {
                    cases.push(self.indexed_case()?);
                }
                DeclarationBody::Package { cases }
            }
            "primitive" => {
                self.expect("=")?;
                DeclarationBody::Primitive {
                    binding: self.indexed_primitive()?,
                }
            }
            _ => {
                return Err(diagnostic(
                    "E_TYPE",
                    "unknown indexed declaration kind",
                    start,
                ));
            }
        };
        let end = self.expect(";")?.span;
        Ok(indexed::Declaration {
            name,
            body,
            span: start.through(end),
        })
    }

    pub(super) fn indexed_type(&mut self, first: String, start: Span) -> Result<Type, Diagnostic> {
        self.indexed = true;
        let mut parts = vec![first];
        while self.consume("::") {
            parts.push(self.path_component()?.0);
        }
        let family = TypePath {
            path: parts,
            span: start.through(self.previous().span),
        };
        self.expect("<")?;
        if family.path == ["Object"] {
            let domain = self.type_path()?;
            self.expect(",")?;
            let marker = self.type_path()?;
            self.type_close()?;
            return Ok(Type::IndexedObject {
                domain: Box::new(domain),
                marker: Box::new(marker),
            });
        }
        let mut arguments = Vec::new();
        if !self.peek().is(">") && !self.peek().is(">=") {
            loop {
                if let TokenKind::Number(value) = self.peek().kind.clone() {
                    self.advance();
                    arguments.push(indexed::Argument::Natural { value });
                } else {
                    arguments.push(indexed::Argument::Name {
                        reference: self.type_path()?,
                    });
                }
                if !self.consume(",") || self.peek().is(">") || self.peek().is(">=") {
                    break;
                }
            }
        }
        self.type_close()?;
        Ok(Type::IndexedApply {
            family: Box::new(family),
            arguments,
        })
    }
}
