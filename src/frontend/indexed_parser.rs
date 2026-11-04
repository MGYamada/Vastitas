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
            "presented_affine" => {
                self.expect("(")?;
                let token = self.peek().clone();
                if self.indexed_tag()? != "rational" {
                    return Err(diagnostic(
                        "E_TYPE",
                        "presented affine objects use the rational field",
                        token.span,
                    ));
                }
                self.expect(")")?;
                Ok(indexed::Representation::PresentedAffine {
                    field: indexed::ExactField::Rational,
                })
            }
            "smooth_affine" => Ok(indexed::Representation::SmoothAffine),
            _ => Err(diagnostic(
                "E_TYPE",
                "unsupported concrete object representation",
                token.span,
            )),
        }
    }

    // Keep the ordinary recursive prefix parser's frame small. The existing
    // source-depth limit must diagnose excessive nesting before stack exhaustion.
    // Returns the node kind with its deepest child expression depth.
    #[inline(never)]
    pub(super) fn indexed_pack(&mut self) -> Result<(ExprKind, usize), Diagnostic> {
        self.indexed = true;
        let package = Box::new(self.ty()?);
        self.expect("{")?;
        self.expect("witness")?;
        self.expect(":")?;
        let (witness, mut depth) = self.expression_with_depth(0)?;
        self.expect(",")?;
        self.expect("fields")?;
        self.expect(":")?;
        let fields = self.indexed_list("[", "]", |p| {
            let (field, field_depth) = p.expression_with_depth(0)?;
            depth = depth.max(field_depth);
            Ok(field)
        })?;
        self.consume(",");
        self.expect("}")?;
        let kind = ExprKind::IndexedPack {
            package,
            witness: Box::new(witness),
            fields,
        };
        Ok((kind, depth))
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
        if kind == "canonical" {
            self.expect(")")?;
            return Ok(Constraint::Canonical { object: left });
        }
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
            "structural" => Ok(Constraint::Structural {
                object: left,
                base: right,
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
            "relative_compose" => Primitive::RelativeCompose {
                family: self.type_path()?,
            },
            "relative_equal" => Primitive::RelativeEqual {
                family: self.type_path()?,
            },
            "relative_view" => {
                let family = self.type_path()?;
                self.expect(",")?;
                let source = self.type_path()?;
                self.expect(",")?;
                Primitive::RelativeView {
                    family,
                    source,
                    target: self.type_path()?,
                }
            }
            "relative_coefficient" => {
                let family = self.type_path()?;
                self.expect(",")?;
                let source = self.type_path()?;
                self.expect(",")?;
                let target = self.type_path()?;
                self.expect(",")?;
                let coordinate = self.coordinate_name()?;
                self.expect(",")?;
                Primitive::RelativeCoefficient {
                    family,
                    source,
                    target,
                    coordinate,
                    monomial: self.poly(0)?,
                }
            }
            "relative_pair" => {
                let family = self.type_path()?;
                self.expect(",")?;
                Primitive::RelativePair {
                    family,
                    fiber: self.type_path()?,
                }
            }
            "relative_int_point" => {
                let family = self.type_path()?;
                self.expect(",")?;
                let object = self.type_path()?;
                self.expect(",")?;
                Primitive::RelativeIntPoint {
                    family,
                    object,
                    base: self.type_path()?,
                }
            }
            "smooth_compose" => Primitive::SmoothCompose {
                family: self.type_path()?,
            },
            "smooth_equal" => Primitive::SmoothEqual {
                family: self.type_path()?,
            },
            "smooth_composite" => Primitive::SmoothComposite {
                family: self.type_path()?,
            },
            "smooth_int_point" => {
                let family = self.type_path()?;
                self.expect(",")?;
                let object = self.type_path()?;
                self.expect(",")?;
                Primitive::SmoothIntPoint {
                    family,
                    object,
                    point: self.type_path()?,
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
                    "relative" => indexed::FamilyRepresentation::Relative,
                    "smooth" => indexed::FamilyRepresentation::Smooth,
                    _ => {
                        return Err(diagnostic(
                            "E_TYPE",
                            "family representation requires token, point, morphism, relative or smooth",
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
            "affine" => self.indexed_affine()?,
            "morphism" => self.indexed_morphism()?,
            "iso" => {
                self.expect("=")?;
                self.expect("forward")?;
                let forward = self.type_path()?;
                self.expect("inverse")?;
                DeclarationBody::Iso {
                    forward,
                    inverse: self.type_path()?,
                }
            }
            "cartesian" => {
                self.expect("=")?;
                self.expect("square")?;
                self.expect("(")?;
                let first = self.type_path()?;
                self.expect(",")?;
                let second = self.type_path()?;
                self.expect(")")?;
                self.expect("through")?;
                let fiber = self.type_path()?;
                self.expect("inverse")?;
                DeclarationBody::Cartesian {
                    first,
                    second,
                    fiber,
                    inverse: self.type_path()?,
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

impl Parser {
    /// `(Impl) = spec[g, ...] [relations(p, ...)] [over Base [by(b -> p, ...)]]`,
    /// the smooth object `(Impl) = Affine(n)[c, ...]`, or `(Impl) = Affine(K, n)[g, ...]`,
    /// which is sugar for `spec[g, ...] over K`.
    fn indexed_affine(&mut self) -> Result<DeclarationBody, Diagnostic> {
        self.expect("(")?;
        let implementation = self.type_path()?;
        self.expect(")")?;
        self.expect("=")?;
        if self.peek().is("Affine") {
            return self.indexed_affine_space(implementation);
        }
        if self.consume("localize") {
            self.expect("(")?;
            let object = self.type_path()?;
            self.expect(",")?;
            let element = self.poly(0)?;
            self.expect(")")?;
            self.expect("inverse")?;
            return Ok(DeclarationBody::AffineLocalization {
                implementation,
                object,
                element,
                inverse: self.name()?.0,
            });
        }
        if self.consume("fiber") {
            self.expect("(")?;
            let left = self.type_path()?;
            self.expect(",")?;
            let right = self.type_path()?;
            self.expect(")")?;
            let via = if self.consume("via") {
                let forward = self.indexed_list("(", ")", Self::poly_binding)?;
                self.expect("inverse")?;
                let inverse = self.indexed_list("(", ")", Self::poly_binding)?;
                Some(indexed::FiberVia { forward, inverse })
            } else {
                None
            };
            return Ok(DeclarationBody::AffineFiber {
                implementation,
                left,
                right,
                via,
            });
        }
        self.expect("spec")?;
        let generators = self.indexed_list("[", "]", |p| Ok(p.name()?.0))?;
        let relations = if self.consume("relations") {
            self.indexed_list("(", ")", |p| p.poly(0))?
        } else {
            Vec::new()
        };
        let (base, bindings) = if self.consume("over") {
            let base = self.type_path()?;
            let bindings = if self.consume("by") {
                self.indexed_list("(", ")", Self::poly_binding)?
            } else {
                Vec::new()
            };
            (Some(base), bindings)
        } else {
            (None, Vec::new())
        };
        Ok(DeclarationBody::Affine {
            implementation,
            generators,
            relations,
            base,
            bindings,
        })
    }

    /// `Affine(n)[c, ...]` or `Affine(K, n)[g, ...]` after `=`.
    fn indexed_affine_space(
        &mut self,
        implementation: TypePath,
    ) -> Result<DeclarationBody, Diagnostic> {
        let start = self.expect("Affine")?.span;
        self.expect("(")?;
        let base = if matches!(self.peek().kind, TokenKind::Number(_)) {
            None
        } else {
            let base = self.type_path()?;
            self.expect(",")?;
            Some(base)
        };
        let token = self.advance();
        let dimension = match token.kind {
            TokenKind::Number(value) => value,
            _ => {
                return Err(diagnostic(
                    "E_PARSE",
                    "`Affine` needs a dimension, written as an unsigned integer",
                    token.span,
                ));
            }
        };
        if dimension.len() > crate::limits::MAX_ALGEBRA_DIGITS {
            return Err(diagnostic(
                "E_LIMIT",
                format!(
                    "an `Affine` dimension has at most {} decimal digits",
                    crate::limits::MAX_ALGEBRA_DIGITS
                ),
                token.span,
            ));
        }
        if !dimension
            .parse::<usize>()
            .is_ok_and(|value| value <= crate::limits::MAX_ALGEBRA_GENERATORS)
        {
            return Err(diagnostic(
                "E_LIMIT",
                format!(
                    "`Affine({dimension})` exceeds the limit of {} coordinates",
                    crate::limits::MAX_ALGEBRA_GENERATORS
                ),
                token.span,
            ));
        }
        self.expect(")")?;
        let coordinates = self.indexed_list("[", "]", |p| Ok(p.name()?.0))?;
        let Some(base) = base else {
            return Ok(DeclarationBody::SmoothAffine {
                implementation,
                dimension,
                coordinates,
            });
        };
        // The algebraic spelling has no wire form of its own, so its
        // dimension is checked here.
        if dimension.parse::<usize>().ok() != Some(coordinates.len()) {
            return Err(diagnostic(
                "E_AFFINE_COORDINATE",
                format!(
                    "Affine({}, {dimension}) needs {dimension} coordinates, but {} are given",
                    base.path.join("::"),
                    coordinates.len()
                ),
                start.through(self.previous().span),
            ));
        }
        Ok(DeclarationBody::Affine {
            implementation,
            generators: coordinates,
            relations: Vec::new(),
            base: Some(base),
            bindings: Vec::new(),
        })
    }

    /// `: Family<X, Y, S> = pullback(y -> p, ...) | identity | structure`
    fn indexed_morphism(&mut self) -> Result<DeclarationBody, Diagnostic> {
        self.expect(":")?;
        let family = self.type_path()?;
        self.expect("<")?;
        let mut indices = vec![self.type_path()?];
        while self.consume(",") {
            indices.push(self.type_path()?);
        }
        self.type_close()?;
        self.expect("=")?;
        let span = self.peek().span;
        let definition = match self.indexed_tag()?.as_str() {
            "pullback" => indexed::MorphismDefinition::Pullback {
                images: self.indexed_list("(", ")", Self::poly_binding)?,
            },
            "identity" => indexed::MorphismDefinition::Identity,
            "structure" => indexed::MorphismDefinition::Structure,
            "first" => indexed::MorphismDefinition::First,
            "second" => indexed::MorphismDefinition::Second,
            "restrict" => {
                self.expect("(")?;
                let morphism = self.type_path()?;
                self.expect(")")?;
                indexed::MorphismDefinition::Restrict { morphism }
            }
            _ => {
                return Err(diagnostic(
                    "E_TYPE",
                    "a morphism is a pullback, identity or structure map",
                    span,
                ));
            }
        };
        Ok(DeclarationBody::Morphism {
            family,
            indices,
            definition,
        })
    }

    fn poly_nesting(&self, depth: usize) -> Result<(), Diagnostic> {
        if depth >= crate::limits::MAX_ALGEBRA_NESTING {
            Err(diagnostic(
                "E_LIMIT",
                "polynomial expression is nested too deeply",
                self.peek().span,
            ))
        } else {
            Ok(())
        }
    }

    /// Sums and differences of terms. Kept n-ary on the wire.
    fn poly(&mut self, depth: usize) -> Result<indexed::PolyExpr, Diagnostic> {
        self.poly_nesting(depth)?;
        let mut terms = vec![self.poly_term(depth)?];
        loop {
            if self.consume("+") {
                terms.push(self.poly_term(depth)?);
            } else if self.consume("-") {
                terms.push(indexed::PolyExpr::Neg {
                    operand: Box::new(self.poly_term(depth)?),
                });
            } else {
                break;
            }
        }
        Ok(if terms.len() == 1 {
            terms.pop().unwrap()
        } else {
            indexed::PolyExpr::Sum { terms }
        })
    }

    fn poly_term(&mut self, depth: usize) -> Result<indexed::PolyExpr, Diagnostic> {
        let mut factors = vec![self.poly_unary(depth)?];
        while self.consume("*") {
            factors.push(self.poly_unary(depth)?);
        }
        Ok(if factors.len() == 1 {
            factors.pop().unwrap()
        } else {
            indexed::PolyExpr::Product { factors }
        })
    }

    fn poly_unary(&mut self, depth: usize) -> Result<indexed::PolyExpr, Diagnostic> {
        if self.consume("-") {
            self.poly_nesting(depth + 1)?;
            return Ok(indexed::PolyExpr::Neg {
                operand: Box::new(self.poly_unary(depth + 1)?),
            });
        }
        let base = self.poly_atom(depth)?;
        if self.consume("^") {
            let exponent = self.poly_literal()?;
            return Ok(indexed::PolyExpr::Pow {
                base: Box::new(base),
                exponent,
            });
        }
        Ok(base)
    }

    fn poly_literal(&mut self) -> Result<String, Diagnostic> {
        let token = self.advance();
        match token.kind {
            TokenKind::Number(value) if value.len() <= crate::limits::MAX_ALGEBRA_DIGITS => {
                Ok(value)
            }
            TokenKind::Number(_) => Err(diagnostic(
                "E_LIMIT",
                format!(
                    "polynomial literals have at most {} decimal digits",
                    crate::limits::MAX_ALGEBRA_DIGITS
                ),
                token.span,
            )),
            _ => Err(diagnostic(
                "E_PARSE",
                "expected an unsigned decimal literal",
                token.span,
            )),
        }
    }

    fn poly_atom(&mut self, depth: usize) -> Result<indexed::PolyExpr, Diagnostic> {
        if matches!(self.peek().kind, TokenKind::Number(_)) {
            return Ok(indexed::PolyExpr::Natural {
                value: self.poly_literal()?,
            });
        }
        if self.consume("(") {
            let inner = self.poly(depth + 1)?;
            self.expect(")")?;
            return Ok(inner);
        }
        if self.peek().is("frac") {
            self.advance();
            self.expect("(")?;
            let negative = self.consume("-");
            let numerator = self.poly_literal()?;
            self.expect(",")?;
            let denominator = self.poly_literal()?;
            self.expect(")")?;
            return Ok(indexed::PolyExpr::Fraction {
                numerator: if negative {
                    format!("-{numerator}")
                } else {
                    numerator
                },
                denominator,
            });
        }
        Ok(indexed::PolyExpr::Coordinate {
            name: self.coordinate_name()?,
        })
    }

    /// A coordinate, qualified by its fiber factors: `x`, `X::x`, or
    /// `Fiber::X::x` for a fiber product that is itself a factor.
    fn coordinate_name(&mut self) -> Result<String, Diagnostic> {
        let (mut name, _) = self.name()?;
        while self.consume("::") {
            name = format!("{name}::{}", self.name()?.0);
        }
        Ok(name)
    }

    /// `name -> polynomial`, where the name may be qualified.
    fn poly_binding(&mut self) -> Result<indexed::Binding, Diagnostic> {
        let name = self.coordinate_name()?;
        self.expect("->")?;
        Ok(indexed::Binding {
            name,
            image: self.poly(0)?,
        })
    }
}
