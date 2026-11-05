use super::*;
use crate::indexed::{
    self, BoundApplication, BoundIndex, Constraint, DeclarationBody, ObjectType, PackageShape,
    Primitive, WireValue,
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

    /// Paths separated by commas, one per field.
    fn indexed_paths(
        &mut self,
        fields: &[&'static str],
    ) -> Result<Vec<(&'static str, WireValue)>, Diagnostic> {
        let mut values = Vec::with_capacity(fields.len());
        for (index, &field) in fields.iter().enumerate() {
            if index > 0 {
                self.expect(",")?;
            }
            values.push((field, WireValue::Path(self.type_path()?)));
        }
        Ok(values)
    }

    /// One arm per surface form. An op that the generated table
    /// (`src/primitive_table.rs`) does not have is the unknown-contract
    /// diagnostic before any argument is parsed, so an arm for such an op is
    /// unreachable. Each arm names the wire fields of its op, and
    /// `Primitive::new` admits them only if they are the table's fields, in
    /// its order and with its kinds. The unit tests check that every table op
    /// has an arm whose fields, order and kinds equal the table's, and that
    /// an op outside the table is unknown; no test notices an unreachable
    /// arm for an op outside the table.
    fn indexed_primitive(&mut self) -> Result<Primitive, Diagnostic> {
        let span = self.peek().span;
        let op = self.indexed_tag()?;
        self.expect("(")?;
        let unknown = || diagnostic("E_TYPE", "unknown indexed primitive contract", span);
        let Some(family) = indexed::primitive_family(&op) else {
            return Err(unknown());
        };
        let fields = match family.op {
            "descriptor" => self.indexed_paths(&["implementation"])?,
            "global" => self.indexed_paths(&["declaration"])?,
            "origin" => {
                let domain = self.indexed_object_type()?;
                self.expect(",")?;
                let mut fields = vec![("domain", WireValue::ObjectType(domain))];
                fields.extend(self.indexed_paths(&["point_family", "base_object"])?);
                fields
            }
            "identity" => {
                let domain = self.indexed_object_type()?;
                self.expect(",")?;
                let mut fields = vec![("domain", WireValue::ObjectType(domain))];
                fields.extend(self.indexed_paths(&["map_family"])?);
                fields
            }
            "dimension" => vec![("domain", WireValue::ObjectType(self.indexed_object_type()?))],
            "compose" => self.indexed_paths(&["map_family"])?,
            "apply" => self.indexed_paths(&["map_family", "point_family"])?,
            "relative_compose" | "relative_equal" => self.indexed_paths(&["family"])?,
            "relative_view" => self.indexed_paths(&["family", "source", "target"])?,
            "relative_coefficient" => {
                let mut fields = self.indexed_paths(&["family", "source", "target"])?;
                self.expect(",")?;
                fields.push(("coordinate", WireValue::Coordinate(self.coordinate_name()?)));
                self.expect(",")?;
                fields.push(("monomial", WireValue::Polynomial(self.poly(0)?)));
                fields
            }
            "relative_pair" => self.indexed_paths(&["family", "fiber"])?,
            "relative_int_point" => self.indexed_paths(&["family", "object", "base"])?,
            "smooth_compose" | "smooth_equal" | "smooth_composite" => {
                self.indexed_paths(&["family"])?
            }
            "smooth_int_point" => self.indexed_paths(&["family", "object", "point"])?,
            "fiber_vector" => self.indexed_paths(&["family", "map_family", "object"])?,
            "fiber_at" => self.indexed_paths(&["family", "map_family"])?,
            "fiber_equal" => self.indexed_paths(&["family"])?,
            "fiber_component" => {
                let mut fields = self.indexed_paths(&["family", "object"])?;
                self.expect(",")?;
                fields.push(("coordinate", WireValue::Coordinate(self.coordinate_name()?)));
                fields
            }
            "fiber_pairing" => self.indexed_paths(&["cotangent", "tangent"])?,
            "cotangent_pullback" => {
                let mut fields = self.indexed_paths(&["map_family", "cotangent"])?;
                self.expect(",")?;
                let token = self.peek().clone();
                let mode = match self.indexed_tag()?.as_str() {
                    "saved" => indexed::PullbackMode::Saved,
                    "recomputed" => indexed::PullbackMode::Recomputed,
                    _ => {
                        return Err(diagnostic(
                            "E_TYPE",
                            "a cotangent pullback mode is saved or recomputed",
                            token.span,
                        ));
                    }
                };
                fields.push(("mode", WireValue::PullbackMode(mode)));
                fields
            }
            "differential" => self.indexed_paths(&["map_family", "cotangent", "line"])?,
            "linearize" => self.indexed_paths(&["map_family", "tape"])?,
            "cotangent_backward" => self.indexed_paths(&["tape", "cotangent"])?,
            "flat" => {
                let mut fields = self.indexed_paths(&["tangent", "cotangent"])?;
                let metric = self.indexed_selection("flat", "using", "an explicit metric")?;
                fields.push(("metric", WireValue::Path(metric)));
                fields
            }
            "sharp" => {
                let mut fields = self.indexed_paths(&["cotangent", "tangent"])?;
                let metric = self.indexed_selection("sharp", "using", "an explicit metric")?;
                fields.push(("metric", WireValue::Path(metric)));
                let evidence =
                    self.indexed_selection("sharp", "evidence", "explicit nondegeneracy evidence")?;
                fields.push(("evidence", WireValue::Path(evidence)));
                fields
            }
            // A table op without a surface arm; the per-entry test fails.
            _ => return Err(unknown()),
        };
        // Fields that differ from the table's; the per-entry test fails.
        let binding = Primitive::new(family.op, fields).map_err(|_| unknown())?;
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
                    "cotangent" => indexed::FamilyRepresentation::Cotangent,
                    "tangent" => indexed::FamilyRepresentation::Tangent,
                    "tape" => indexed::FamilyRepresentation::Tape,
                    "metric_form" => indexed::FamilyRepresentation::MetricForm,
                    _ => {
                        return Err(diagnostic(
                            "E_TYPE",
                            "family representation requires token, point, morphism, relative, smooth, cotangent, tangent, tape or metric_form",
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
            "metric" => self.indexed_metric()?,
            "evidence" => {
                self.expect("=")?;
                let span = self.peek().span;
                let evidence = match self.indexed_tag()?.as_str() {
                    "nondegenerate" => indexed::EvidenceKind::Nondegenerate,
                    "riemannian" => indexed::EvidenceKind::Riemannian,
                    _ => {
                        return Err(diagnostic(
                            "E_TYPE",
                            "evidence is nondegenerate(metric) or riemannian(metric)",
                            span,
                        ));
                    }
                };
                self.expect("(")?;
                let metric = self.type_path()?;
                self.expect(")")?;
                DeclarationBody::Evidence { metric, evidence }
            }
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

    /// `: Family<X> = euclidean` or `: Family<X> = gram((a, b), (c, d))`.
    fn indexed_metric(&mut self) -> Result<DeclarationBody, Diagnostic> {
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
        let gram = match self.indexed_tag()?.as_str() {
            "euclidean" => indexed::MetricGram::Euclidean,
            "gram" => indexed::MetricGram::Gram {
                rows: self.indexed_list("(", ")", |p| p.indexed_list("(", ")", |q| q.poly(0)))?,
            },
            _ => {
                return Err(diagnostic(
                    "E_TYPE",
                    "a metric is `euclidean` or `gram((…), …)` with one row per coordinate",
                    span,
                ));
            }
        };
        Ok(DeclarationBody::Metric {
            family,
            indices,
            gram,
        })
    }

    /// `, keyword = path`: the metric or evidence that `flat` and `sharp`
    /// name explicitly. No default is ever selected.
    fn indexed_selection(
        &mut self,
        operation: &str,
        keyword: &str,
        what: &str,
    ) -> Result<TypePath, Diagnostic> {
        let token = self.peek().clone();
        if !(self.consume(",") && self.consume(keyword)) {
            return Err(diagnostic(
                "E_PARSE",
                format!("`{operation}` needs {what}: write `{keyword} = …`"),
                token.span,
            ));
        }
        self.expect("=")?;
        self.type_path()
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
        // `frac(` starts a fraction literal; any other `frac` is a coordinate,
        // as in `frac^2` or `frac::t`.
        if self.peek().is("frac")
            && self
                .tokens
                .get(self.position + 1)
                .is_some_and(|next| next.is("("))
        {
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

#[cfg(test)]
mod tests {
    use super::*;

    /// One surface form per family of the generated table, in table order.
    const SNIPPETS: &[(&str, &str)] = &[
        ("descriptor", "descriptor(AffineQQ)"),
        ("global", "global(SpecQQ)"),
        ("origin", "origin((Scheme, QQ), Point, Base)"),
        ("identity", "identity((Scheme, QQ), Morphism)"),
        ("dimension", "dimension((Scheme, QQ))"),
        ("compose", "compose(Morphism)"),
        ("apply", "apply(Morphism, Point)"),
        ("relative_compose", "relative_compose(Over)"),
        ("relative_equal", "relative_equal(Over)"),
        ("relative_view", "relative_view(Over, S, SpecQQ)"),
        (
            "relative_coefficient",
            "relative_coefficient(Over, D, Line, Fiber::X::x, e^2 + 1)",
        ),
        (
            "relative_int_point",
            "relative_int_point(Over, Line, SpecQQ)",
        ),
        ("relative_pair", "relative_pair(Over, Fiber)"),
        ("smooth_compose", "smooth_compose(Smooth)"),
        ("smooth_equal", "smooth_equal(Smooth)"),
        ("smooth_composite", "smooth_composite(Smooth)"),
        ("smooth_int_point", "smooth_int_point(Smooth, Plane, Pt)"),
        ("fiber_vector", "fiber_vector(Cotangent, Smooth, Line)"),
        ("fiber_at", "fiber_at(Cotangent, Smooth)"),
        ("fiber_equal", "fiber_equal(Cotangent)"),
        ("fiber_component", "fiber_component(Cotangent, Line, t)"),
        ("fiber_pairing", "fiber_pairing(Cotangent, Tangent)"),
        (
            "cotangent_pullback",
            "cotangent_pullback(Smooth, Cotangent, recomputed)",
        ),
        ("differential", "differential(Smooth, Cotangent, Line)"),
        ("linearize", "linearize(Smooth, Tape)"),
        ("cotangent_backward", "cotangent_backward(Tape, Cotangent)"),
        ("flat", "flat(Tangent, Cotangent, using = Skew)"),
        (
            "sharp",
            "sharp(Cotangent, Tangent, using = Skew, evidence = SkewInvertible)",
        ),
    ];

    fn parse_binding(source: &str) -> Result<Primitive, Diagnostic> {
        let parsed = parse_module_source(
            SourceInput {
                source,
                file: "primitive.vast",
                offset: 0,
            },
            vec![],
            true,
            None,
        )?;
        let [module] = &parsed.modules[..] else {
            panic!("one module expected");
        };
        let [declaration] = &module.indexed_declarations[..] else {
            panic!("one declaration expected");
        };
        match &declaration.declaration.body {
            DeclarationBody::Primitive { binding } => Ok(binding.clone()),
            body => panic!("primitive expected, got {body:?}"),
        }
    }

    /// Every family of the table has a surface form, and each form parses
    /// to a binding with exactly the family's fields, which serializes as
    /// `{"op": …}` followed by those fields in table order.
    #[test]
    fn every_table_entry_parses_to_its_wire_fields() {
        let table: Vec<&str> = indexed::primitive_families()
            .iter()
            .map(|family| family.op)
            .collect();
        let snippets: Vec<&str> = SNIPPETS.iter().map(|(op, _)| *op).collect();
        assert_eq!(
            snippets, table,
            "one snippet per table entry, in table order"
        );
        for (family, (_, snippet)) in indexed::primitive_families().iter().zip(SNIPPETS) {
            let source = format!("indexed primitive p = {snippet};");
            let binding = parse_binding(&source)
                .unwrap_or_else(|error| panic!("`{snippet}` does not parse: {error:?}"));
            assert_eq!(binding.op(), family.op);
            let fields: Vec<(&str, indexed::WireKind)> = binding
                .fields()
                .map(|(name, value)| (name, value.kind()))
                .collect();
            assert_eq!(fields, family.fields, "{snippet}");
            let mut expected = format!("{{\"op\":\"{}\"", family.op);
            for (name, value) in binding.fields() {
                expected.push_str(&format!(
                    ",\"{name}\":{}",
                    serde_json::to_string(value).unwrap()
                ));
            }
            expected.push('}');
            assert_eq!(serde_json::to_string(&binding).unwrap(), expected);
        }
    }

    #[test]
    fn an_op_outside_the_table_is_unknown() {
        let error = parse_binding("indexed primitive p = gradient(Smooth, Cotangent);")
            .expect_err("`gradient` is not a primitive");
        assert_eq!(error.code, "E_TYPE");
        assert_eq!(error.message, "unknown indexed primitive contract");
    }
}
