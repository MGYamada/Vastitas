use super::*;
use crate::indexed::{
    self, BoundApplication, BoundIndex, Constraint, DeclarationBody, ObjectType, PackageShape,
    Primitive, WireValue,
};

/// The frame that `frame_encode`, `frame_decode` and `frame_vector` embed,
/// with what its missing keyword's diagnostic says is needed.
const FRAME: &[(&str, &str)] = &[("frame", "an explicit frame")];

/// The source and target frames of `frame_matrix` and `frame_transition`.
const ENDPOINTS: &[(&str, &str)] = &[
    ("source", "an explicit source frame"),
    ("target", "an explicit target frame"),
];

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
            "frame" => {
                self.expect("(")?;
                let family = self.type_path()?;
                self.expect(")")?;
                Ok(indexed::Parameter::Frame { family })
            }
            _ => Err(diagnostic(
                "E_TYPE",
                "index parameters use domain, marker, natural, object(Classification), or frame(Family)",
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

    /// The paths `fields`, then each frame of `frames` as `, keyword = path`
    /// (`indexed_selection`), in wire order. Each keyword is the name of its
    /// wire field. A missing keyword is `E_PARSE` naming it; no frame is
    /// ever chosen by default.
    fn indexed_framed(
        &mut self,
        op: &str,
        fields: &[&'static str],
        frames: &[(&'static str, &str)],
    ) -> Result<Vec<(&'static str, WireValue)>, Diagnostic> {
        let mut values = self.indexed_paths(fields)?;
        for &(keyword, what) in frames {
            let frame = self.indexed_selection(op, keyword, what)?;
            values.push((keyword, WireValue::Path(frame)));
        }
        Ok(values)
    }

    /// `, n`: the natural field `field` of `op`, an unsigned decimal literal
    /// with at most as many digits as the kernel's decoder admits
    /// (`algebraCoefficientDigits`), as for polynomial literals. The digits
    /// go to the wire as written.
    fn indexed_natural(
        &mut self,
        op: &str,
        field: &'static str,
    ) -> Result<(&'static str, WireValue), Diagnostic> {
        self.expect(",")?;
        let token = self.advance();
        match token.kind {
            TokenKind::Number(digits) if digits.len() <= crate::limits::MAX_ALGEBRA_DIGITS => {
                Ok((field, WireValue::Natural(digits)))
            }
            TokenKind::Number(_) => Err(diagnostic(
                "E_LIMIT",
                format!(
                    "the {field} of `{op}` has at most {} decimal digits",
                    crate::limits::MAX_ALGEBRA_DIGITS
                ),
                token.span,
            )),
            _ => Err(diagnostic(
                "E_PARSE",
                format!(
                    "the {field} of `{op}` is a natural literal, written as an unsigned integer"
                ),
                token.span,
            )),
        }
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
                fields.push(("monomial", WireValue::Polynomial(self.polynomial()?)));
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
            // Stage 4 (#759): the frames that a frame primitive embeds are
            // named explicitly, `frame =`, or `source =` and `target =`.
            "frame_encode" => self.indexed_framed("frame_encode", &["fiber", "coords"], FRAME)?,
            "frame_decode" => self.indexed_framed("frame_decode", &["coords", "fiber"], FRAME)?,
            "frame_vector" => {
                self.indexed_framed("frame_vector", &["coords", "map_family"], FRAME)?
            }
            "frame_matrix" => {
                self.indexed_framed("frame_matrix", &["map_family", "frame_map"], ENDPOINTS)?
            }
            "frame_transition" => {
                self.indexed_framed("frame_transition", &["map_family", "frame_map"], ENDPOINTS)?
            }
            "frame_apply" => self.indexed_paths(&["frame_map", "coords"])?,
            "frame_coapply" => self.indexed_paths(&["frame_map", "cocoords"])?,
            "frame_compose" => self.indexed_paths(&["frame_map"])?,
            "frame_pairing" => self.indexed_paths(&["cocoords", "coords"])?,
            "frame_component" => {
                let mut fields = self.indexed_paths(&["family"])?;
                fields.push(self.indexed_natural("frame_component", "index")?);
                fields
            }
            "frame_entry" => {
                let mut fields = self.indexed_paths(&["frame_map"])?;
                fields.push(self.indexed_natural("frame_entry", "row")?);
                fields.push(self.indexed_natural("frame_entry", "column")?);
                fields
            }
            "frame_equal" => self.indexed_paths(&["family"])?,
            "frame_at" => self.indexed_paths(&["family", "map_family"])?,
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
        // The kernel rejects the same names, but it has no span for the name.
        if !super::INDEXED_SPELLINGS.contains(&name.as_str()) {
            self.check_binding_name(&name, name_span)?;
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
                    "frame" => indexed::FamilyRepresentation::Frame,
                    "frame_vector" => indexed::FamilyRepresentation::FrameVector,
                    "frame_covector" => indexed::FamilyRepresentation::FrameCovector,
                    "frame_map" => indexed::FamilyRepresentation::FrameMap,
                    "reading" => indexed::FamilyRepresentation::Reading,
                    "physical_metric" => indexed::FamilyRepresentation::PhysicalMetric,
                    _ => {
                        return Err(diagnostic(
                            "E_TYPE",
                            "family representation requires token, point, morphism, relative, smooth, cotangent, tangent, tape, metric_form, frame, frame_vector, frame_covector, frame_map, reading or physical_metric",
                            span,
                        ));
                    }
                };
                // Frame arrays and frame maps have no constraints, so they may
                // omit the clause. Every other family states it.
                let constraints = if !self.peek().is("constraints")
                    && matches!(
                        representation,
                        indexed::FamilyRepresentation::FrameVector
                            | indexed::FamilyRepresentation::FrameCovector
                            | indexed::FamilyRepresentation::FrameMap
                    ) {
                    Vec::new()
                } else {
                    self.expect("constraints")?;
                    self.indexed_list("(", ")", Self::indexed_constraint)?
                };
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
            "frame" => self.indexed_frame()?,
            "base_dimension" => DeclarationBody::BaseDimension,
            "quantity" => {
                self.expect("=")?;
                DeclarationBody::Quantity {
                    dimension: self.indexed_dimension()?,
                }
            }
            "reading" => self.indexed_reading()?,
            "scale" => {
                self.expect("=")?;
                let magnitude = self.polynomial()?;
                self.expect("of")?;
                DeclarationBody::Scale {
                    quantity: self.type_path()?,
                    magnitude,
                }
            }
            "physical" => self.indexed_physical()?,
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
            let element = self.polynomial()?;
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
            self.indexed_list("(", ")", Self::polynomial)?
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

    /// `: Family<X, ...> =`: the family and the indices of a declaration that
    /// is declared at a family, up to its `=`.
    fn indexed_application(&mut self) -> Result<(TypePath, Vec<TypePath>), Diagnostic> {
        self.expect(":")?;
        let family = self.type_path()?;
        self.expect("<")?;
        let mut indices = vec![self.type_path()?];
        while self.consume(",") {
            indices.push(self.type_path()?);
        }
        self.type_close()?;
        self.expect("=")?;
        Ok((family, indices))
    }

    /// `: Family<X, Y, S> = pullback(y -> p, ...) | identity | structure`
    fn indexed_morphism(&mut self) -> Result<DeclarationBody, Diagnostic> {
        let (family, indices) = self.indexed_application()?;
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
        let (family, indices) = self.indexed_application()?;
        let span = self.peek().span;
        let gram = match self.indexed_tag()?.as_str() {
            "euclidean" => indexed::MetricGram::Euclidean,
            "gram" => indexed::MetricGram::Gram {
                rows: self
                    .indexed_list("(", ")", |p| p.indexed_list("(", ")", Self::polynomial))?,
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

    /// `: Family<X> = columns((p, …), …) [inverse = columns((q, …), …)]` or
    /// `: Family<X> = coordinates`. Each column is a parenthesized tuple of
    /// polynomials in the coordinates of `X`, and the wire keeps the columns
    /// in source order. The kernel computes the inverse of a constant frame;
    /// a frame polynomial in the point declares its inverse.
    fn indexed_frame(&mut self) -> Result<DeclarationBody, Diagnostic> {
        let (family, indices) = self.indexed_application()?;
        let span = self.peek().span;
        let columns = match self.indexed_tag()?.as_str() {
            "coordinates" => {
                if self.peek().is("inverse") {
                    return Err(diagnostic(
                        "E_PARSE",
                        "the coordinate frame `coordinates` declares no inverse",
                        self.peek().span,
                    ));
                }
                indexed::FrameColumns::Coordinates
            }
            "columns" => self.frame_columns()?,
            "inverse" => {
                return Err(diagnostic(
                    "E_PARSE",
                    "a frame declares its `columns(…)` first; `inverse = columns(…)` follows them",
                    span,
                ));
            }
            _ => {
                return Err(diagnostic(
                    "E_TYPE",
                    "a frame is `coordinates` or `columns((…), …)` with one column per coordinate, optionally followed by `inverse = columns((…), …)`",
                    span,
                ));
            }
        };
        let inverse = if self.consume("inverse") {
            self.expect("=")?;
            self.expect("columns")?;
            Some(self.frame_columns()?)
        } else {
            None
        };
        Ok(DeclarationBody::Frame {
            family,
            indices,
            columns,
            inverse,
        })
    }

    /// `((p, …), …)` after `columns`: the columns, each a parenthesized tuple
    /// of polynomial entries. `columns()` has no columns.
    fn frame_columns(&mut self) -> Result<indexed::FrameColumns, Diagnostic> {
        let columns = self.indexed_list("(", ")", |p| {
            if !p.peek().is("(") {
                return Err(diagnostic(
                    "E_PARSE",
                    "a frame column is a parenthesized tuple of entries, as in `columns((1, 0), (0, 1))`",
                    p.peek().span,
                ));
            }
            p.indexed_list("(", ")", Self::polynomial)
        })?;
        Ok(indexed::FrameColumns::Columns { columns })
    }

    /// A physical dimension after `quantity … =` or `value =`: `1`, or base
    /// dimensions with integer exponents, as in `L * T^-1`. There is no
    /// division; the lexer already rejects `/`.
    fn indexed_dimension(&mut self) -> Result<Vec<indexed::DimensionFactor>, Diagnostic> {
        let token = self.peek().clone();
        if let TokenKind::Number(value) = &token.kind {
            if value == "1" {
                self.advance();
                return Ok(Vec::new());
            }
            return Err(diagnostic(
                "E_PARSE",
                "a dimension is `1` or a product of base dimensions with integer exponents, as in `L * T^-1`",
                token.span,
            ));
        }
        let mut factors = Vec::new();
        loop {
            let base = self.type_path()?;
            let exponent = if self.consume("^") {
                self.indexed_exponent()?
            } else {
                "1".into()
            };
            factors.push(indexed::DimensionFactor { base, exponent });
            if !self.consume("*") {
                return Ok(factors);
            }
        }
    }

    /// The integer exponent after `^`: `n` or `-n`. Its digits are bounded as
    /// the kernel's decoder bounds them.
    fn indexed_exponent(&mut self) -> Result<String, Diagnostic> {
        let negative = self.consume("-");
        let token = self.advance();
        match token.kind {
            TokenKind::Number(digits) if digits.len() <= crate::limits::MAX_ALGEBRA_DIGITS => {
                Ok(if negative {
                    format!("-{digits}")
                } else {
                    digits
                })
            }
            TokenKind::Number(_) => Err(diagnostic(
                "E_LIMIT",
                format!(
                    "an exponent has at most {} decimal digits",
                    crate::limits::MAX_ALGEBRA_DIGITS
                ),
                token.span,
            )),
            _ => Err(diagnostic(
                "E_PARSE",
                "an exponent is an integer, written `^n` or `^-n`; rational exponents are not supported",
                token.span,
            )),
        }
    }

    /// `: Family<X> = (x: Quantity, …)`: the quantity of each coordinate of
    /// `X`, in source order.
    fn indexed_reading(&mut self) -> Result<DeclarationBody, Diagnostic> {
        let (family, indices) = self.indexed_application()?;
        let quantities = self.indexed_list("(", ")", |p| {
            let coordinate = p.coordinate_name()?;
            p.expect(":")?;
            Ok(indexed::ReadingEntry {
                coordinate,
                quantity: p.type_path()?,
            })
        })?;
        Ok(DeclarationBody::Reading {
            family,
            indices,
            quantities,
        })
    }

    /// `: Family<X> = interpret(G, reading = r, entries[, value = D])`, where
    /// the entries are `euclidean`, `gram((m, …), …)` with rows of scale
    /// monomials, or `normalized(x: s, …)` with one scale per coordinate.
    fn indexed_physical(&mut self) -> Result<DeclarationBody, Diagnostic> {
        let (family, indices) = self.indexed_application()?;
        self.expect("interpret")?;
        self.expect("(")?;
        let metric = self.type_path()?;
        let reading = self.indexed_selection("interpret", "reading", "the reading of its chart")?;
        self.expect(",")?;
        let span = self.peek().span;
        let entries = match self.indexed_tag()?.as_str() {
            "euclidean" => indexed::PhysicalGram::Euclidean,
            "gram" => indexed::PhysicalGram::Gram {
                rows: self
                    .indexed_list("(", ")", |p| p.indexed_list("(", ")", Self::scale_monomial))?,
            },
            "normalized" => indexed::PhysicalGram::Normalized {
                scales: self.indexed_list("(", ")", |p| {
                    let coordinate = p.coordinate_name()?;
                    p.expect(":")?;
                    Ok(indexed::CoordinateScale {
                        coordinate,
                        scale: p.type_path()?,
                    })
                })?,
            },
            _ => {
                return Err(diagnostic(
                    "E_TYPE",
                    "a physical metric interprets `euclidean`, `gram((…), …)` with one row per coordinate, or `normalized(x: scale, …)`",
                    span,
                ));
            }
        };
        let value = if self.consume(",") {
            self.expect("value")?;
            self.expect("=")?;
            Some(self.indexed_dimension()?)
        } else {
            None
        };
        self.expect(")")?;
        Ok(DeclarationBody::PhysicalMetric {
            family,
            indices,
            metric,
            reading,
            value,
            entries,
        })
    }

    /// One entry of a physical Gram matrix, in its own small grammar rather
    /// than as a polynomial: `['-'] factor ('*' factor)*`, where a factor is a
    /// coefficient `n` or `frac(i, n)`, or a scale with an optional integer
    /// exponent, `s^k`. The coefficient is the product of the coefficient
    /// factors (`1` without any), negated by a leading `-`, so `-1 * c^2` and
    /// `-c^2` are the same entry. `0` is the zero entry.
    fn scale_monomial(&mut self) -> Result<indexed::ScaleMonomial, Diagnostic> {
        let negative = self.consume("-");
        let mut coefficients = Vec::new();
        let mut factors = Vec::new();
        loop {
            if matches!(self.peek().kind, TokenKind::Number(_)) {
                coefficients.push(indexed::PolyExpr::Natural {
                    value: self.poly_literal()?,
                });
            } else if self.at_fraction() {
                coefficients.push(self.fraction()?);
            } else {
                let scale = self.type_path()?;
                let exponent = if self.consume("^") {
                    self.indexed_exponent()?
                } else {
                    "1".into()
                };
                factors.push(indexed::ScaleFactor { scale, exponent });
            }
            if !self.consume("*") {
                break;
            }
        }
        let coefficient = match coefficients.len() {
            0 => indexed::PolyExpr::Natural { value: "1".into() },
            1 => coefficients.pop().unwrap(),
            _ => indexed::PolyExpr::Product {
                factors: coefficients,
            },
        };
        Ok(indexed::ScaleMonomial {
            coefficient: if negative {
                indexed::PolyExpr::Neg {
                    operand: Box::new(coefficient),
                }
            } else {
                coefficient
            },
            factors,
        })
    }

    /// `, keyword = path`: the metric or evidence that `flat` and `sharp`
    /// name explicitly, the reading that `interpret` names, and the frames
    /// of the frame primitives. No default is ever selected.
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

    /// One whole polynomial expression. The kernel's decoder spends one level
    /// of `algebraNesting` on every node of the wire tree. The frontend counts
    /// the same levels, so an expression that the decoder would refuse is an
    /// `E_LIMIT` at its own span.
    fn polynomial(&mut self) -> Result<indexed::PolyExpr, Diagnostic> {
        let start = self.peek().span;
        let expression = self.poly(0)?;
        if poly_levels(&expression) > crate::limits::MAX_ALGEBRA_NESTING {
            return Err(diagnostic(
                "E_LIMIT",
                "polynomial expression is nested too deeply",
                start.through(self.previous().span),
            ));
        }
        Ok(expression)
    }

    /// Bounds the parser's own recursion: `depth` counts the enclosing
    /// parentheses and prefix `-`. Parentheses are not nodes of the wire
    /// tree, so `polynomial` counts its levels separately.
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
        if self.at_fraction() {
            return self.fraction();
        }
        Ok(indexed::PolyExpr::Coordinate {
            name: self.coordinate_name()?,
        })
    }

    /// Whether the next tokens start a fraction literal, `frac(`.
    fn at_fraction(&self) -> bool {
        self.peek().is("frac")
            && self
                .tokens
                .get(self.position + 1)
                .is_some_and(|next| next.is("("))
    }

    /// `frac(i, n)`: a fraction literal whose numerator may carry a `-`.
    fn fraction(&mut self) -> Result<indexed::PolyExpr, Diagnostic> {
        self.expect("frac")?;
        self.expect("(")?;
        let negative = self.consume("-");
        let numerator = self.poly_literal()?;
        self.expect(",")?;
        let denominator = self.poly_literal()?;
        self.expect(")")?;
        Ok(indexed::PolyExpr::Fraction {
            numerator: if negative {
                format!("-{numerator}")
            } else {
                numerator
            },
            denominator,
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
            image: self.polynomial()?,
        })
    }
}

/// The levels that the kernel's `Wire.polyExpr` spends on an expression: the
/// nodes on the longest path from its root to a leaf. Every literal,
/// coordinate, sum, product, negation and power is a node. The recursion is
/// bounded, because `poly_nesting` admits at most four nodes for each level of
/// parentheses and one for each prefix `-`.
fn poly_levels(expression: &indexed::PolyExpr) -> usize {
    use indexed::PolyExpr::{Coordinate, Fraction, Natural, Neg, Pow, Product, Sum};
    1 + match expression {
        Natural { .. } | Fraction { .. } | Coordinate { .. } => 0,
        Neg { operand } => poly_levels(operand),
        Pow { base, .. } => poly_levels(base),
        Sum { terms: operands } | Product { factors: operands } => {
            operands.iter().map(poly_levels).max().unwrap_or(0)
        }
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
        ("frame_encode", "frame_encode(Tangent, Coords, frame = b)"),
        ("frame_decode", "frame_decode(Coords, Tangent, frame = b)"),
        ("frame_vector", "frame_vector(Coords, Smooth, frame = b)"),
        (
            "frame_matrix",
            "frame_matrix(Smooth, FrameMap, source = b, target = c)",
        ),
        (
            "frame_transition",
            "frame_transition(Smooth, FrameMap, source = b, target = b2)",
        ),
        ("frame_apply", "frame_apply(FrameMap, Coords)"),
        ("frame_coapply", "frame_coapply(FrameMap, CoCoords)"),
        ("frame_compose", "frame_compose(FrameMap)"),
        ("frame_pairing", "frame_pairing(CoCoords, Coords)"),
        ("frame_component", "frame_component(Coords, 0)"),
        ("frame_entry", "frame_entry(FrameMap, 0, 1)"),
        ("frame_equal", "frame_equal(Coords)"),
        ("frame_at", "frame_at(Coords, Smooth)"),
    ];

    /// The one indexed declaration of a package module.
    fn parse_declaration(source: &str) -> Result<indexed::Declaration, Diagnostic> {
        let parsed = parse_module_source(
            SourceInput {
                source,
                file: "declaration.vast",
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
        Ok(declaration.declaration.clone())
    }

    fn parse_binding(source: &str) -> Result<Primitive, Diagnostic> {
        match parse_declaration(source)?.body {
            DeclarationBody::Primitive { binding } => Ok(binding),
            body => panic!("primitive expected, got {body:?}"),
        }
    }

    /// Every family of the table has a surface form, and each form parses
    /// to a binding with exactly the family's fields, which serializes as
    /// `{"op": …}` followed by those fields in table order. A declaration of
    /// the binding needs protocol 9 exactly when the table says the family is
    /// algebraic.
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
            let body = DeclarationBody::Primitive { binding };
            assert_eq!(body.is_algebraic(), family.algebraic, "{snippet}");
        }
    }

    /// The frame primitives of Stage 4 (#759), each with the binding that
    /// the kernel's protocol-9 decoder reads: the positional fields in wire
    /// order, the frames under their keywords, and natural fields as bare
    /// decimal strings. Every one is algebraic, so it selects protocol 9.
    #[test]
    fn every_frame_primitive_parses_to_its_wire_record() {
        let widest = "9".repeat(crate::limits::MAX_ALGEBRA_DIGITS);
        let widest_source = format!("indexed primitive wide = frame_component(Coords, {widest});");
        let cases: Vec<(&str, Value)> = vec![
            (
                "indexed primitive enc_b = frame_encode(Tangent, Coords, frame = b);",
                json!({ "op": "frame_encode", "fiber": p("Tangent"), "coords": p("Coords"),
                    "frame": p("b") }),
            ),
            (
                "indexed primitive coenc_b = frame_encode(Cotangent, CoCoords, frame = b);",
                json!({ "op": "frame_encode", "fiber": p("Cotangent"), "coords": p("CoCoords"),
                    "frame": p("b") }),
            ),
            (
                "indexed primitive dec_b = frame_decode(Coords, Tangent, frame = b);",
                json!({ "op": "frame_decode", "coords": p("Coords"), "fiber": p("Tangent"),
                    "frame": p("b") }),
            ),
            (
                "indexed primitive vec_b = frame_vector(Coords, Smooth, frame = b);",
                json!({ "op": "frame_vector", "coords": p("Coords"), "map_family": p("Smooth"),
                    "frame": p("b") }),
            ),
            (
                "indexed primitive matrix_bc = frame_matrix(Smooth, FrameMap, source = b, target = c);",
                json!({ "op": "frame_matrix", "map_family": p("Smooth"),
                    "frame_map": p("FrameMap"), "source": p("b"), "target": p("c") }),
            ),
            (
                "indexed primitive move_bb2 = frame_transition(Smooth, FrameMap, source = b, target = b2);",
                json!({ "op": "frame_transition", "map_family": p("Smooth"),
                    "frame_map": p("FrameMap"), "source": p("b"), "target": p("b2") }),
            ),
            (
                "indexed primitive apply = frame_apply(FrameMap, Coords);",
                json!({ "op": "frame_apply", "frame_map": p("FrameMap"), "coords": p("Coords") }),
            ),
            (
                "indexed primitive coapply = frame_coapply(FrameMap, CoCoords);",
                json!({ "op": "frame_coapply", "frame_map": p("FrameMap"),
                    "cocoords": p("CoCoords") }),
            ),
            (
                "indexed primitive then = frame_compose(FrameMap);",
                json!({ "op": "frame_compose", "frame_map": p("FrameMap") }),
            ),
            // `pair` is a builtin, reserved as a declaration name.
            (
                "indexed primitive pairing = frame_pairing(CoCoords, Coords);",
                json!({ "op": "frame_pairing", "cocoords": p("CoCoords"), "coords": p("Coords") }),
            ),
            (
                "indexed primitive first = frame_component(Coords, 0);",
                json!({ "op": "frame_component", "family": p("Coords"), "index": "0" }),
            ),
            (
                "indexed primitive entry_01 = frame_entry(FrameMap, 0, 1);",
                json!({ "op": "frame_entry", "frame_map": p("FrameMap"), "row": "0",
                    "column": "1" }),
            ),
            (
                "indexed primitive same_coords = frame_equal(Coords);",
                json!({ "op": "frame_equal", "family": p("Coords") }),
            ),
            (
                "indexed primitive over = frame_at(Coords, Smooth);",
                json!({ "op": "frame_at", "family": p("Coords"), "map_family": p("Smooth") }),
            ),
            // Qualified paths, and the digits of a natural as written, up to
            // the decoder's bound.
            (
                "indexed primitive move = frame_transition(geo::Smooth, geo::FrameMap, source = geo::b, target = super::c);",
                json!({ "op": "frame_transition",
                    "map_family": { "path": ["geo", "Smooth"] },
                    "frame_map": { "path": ["geo", "FrameMap"] },
                    "source": { "path": ["geo", "b"] }, "target": { "path": ["super", "c"] } }),
            ),
            (
                "indexed primitive late = frame_entry(FrameMap, 007, 10);",
                json!({ "op": "frame_entry", "frame_map": p("FrameMap"), "row": "007",
                    "column": "10" }),
            ),
            (
                &widest_source,
                json!({ "op": "frame_component", "family": p("Coords"), "index": widest }),
            ),
        ];
        for (source, expected) in cases {
            let declaration = parse_declaration(source)
                .unwrap_or_else(|error| panic!("`{source}` does not parse: {error:?}"));
            assert!(declaration.body.is_algebraic(), "{source}");
            let record = without_spans(serde_json::to_value(&declaration.body).unwrap());
            assert_eq!(
                record,
                json!({ "kind": "primitive", "binding": expected }),
                "{source}"
            );
            assert_eq!(
                &source[declaration.span.start..declaration.span.end],
                source
            );
        }
    }

    /// Malformed frame primitives are rejected at the offending token: a
    /// missing frame keyword, a natural field that is not a natural literal,
    /// and a wrong number of fields. Each case names the token of the place
    /// and a text that starts there and occurs once in the source, so a `,`
    /// or `)` place is the one meant.
    #[test]
    fn malformed_frame_primitives_are_rejected_at_their_place() {
        let long = "9".repeat(crate::limits::MAX_ALGEBRA_DIGITS + 1);
        let long_index = format!("indexed primitive p = frame_component(Coords, {long});");
        let long_column = format!("indexed primitive p = frame_entry(FrameMap, 0, {long});");
        let frame = "`frame_encode` needs an explicit frame: write `frame = …`";
        let source_frame = "`frame_matrix` needs an explicit source frame: write `source = …`";
        let index =
            "the index of `frame_component` is a natural literal, written as an unsigned integer";
        let cases: Vec<(&str, &str, &str, &str, &str)> = vec![
            // The frames are named by their keywords, in wire order.
            (
                "indexed primitive p = frame_encode(Tangent, Coords, b);",
                "E_PARSE",
                frame,
                ",",
                ", b)",
            ),
            (
                "indexed primitive p = frame_encode(Tangent, Coords);",
                "E_PARSE",
                frame,
                ")",
                ");",
            ),
            (
                "indexed primitive p = frame_decode(Coords, Tangent, using = b);",
                "E_PARSE",
                "`frame_decode` needs an explicit frame: write `frame = …`",
                ",",
                ", using",
            ),
            (
                "indexed primitive p = frame_vector(Coords, Smooth);",
                "E_PARSE",
                "`frame_vector` needs an explicit frame: write `frame = …`",
                ")",
                ");",
            ),
            (
                "indexed primitive p = frame_encode(Tangent, Coords, frame b);",
                "E_PARSE",
                "expected `=`, found `b`",
                "b",
                "b)",
            ),
            (
                "indexed primitive p = frame_matrix(Smooth, FrameMap, b, c);",
                "E_PARSE",
                source_frame,
                ",",
                ", b,",
            ),
            (
                "indexed primitive p = frame_matrix(Smooth, FrameMap, target = c, source = b);",
                "E_PARSE",
                source_frame,
                ",",
                ", target",
            ),
            (
                "indexed primitive p = frame_matrix(Smooth, FrameMap, source = b);",
                "E_PARSE",
                "`frame_matrix` needs an explicit target frame: write `target = …`",
                ")",
                ");",
            ),
            (
                "indexed primitive p = frame_transition(Smooth, FrameMap, source = b, c);",
                "E_PARSE",
                "`frame_transition` needs an explicit target frame: write `target = …`",
                ",",
                ", c)",
            ),
            // Without its frame map, `source` is read as the frame map, and
            // the source frame is missing.
            (
                "indexed primitive p = frame_matrix(Smooth, source = b, target = c);",
                "E_PARSE",
                source_frame,
                "=",
                "= b,",
            ),
            (
                "indexed primitive p = frame_encode(Tangent, Coords, frame = b, frame = c);",
                "E_PARSE",
                "expected `)`, found `,`",
                ",",
                ", frame = c",
            ),
            // Natural fields are unsigned decimal literals.
            (
                "indexed primitive p = frame_component(Coords, x);",
                "E_PARSE",
                index,
                "x",
                "x)",
            ),
            (
                "indexed primitive p = frame_component(Coords, -1);",
                "E_PARSE",
                index,
                "-",
                "-1",
            ),
            (
                "indexed primitive p = frame_component(Coords, index = 0);",
                "E_PARSE",
                index,
                "index",
                "index =",
            ),
            (
                "indexed primitive p = frame_entry(FrameMap, frac(1, 2), 0);",
                "E_PARSE",
                "the row of `frame_entry` is a natural literal, written as an unsigned integer",
                "frac",
                "frac",
            ),
            (
                "indexed primitive p = frame_entry(FrameMap, 0, 1.5);",
                "E_PARSE",
                "the column of `frame_entry` is a natural literal, written as an unsigned integer",
                "1.5",
                "1.5",
            ),
            (
                &long_index,
                "E_LIMIT",
                "the index of `frame_component` has at most 64 decimal digits",
                &long,
                &long,
            ),
            (
                &long_column,
                "E_LIMIT",
                "the column of `frame_entry` has at most 64 decimal digits",
                &long,
                &long,
            ),
            // Too few or too many fields.
            (
                "indexed primitive p = frame_apply(FrameMap);",
                "E_PARSE",
                "expected `,`, found `)`",
                ")",
                ");",
            ),
            (
                "indexed primitive p = frame_compose(FrameMap, FrameMap);",
                "E_PARSE",
                "expected `)`, found `,`",
                ",",
                ", FrameMap)",
            ),
            (
                "indexed primitive p = frame_pairing(CoCoords, Coords, Coords);",
                "E_PARSE",
                "expected `)`, found `,`",
                ",",
                ", Coords)",
            ),
            (
                "indexed primitive p = frame_component(Coords);",
                "E_PARSE",
                "expected `,`, found `)`",
                ")",
                ");",
            ),
            (
                "indexed primitive p = frame_entry(FrameMap, 0);",
                "E_PARSE",
                "expected `,`, found `)`",
                ")",
                ");",
            ),
            (
                "indexed primitive p = frame_entry(FrameMap, 0, 1, 2);",
                "E_PARSE",
                "expected `)`, found `,`",
                ",",
                ", 2)",
            ),
            (
                "indexed primitive p = frame_at(Coords);",
                "E_PARSE",
                "expected `,`, found `)`",
                ")",
                ");",
            ),
        ];
        for (source, code, message, place, context) in cases {
            let error = parse_declaration(source).expect_err(source);
            assert_eq!(
                (error.code.as_str(), error.message.as_str()),
                (code, message),
                "{source}"
            );
            assert_eq!(
                &source[error.span.start..error.span.end],
                place,
                "{source}: {error:?}"
            );
            assert_eq!(source.matches(context).count(), 1, "{source}: {context}");
            assert!(context.starts_with(place), "{source}: {context}");
            assert_eq!(
                source.find(context),
                Some(error.span.start),
                "{source}: {error:?}"
            );
        }
    }

    fn coefficient(monomial: &str) -> Result<Primitive, Diagnostic> {
        parse_binding(&format!(
            "indexed primitive p = relative_coefficient(Over, D, Line, t, {monomial});"
        ))
    }

    /// The frontend counts the levels that the kernel's decoder spends on a
    /// polynomial (#631): one for the leaf and one for every sum, product,
    /// negation and power above it. A binary minus is a sum over a negation,
    /// and parentheses are no level.
    #[test]
    fn polynomial_levels_count_every_wire_node() {
        const TOO_DEEP: &str = "polynomial expression is nested too deeply";
        let limit = crate::limits::MAX_ALGEBRA_NESTING;
        // Each wrap puts `levels` nodes above its operand `@`.
        for (wrap, levels) in [
            ("(@ + 1)", 1),
            ("(@ * 2)", 1),
            ("(@)^1", 1),
            ("(1 - @)", 2),
            ("(@ * 1 + 1)", 2),
            ("(1 - @ * 2)", 3),
            ("(1 - 2 * (@)^1)", 4),
        ] {
            let wraps = (limit - 1) / levels;
            let body = (0..wraps).fold("e".to_string(), |inner, _| wrap.replace('@', &inner));
            // Prefix minus signs fill the path up to the limit, one level each.
            let filled = format!("{}{body}", "-".repeat(limit - 1 - wraps * levels));
            coefficient(&filled).unwrap_or_else(|error| panic!("`{wrap}`: {error:?}"));
            let error = coefficient(&format!("-{filled}")).expect_err(wrap);
            assert_eq!(
                (error.code.as_str(), error.message.as_str()),
                ("E_LIMIT", TOO_DEEP)
            );
        }
        // The diagnostic covers the whole expression.
        let entry = (0..33).fold("1".to_string(), |inner, _| format!("({inner}*1+1)"));
        let source =
            format!("indexed primitive p = relative_coefficient(Over, D, Line, t, {entry});");
        let error = parse_binding(&source).expect_err("67 levels");
        assert_eq!(
            (error.code.as_str(), error.message.as_str()),
            ("E_LIMIT", TOO_DEEP)
        );
        assert_eq!(&source[error.span.start..error.span.end], entry);
        // Parentheses and prefix minus signs bound the parser's recursion.
        let parentheses = |depth: usize| format!("{}e{}", "(".repeat(depth), ")".repeat(depth));
        coefficient(&parentheses(limit - 1)).unwrap();
        let error = coefficient(&parentheses(limit)).expect_err("64 parentheses");
        assert_eq!(
            (error.code.as_str(), error.message.as_str()),
            ("E_LIMIT", TOO_DEEP)
        );
    }

    #[test]
    fn an_op_outside_the_table_is_unknown() {
        let error = parse_binding("indexed primitive p = gradient(Smooth, Cotangent);")
            .expect_err("`gradient` is not a primitive");
        assert_eq!(error.code, "E_TYPE");
        assert_eq!(error.message, "unknown indexed primitive contract");
    }

    use serde_json::{Value, json};

    /// A value without its `span` fields, which the tables below omit.
    fn without_spans(mut value: Value) -> Value {
        fn strip(value: &mut Value) {
            match value {
                Value::Object(fields) => {
                    fields.remove("span");
                    fields.values_mut().for_each(strip);
                }
                Value::Array(items) => items.iter_mut().for_each(strip),
                _ => {}
            }
        }
        strip(&mut value);
        value
    }

    fn p(name: &str) -> Value {
        json!({ "path": [name] })
    }

    fn n(value: &str) -> Value {
        json!({ "op": "natural", "value": value })
    }

    fn fraction(numerator: &str, denominator: &str) -> Value {
        json!({ "op": "fraction", "numerator": numerator, "denominator": denominator })
    }

    fn coordinate(name: &str) -> Value {
        json!({ "op": "coordinate", "name": name })
    }

    /// A scale monomial: a coefficient and `(scale, exponent)` factors.
    fn monomial(coefficient: Value, factors: &[(&str, &str)]) -> Value {
        let factors: Vec<Value> = factors
            .iter()
            .map(|(scale, exponent)| json!({ "scale": p(scale), "exponent": exponent }))
            .collect();
        json!({ "coefficient": coefficient, "factors": factors })
    }

    fn factor(base: &str, exponent: &str) -> Value {
        json!({ "base": p(base), "exponent": exponent })
    }

    /// Every Stage 4 declaration form (#759) with the record that the kernel's
    /// protocol-9 decoder reads, spans omitted. The shapes are S1's
    /// (`indexed::tests::every_frame_and_dimension_form_serializes_to_its_wire_shape_and_is_algebraic`).
    fn stage4_declarations() -> Vec<(&'static str, Value)> {
        let family = |parameters: Value, constraints: Value, representation: &str| {
            json!({ "kind": "family", "parameters": parameters,
                "constraints": constraints, "representation": representation })
        };
        let object = json!([{ "kind": "object", "domain": p("CInfAffine") }]);
        let canonical = json!([{ "kind": "canonical", "object": 0 }]);
        let frame_parameter = json!({ "kind": "frame", "family": p("Frame") });
        let frame = |columns: Value, inverse: Value| {
            json!({ "kind": "frame", "family": p("Frame"), "indices": [p("X")],
                "columns": columns, "inverse": inverse })
        };
        let columns = |columns: Value| json!({ "kind": "columns", "columns": columns });
        let physical = |metric: &str, value: Value, entries: Value| {
            json!({ "kind": "physical_metric", "family": p("PhysicalMetric"), "indices": [p("C")],
                "metric": p(metric), "reading": p("phys"), "value": value, "entries": entries })
        };
        let one = || monomial(n("1"), &[]);
        let zero = || monomial(n("0"), &[]);
        let minus_one = json!({ "op": "neg", "operand": n("1") });
        vec![
            (
                "indexed family Frame(object(CInfAffine)) = frame constraints(canonical(0));",
                family(object.clone(), canonical.clone(), "frame"),
            ),
            (
                "indexed family Coords(frame(Frame)) = frame_vector;",
                family(json!([frame_parameter]), json!([]), "frame_vector"),
            ),
            (
                "indexed family CoCoords(frame(Frame)) = frame_covector;",
                family(json!([frame_parameter]), json!([]), "frame_covector"),
            ),
            (
                "indexed family FrameMap(frame(Frame), frame(Frame)) = frame_map;",
                family(
                    json!([frame_parameter, frame_parameter]),
                    json!([]),
                    "frame_map",
                ),
            ),
            // An empty clause is the same record.
            (
                "indexed family Coords(frame(Frame)) = frame_vector constraints();",
                family(json!([frame_parameter]), json!([]), "frame_vector"),
            ),
            (
                "indexed family Reading(object(CInfAffine)) = reading constraints(canonical(0));",
                family(object.clone(), canonical.clone(), "reading"),
            ),
            (
                "indexed family PhysicalMetric(object(CInfAffine)) = physical_metric constraints(canonical(0));",
                family(object, canonical, "physical_metric"),
            ),
            (
                "indexed frame b: Frame<X> = columns((1, 0), (1, 2));",
                frame(
                    columns(json!([[n("1"), n("0")], [n("1"), n("2")]])),
                    Value::Null,
                ),
            ),
            (
                "indexed frame r: Frame<X> = columns((1, 0), (x, 2)) inverse = columns((1, 0), (frac(-1, 2) * x, frac(1, 2)));",
                frame(
                    columns(json!([[n("1"), n("0")], [coordinate("x"), n("2")]])),
                    columns(json!([
                        [n("1"), n("0")],
                        [
                            { "op": "product", "factors": [fraction("-1", "2"), coordinate("x")] },
                            fraction("1", "2")
                        ]
                    ])),
                ),
            ),
            (
                "indexed frame e: Frame<X> = coordinates;",
                frame(json!({ "kind": "coordinates" }), Value::Null),
            ),
            // `Affine(0)` has a frame without columns.
            (
                "indexed frame z: Frame<X> = columns();",
                frame(columns(json!([])), Value::Null),
            ),
            (
                "indexed base_dimension L;",
                json!({ "kind": "base_dimension" }),
            ),
            (
                "indexed quantity Length = L;",
                json!({ "kind": "quantity", "dimension": [factor("L", "1")] }),
            ),
            (
                "indexed quantity Speed = L * T^-1;",
                json!({ "kind": "quantity", "dimension": [factor("L", "1"), factor("T", "-1")] }),
            ),
            (
                "indexed quantity Ratio = 1;",
                json!({ "kind": "quantity", "dimension": [] }),
            ),
            (
                "indexed reading phys: Reading<C> = (x: Length, t: Time);",
                json!({ "kind": "reading", "family": p("Reading"), "indices": [p("C")],
                    "quantities": [{ "coordinate": "x", "quantity": p("Length") },
                        { "coordinate": "t", "quantity": p("Time") }] }),
            ),
            (
                "indexed scale l0 = 3 of Length;",
                json!({ "kind": "scale", "quantity": p("Length"), "magnitude": n("3") }),
            ),
            (
                "indexed scale h = frac(1, 2) of Length;",
                json!({ "kind": "scale", "quantity": p("Length"), "magnitude": fraction("1", "2") }),
            ),
            (
                "indexed physical PG: PhysicalMetric<C> = interpret(G, reading = phys, gram((l0^-2, 0), (0, t0^-2)));",
                physical(
                    "G",
                    Value::Null,
                    json!({ "kind": "gram", "rows": [
                        [monomial(n("1"), &[("l0", "-2")]), zero()],
                        [zero(), monomial(n("1"), &[("t0", "-2")])]
                    ] }),
                ),
            ),
            (
                "indexed physical PE: PhysicalMetric<C> = interpret(E, reading = phys, euclidean);",
                physical("E", Value::Null, json!({ "kind": "euclidean" })),
            ),
            (
                "indexed physical PN: PhysicalMetric<C> = interpret(G, reading = phys, normalized(x: l0, t: t0), value = 1);",
                physical(
                    "G",
                    json!([]),
                    json!({ "kind": "normalized", "scales": [
                        { "coordinate": "x", "scale": p("l0") },
                        { "coordinate": "t", "scale": p("t0") }
                    ] }),
                ),
            ),
            (
                "indexed physical PM: PhysicalMetric<C> = interpret(M, reading = phys, gram((1, 0), (0, -1 * c^2)), value = L^2);",
                physical(
                    "M",
                    json!([factor("L", "2")]),
                    json!({ "kind": "gram", "rows": [
                        [one(), zero()],
                        [zero(), monomial(minus_one.clone(), &[("c", "2")])]
                    ] }),
                ),
            ),
            // `-c^2` is `-1 * c^2`. Several coefficients are one product, and
            // a scale without an exponent has exponent 1.
            (
                "indexed physical PM: PhysicalMetric<C> = interpret(M, reading = phys, gram((-c^2, 2 * frac(-1, 3) * l0 * t0^4)), value = L^2 * T^-2);",
                physical(
                    "M",
                    json!([factor("L", "2"), factor("T", "-2")]),
                    json!({ "kind": "gram", "rows": [[
                        monomial(minus_one, &[("c", "2")]),
                        monomial(
                            json!({ "op": "product", "factors": [n("2"), fraction("-1", "3")] }),
                            &[("l0", "1"), ("t0", "4")]
                        )
                    ]] }),
                ),
            ),
        ]
    }

    /// Each Stage 4 declaration form parses to the record of its S1 wire
    /// shape, which exists only in protocol 9.
    #[test]
    fn every_stage4_declaration_parses_to_its_wire_record() {
        for (source, expected) in stage4_declarations() {
            let declaration = parse_declaration(source)
                .unwrap_or_else(|error| panic!("`{source}` does not parse: {error:?}"));
            assert!(declaration.body.is_algebraic(), "{source}");
            let record = without_spans(serde_json::to_value(&declaration.body).unwrap());
            assert_eq!(record, expected, "{source}");
            // The declaration's place runs from `indexed` to its `;`.
            assert_eq!(
                &source[declaration.span.start..declaration.span.end],
                source
            );
        }
    }

    /// Malformed Stage 4 declarations are rejected at the offending token.
    #[test]
    fn malformed_stage4_declarations_are_rejected_at_their_place() {
        let long = "9".repeat(crate::limits::MAX_ALGEBRA_DIGITS + 1);
        let long_exponent = format!("indexed quantity Q = L^-{long};");
        let long_scale_exponent = format!(
            "indexed physical P: PhysicalMetric<C> = interpret(G, reading = phys, gram((l0^{long})));"
        );
        let cases: Vec<(&str, &str, &str, &str)> = vec![
            // A scale names its quantity after `of`.
            (
                "indexed scale l0 = 3 Length;",
                "E_PARSE",
                "expected `of`, found `Length`",
                "Length",
            ),
            // Exponents are integers.
            (
                "indexed quantity Q = L^frac(1, 2);",
                "E_PARSE",
                "an exponent is an integer, written `^n` or `^-n`; rational exponents are not supported",
                "frac",
            ),
            (
                "indexed quantity Q = L^1.5;",
                "E_PARSE",
                "rational exponents are not supported",
                "1.5",
            ),
            (
                "indexed quantity Q = L^-(1);",
                "E_PARSE",
                "rational exponents are not supported",
                "(",
            ),
            (
                "indexed physical P: PhysicalMetric<C> = interpret(G, reading = phys, gram((l0^frac(1, 2))));",
                "E_PARSE",
                "rational exponents are not supported",
                "frac",
            ),
            (
                &long_exponent,
                "E_LIMIT",
                "an exponent has at most 64 decimal digits",
                &long,
            ),
            (
                &long_scale_exponent,
                "E_LIMIT",
                "an exponent has at most 64 decimal digits",
                &long,
            ),
            // A dimension has no division: the lexer rejects `/`.
            (
                "indexed quantity Speed = L / T;",
                "E_UNSUPPORTED",
                "division is not supported",
                "/",
            ),
            (
                "indexed physical P: PhysicalMetric<C> = interpret(G, reading = phys, euclidean, value = L / T);",
                "E_UNSUPPORTED",
                "division is not supported",
                "/",
            ),
            (
                "indexed quantity Q = 2;",
                "E_PARSE",
                "a dimension is `1` or a product of base dimensions with integer exponents, as in `L * T^-1`",
                "2",
            ),
            // Columns are tuples, and `inverse` follows them.
            (
                "indexed frame b: Frame<X> = columns(1, 2);",
                "E_PARSE",
                "a frame column is a parenthesized tuple of entries, as in `columns((1, 0), (0, 1))`",
                "1",
            ),
            (
                "indexed frame b: Frame<X> = columns((1, 0), 2);",
                "E_PARSE",
                "a frame column is a parenthesized tuple of entries",
                "2",
            ),
            (
                "indexed frame r: Frame<X> = inverse = columns((1, 0), (0, 1)) columns((1, 0), (0, 1));",
                "E_PARSE",
                "a frame declares its `columns(…)` first; `inverse = columns(…)` follows them",
                "inverse",
            ),
            (
                "indexed frame e: Frame<X> = coordinates inverse = columns((1, 0), (0, 1));",
                "E_PARSE",
                "the coordinate frame `coordinates` declares no inverse",
                "inverse",
            ),
            (
                "indexed frame r: Frame<X> = columns((1, 0), (x, 1)) inverse = coordinates;",
                "E_PARSE",
                "expected `columns`, found `coordinates`",
                "coordinates",
            ),
            (
                "indexed frame b: Frame<X> = rows((1, 0), (0, 1));",
                "E_TYPE",
                "a frame is `coordinates` or `columns((…), …)` with one column per coordinate, optionally followed by `inverse = columns((…), …)`",
                "rows",
            ),
            // The tags of families and parameters list the new ones.
            (
                "indexed family F(object(CInfAffine)) = frames constraints(canonical(0));",
                "E_TYPE",
                "family representation requires token, point, morphism, relative, smooth, cotangent, tangent, tape, metric_form, frame, frame_vector, frame_covector, frame_map, reading or physical_metric",
                "frames",
            ),
            (
                "indexed family Coords(frames(Frame)) = frame_vector;",
                "E_TYPE",
                "index parameters use domain, marker, natural, object(Classification), or frame(Family)",
                "frames",
            ),
            // Only frame arrays and frame maps may omit their constraints.
            (
                "indexed family Frame(object(CInfAffine)) = frame;",
                "E_PARSE",
                "expected `constraints`, found `;`",
                ";",
            ),
            (
                "indexed family Reading(object(CInfAffine)) = reading;",
                "E_PARSE",
                "expected `constraints`, found `;`",
                ";",
            ),
            // A reading pairs each coordinate with a quantity.
            (
                "indexed reading phys: Reading<C> = (x Length);",
                "E_PARSE",
                "expected `:`, found `Length`",
                "Length",
            ),
            // `interpret` names its reading, then its entries.
            (
                "indexed physical P: PhysicalMetric<C> = interpret(G, phys, euclidean);",
                "E_PARSE",
                "`interpret` needs the reading of its chart: write `reading = …`",
                ",",
            ),
            (
                "indexed physical P: PhysicalMetric<C> = interpret(G, reading = phys, identity);",
                "E_TYPE",
                "a physical metric interprets `euclidean`, `gram((…), …)` with one row per coordinate, or `normalized(x: scale, …)`",
                "identity",
            ),
            (
                "indexed physical P: PhysicalMetric<C> = interpret(G, reading = phys, euclidean, dimension = L);",
                "E_PARSE",
                "expected `value`, found `dimension`",
                "dimension",
            ),
            (
                "indexed physical P: PhysicalMetric<C> = interpret(G, reading = phys, normalized(x = l0));",
                "E_PARSE",
                "expected `:`, found `=`",
                "=",
            ),
        ];
        for (source, code, message, place) in cases {
            let error = parse_declaration(source).expect_err(source);
            assert_eq!(error.code, code, "{source}: {error:?}");
            assert!(error.message.contains(message), "{source}: {error:?}");
            assert_eq!(
                &source[error.span.start..error.span.end],
                place,
                "{source}: {error:?}"
            );
        }
    }

    /// The Stage 4 words are contextual: they are reserved nowhere, so
    /// programs that use them as names keep parsing.
    #[test]
    fn stage4_words_remain_ordinary_names() {
        const WORDS: [&str; 15] = [
            "frame",
            "quantity",
            "reading",
            "scale",
            "physical",
            "base_dimension",
            "columns",
            "coordinates",
            "inverse",
            "interpret",
            "normalized",
            "euclidean",
            "of",
            "value",
            "frame_vector",
        ];
        for word in WORDS {
            assert!(!super::super::reserved(word), "{word}");
        }
        // As function names, and as parameter and `let` names.
        let functions: String = WORDS
            .iter()
            .map(|w| format!("fn {w}(n: Int) -> Int {{ n }}\n"))
            .collect();
        let calls: Vec<String> = WORDS.iter().map(|w| format!("{w}(1)")).collect();
        let named = format!("{functions}fn main() -> Int {{ {} }}\n", calls.join(" + "));
        let parameters: Vec<String> = WORDS.iter().map(|w| format!("{w}: Int")).collect();
        let lets: String = WORDS.iter().map(|w| format!("let {w} = 1; ")).collect();
        let bound = format!(
            "fn all({}) -> Int {{ {} }}\nfn main() -> Int {{ {lets}all({}) }}\n",
            parameters.join(", "),
            WORDS.join(" + "),
            WORDS.join(", ")
        );
        for flat in [named, bound] {
            crate::frontend::parse(&flat, "names.vast")
                .unwrap_or_else(|errors| panic!("{errors:?}\n{flat}"));
        }
        // In a package, the words also name indexed declarations, scales and
        // quantities, next to declarations of the new kinds.
        let package = "indexed marker frame;
indexed base_dimension quantity;
indexed quantity reading = quantity^2;
indexed scale of = 3 of reading;
indexed scale value = frac(1, 2) of reading;
indexed physical inverse: PhysicalMetric<C> = interpret(coordinates, reading = columns, gram((of^-2 * value)), value = quantity);
fn scale(physical: Int) -> Int { let interpret = physical; interpret }
";
        let parsed = parse_module_source(
            SourceInput {
                source: package,
                file: "names.vast",
                offset: 0,
            },
            vec![],
            true,
            None,
        )
        .unwrap_or_else(|error| panic!("{error:?}"));
        let names: Vec<&str> = parsed.modules[0]
            .indexed_declarations
            .iter()
            .map(|d| d.declaration.name.as_str())
            .collect();
        assert_eq!(
            names,
            ["frame", "quantity", "reading", "of", "value", "inverse"]
        );
    }
}
