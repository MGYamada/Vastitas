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
        let fields = self.delimited_list("[", "]", |p| {
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
            let indices = self.delimited_list("(", ")", Self::indexed_bound)?;
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

    /// `, n`: the natural field `field` of `op` (`natural_literal`).
    fn indexed_natural(
        &mut self,
        op: &str,
        field: &'static str,
    ) -> Result<(&'static str, WireValue), Diagnostic> {
        self.expect(",")?;
        Ok((field, WireValue::Natural(self.natural_literal(op, field)?)))
    }

    /// The natural `field` of `op`: an unsigned decimal literal with at most
    /// as many digits as the kernel's decoder admits
    /// (`algebraCoefficientDigits`), as for polynomial literals. The digits
    /// go to the wire as written; the kernel applies every other bound.
    fn natural_literal(&mut self, op: &str, field: &str) -> Result<String, Diagnostic> {
        let token = self.advance();
        match token.kind {
            TokenKind::Number(digits) if digits.len() <= crate::limits::MAX_ALGEBRA_DIGITS => {
                Ok(digits)
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

    /// `Smooth, spectrum = S, element = f`: the leading fields of the module
    /// observations `annihilates` and `action_entry`. The spectrum and the
    /// element of `A[t]` are named explicitly; the element is a polynomial
    /// in the coordinates of the object and the fiber coordinate.
    fn indexed_spectral_element(
        &mut self,
        op: &str,
    ) -> Result<Vec<(&'static str, WireValue)>, Diagnostic> {
        let mut fields = self.indexed_paths(&["map_family"])?;
        let spectrum = self.indexed_selection(op, "spectrum", "an explicit spectrum")?;
        fields.push(("spectrum", WireValue::Path(spectrum)));
        self.indexed_keyword(op, "element", "an explicit element")?;
        fields.push(("element", WireValue::Polynomial(self.polynomial()?)));
        Ok(fields)
    }

    /// `, branch = B`: the branch that a branch observation names.
    fn indexed_branch_field(&mut self, op: &str) -> Result<(&'static str, WireValue), Diagnostic> {
        let branch = self.indexed_selection(op, "branch", "an explicit branch")?;
        Ok(("branch", WireValue::Path(branch)))
    }

    /// `, e_i, e_j`: the row and the column of an observed matrix entry, each
    /// a basis name of the free module, as written in its `basis(…)`.
    fn indexed_basis_entry(
        &mut self,
        op: &str,
    ) -> Result<Vec<(&'static str, WireValue)>, Diagnostic> {
        let mut fields = Vec::with_capacity(2);
        for field in ["row", "column"] {
            self.expect(",")?;
            if !matches!(self.peek().kind, TokenKind::Name(_)) {
                return Err(diagnostic(
                    "E_PARSE",
                    format!("the {field} of `{op}` is a basis name, as in `e1`"),
                    self.peek().span,
                ));
            }
            fields.push((field, WireValue::Coordinate(self.name()?.0)));
        }
        Ok(fields)
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
        let tag = self.indexed_tag()?;
        self.expect("(")?;
        let unknown = || diagnostic("E_TYPE", "unknown indexed primitive contract", span);
        let Some(family) = indexed::primitive_family(&tag) else {
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
            "dim" => vec![("domain", WireValue::ObjectType(self.indexed_object_type()?))],
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
            // Stage 5 (#806): the spectrum or the branch that an observation
            // embeds, and the element of `A[t]` it observes, are named
            // explicitly, `spectrum =`, `element =` and `branch =`.
            "annihilates" => self.indexed_spectral_element("annihilates")?,
            "action_entry" => {
                let mut fields = self.indexed_spectral_element("action_entry")?;
                fields.extend(self.indexed_basis_entry("action_entry")?);
                fields
            }
            "on_branch" => {
                let mut fields = self.indexed_paths(&["map_family", "line"])?;
                fields.push(self.indexed_branch_field("on_branch")?);
                fields
            }
            // The families in wire order, as for `differential`: the
            // cotangent family before the line.
            "branch_differential" => {
                let mut fields = self.indexed_paths(&["map_family", "cotangent", "line"])?;
                fields.push(self.indexed_branch_field("branch_differential")?);
                fields
            }
            "branch_projector" => {
                let mut fields = self.indexed_paths(&["map_family", "line"])?;
                fields.push(self.indexed_branch_field("branch_projector")?);
                fields.extend(self.indexed_basis_entry("branch_projector")?);
                fields
            }
            "average_at" => {
                let mut fields = self.indexed_paths(&["map_family", "line"])?;
                let average = self.indexed_selection(
                    "average_at",
                    "average",
                    "an explicit transition average",
                )?;
                fields.push(("average", WireValue::Path(average)));
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
        // The kernel rejects the same names, but it has no span for the name.
        if !super::INDEXED_SPELLINGS.contains(&name.as_str()) {
            check_binding_name(&name, name_span)?;
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
                let capabilities = self.delimited_list("(", ")", |parser| {
                    let token = parser.peek().clone();
                    match parser.indexed_tag()?.as_str() {
                        "origin" => Ok(indexed::Capability::Origin),
                        // The wire token stays `dimension` (#778).
                        "dim" => Ok(indexed::Capability::Dimension),
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
                let parents = self.delimited_list("(", ")", Self::type_path)?;
                self.expect(";")?;
                self.expect("domain")?;
                let domain = self.delimited_list("(", ")", Self::type_path)?;
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
                let parameters = self.delimited_list("(", ")", Self::indexed_parameter)?;
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
                    "free_module" => indexed::FamilyRepresentation::FreeModule,
                    "endomorphism" => indexed::FamilyRepresentation::Endomorphism,
                    "spectrum" => indexed::FamilyRepresentation::Spectrum,
                    "branch" => indexed::FamilyRepresentation::Branch,
                    "transition_average" => indexed::FamilyRepresentation::TransitionAverage,
                    "model" => indexed::FamilyRepresentation::Model,
                    "calibration" => indexed::FamilyRepresentation::Calibration,
                    "dataset" => indexed::FamilyRepresentation::Dataset,
                    "comparison" => indexed::FamilyRepresentation::Comparison,
                    _ => {
                        return Err(diagnostic(
                            "E_TYPE",
                            "family representation requires token, point, morphism, relative, smooth, cotangent, tangent, tape, metric_form, free_module, endomorphism, spectrum, branch, transition_average, frame, frame_vector, frame_covector, frame_map, reading, physical_metric, model, calibration, dataset or comparison",
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
                    self.delimited_list("(", ")", Self::indexed_constraint)?
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
            "free_module" => self.indexed_free_module()?,
            "average" => self.indexed_average()?,
            "convention" => {
                self.expect("=")?;
                let span = self.peek().span;
                match self.indexed_tag()?.as_str() {
                    "hbar_one" => DeclarationBody::Convention {
                        value: indexed::ConventionKind::HbarOne,
                    },
                    _ => {
                        return Err(diagnostic(
                            "E_TYPE",
                            "a convention is `hbar_one`, the one convention of the profile",
                            span,
                        ));
                    }
                }
            }
            "model" => self.indexed_model()?,
            "calibration" => self.indexed_calibration()?,
            "dataset" => self.indexed_dataset()?,
            "comparison" => self.indexed_comparison()?,
            "endomorphism" => self.indexed_endomorphism()?,
            "spectrum" => self.indexed_spectrum()?,
            "branch" => self.indexed_branch()?,
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
                let forward = self.delimited_list("(", ")", Self::poly_binding)?;
                self.expect("inverse")?;
                let inverse = self.delimited_list("(", ")", Self::poly_binding)?;
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
        let generators = self.delimited_list("[", "]", |p| Ok(p.name()?.0))?;
        let relations = if self.consume("relations") {
            self.delimited_list("(", ")", Self::polynomial)?
        } else {
            Vec::new()
        };
        let (base, bindings) = if self.consume("over") {
            let base = self.type_path()?;
            let bindings = if self.consume("by") {
                self.delimited_list("(", ")", Self::poly_binding)?
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
        let coordinates = self.delimited_list("[", "]", |p| Ok(p.name()?.0))?;
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

    /// `: Family<X, Y, S> = pullback(y -> p, ...) | identity | structure`, and
    /// the other definitions: `first`, `second`, `restrict(φ)`,
    /// `trace_power(H, k)` and `char_coefficient(S, i)`.
    fn indexed_morphism(&mut self) -> Result<DeclarationBody, Diagnostic> {
        let (family, indices) = self.indexed_application()?;
        let span = self.peek().span;
        let definition = match self.indexed_tag()?.as_str() {
            "pullback" => indexed::MorphismDefinition::Pullback {
                images: self.delimited_list("(", ")", Self::poly_binding)?,
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
            // Stage 5 (#806): the invariants of an endomorphism and of a
            // spectrum, with their natural argument as written.
            "trace_power" => {
                self.expect("(")?;
                let endomorphism = self.type_path()?;
                self.expect(",")?;
                let power = self.natural_literal("trace_power", "power")?;
                self.expect(")")?;
                indexed::MorphismDefinition::TracePower {
                    endomorphism,
                    power,
                }
            }
            "char_coefficient" => {
                self.expect("(")?;
                let spectrum = self.type_path()?;
                self.expect(",")?;
                let index = self.natural_literal("char_coefficient", "index")?;
                self.expect(")")?;
                indexed::MorphismDefinition::CharCoefficient { spectrum, index }
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
                    .delimited_list("(", ")", |p| p.delimited_list("(", ")", Self::polynomial))?,
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
        let columns = self.delimited_list("(", ")", |p| {
            if !p.peek().is("(") {
                return Err(diagnostic(
                    "E_PARSE",
                    "a frame column is a parenthesized tuple of entries, as in `columns((1, 0), (0, 1))`",
                    p.peek().span,
                ));
            }
            p.delimited_list("(", ")", Self::polynomial)
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
        let quantities = self.delimited_list("(", ")", |p| {
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
                rows: self.delimited_list("(", ")", |p| {
                    p.delimited_list("(", ")", Self::scale_monomial)
                })?,
            },
            "normalized" => indexed::PhysicalGram::Normalized {
                scales: self.delimited_list("(", ")", |p| {
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

    /// `: Family<X> = basis(e1, …)`: a free module with its named ordered
    /// basis, in source order. The kernel checks the names and the rank.
    fn indexed_free_module(&mut self) -> Result<DeclarationBody, Diagnostic> {
        let (family, indices) = self.indexed_application()?;
        self.expect("basis")?;
        let basis = self.delimited_list("(", ")", |p| Ok(p.name()?.0))?;
        Ok(DeclarationBody::FreeModule {
            family,
            indices,
            basis,
        })
    }

    /// `: Family<X> = rows((p, …), …) of V [symmetric]`: an endomorphism of
    /// the free module `V`, each row a parenthesized tuple of polynomials in
    /// the coordinates of `X`, in source order. `symmetric` is the claim
    /// H = Hᵀ, which the kernel checks; without it the claim is not made.
    fn indexed_endomorphism(&mut self) -> Result<DeclarationBody, Diagnostic> {
        let (family, indices) = self.indexed_application()?;
        self.expect("rows")?;
        let rows = self.delimited_list("(", ")", |p| {
            if !p.peek().is("(") {
                return Err(diagnostic(
                    "E_PARSE",
                    "an endomorphism row is a parenthesized tuple of entries, as in `rows((x, y), (y, -x))`",
                    p.peek().span,
                ));
            }
            p.delimited_list("(", ")", Self::polynomial)
        })?;
        self.expect("of")?;
        let module = self.type_path()?;
        let symmetric = self.consume("symmetric");
        Ok(DeclarationBody::Endomorphism {
            family,
            indices,
            module,
            rows,
            symmetric,
        })
    }

    /// `: Family<X> = eigen(H, t)`: the spectrum of the endomorphism `H`,
    /// whose fiber coordinate is named `t`. The wire carries no certificate.
    fn indexed_spectrum(&mut self) -> Result<DeclarationBody, Diagnostic> {
        let (family, indices) = self.indexed_application()?;
        self.expect("eigen")?;
        self.expect("(")?;
        let endomorphism = self.type_path()?;
        self.expect(",")?;
        let fiber = self.name()?.0;
        self.expect(")")?;
        Ok(DeclarationBody::Spectrum {
            family,
            indices,
            endomorphism,
            fiber,
        })
    }

    /// `: Family<X> = simple(S, localize = g, witness = W, exponent = e)`: a
    /// simple branch of the spectrum `S` on the principal open of `g`, with
    /// its gap witness `W` and the exponent `e`, each named explicitly and
    /// in this order. The wire carries no quotient.
    fn indexed_branch(&mut self) -> Result<DeclarationBody, Diagnostic> {
        let (family, indices) = self.indexed_application()?;
        self.expect("simple")?;
        self.expect("(")?;
        let spectrum = self.type_path()?;
        self.indexed_keyword("simple", "localize", "an explicit localization")?;
        let localize = self.polynomial()?;
        self.indexed_keyword("simple", "witness", "an explicit gap witness")?;
        let witness = self.polynomial()?;
        self.indexed_keyword("simple", "exponent", "an explicit exponent")?;
        let exponent = self.natural_literal("simple", "exponent")?;
        self.expect(")")?;
        Ok(DeclarationBody::Branch {
            family,
            indices,
            spectrum,
            localize,
            witness,
            exponent,
        })
    }

    /// `: Family<X> = transition_average(B, from = i, to = j) = ratio(N, D)`
    /// (Stage 6, #841): the dephased transition average of the branch `B` from
    /// the basis vector `i` to `j`, with its closed form N/D, two polynomials
    /// in the coordinates of `X`, written as `ratio(…)` in the style of
    /// `frac(…)`: the language has no `/`. The wire carries no certificate.
    fn indexed_average(&mut self) -> Result<DeclarationBody, Diagnostic> {
        let (family, indices) = self.indexed_application()?;
        self.expect("transition_average")?;
        self.expect("(")?;
        let branch = self.type_path()?;
        self.indexed_keyword("transition_average", "from", "an explicit source vector")?;
        let from = self.basis_word("transition_average", "source vector")?;
        self.indexed_keyword("transition_average", "to", "an explicit target vector")?;
        let to = self.basis_word("transition_average", "target vector")?;
        self.expect(")")?;
        self.expect("=")?;
        if !(self.peek().is("ratio") && self.second_is("(")) {
            return Err(diagnostic(
                "E_PARSE",
                "the closed form of `transition_average` is `ratio(N, D)` of two polynomials",
                self.peek().span,
            ));
        }
        self.advance();
        self.advance();
        let numerator = self.polynomial()?;
        self.expect(",")?;
        let denominator = self.polynomial()?;
        self.expect(")")?;
        Ok(DeclarationBody::TransitionAverage {
            family,
            indices,
            branch,
            from,
            to,
            numerator,
            denominator,
        })
    }

    /// A basis name that `operation` takes as `what`, as written in the
    /// `basis(…)` of a free module.
    fn basis_word(&mut self, operation: &str, what: &str) -> Result<String, Diagnostic> {
        if !matches!(self.peek().kind, TokenKind::Name(_)) {
            return Err(diagnostic(
                "E_PARSE",
                format!("the {what} of `{operation}` is a basis name, as in `e1`"),
                self.peek().span,
            ));
        }
        Ok(self.name()?.0)
    }

    /// `keyword =`: the first field of `operation`, named explicitly.
    fn indexed_first_keyword(
        &mut self,
        operation: &str,
        keyword: &str,
        what: &str,
    ) -> Result<(), Diagnostic> {
        let token = self.peek().clone();
        if !(token.is(keyword) && self.second_is("=")) {
            return Err(diagnostic(
                "E_PARSE",
                format!("`{operation}` needs {what}: write `{keyword} = …`"),
                token.span,
            ));
        }
        self.advance();
        self.expect("=")?;
        Ok(())
    }

    /// A string literal that `operation` takes as `what` (Stage 6, #841): text
    /// between double quotes of printable ASCII characters other than `\` and
    /// `"`, at most `recordTextBytes` bytes, which the wire carries as written
    /// and the kernel checks again. Only the regime of a model, the reference
    /// and the revision of a calibration and the fingerprint of a comparison
    /// take a string literal; no escape is decoded, so no escape reaches a
    /// diagnostic or a terminal.
    fn stage6_text(&mut self, operation: &str, what: &str) -> Result<String, Diagnostic> {
        let token = self.peek().clone();
        if !matches!(token.kind, TokenKind::Text) {
            return Err(diagnostic(
                "E_PARSE",
                format!("the {what} of `{operation}` is a string literal, as in \"…\""),
                token.span,
            ));
        }
        self.advance();
        let raw =
            &self.text[token.span.start - self.text_offset..token.span.end - self.text_offset];
        let closed = raw.len() >= 2 && raw.ends_with('"');
        let inner = if closed {
            &raw[1..raw.len() - 1]
        } else {
            &raw[1..]
        };
        if !closed
            || !inner
                .chars()
                .all(|c| (' '..='~').contains(&c) && c != '\\' && c != '"')
        {
            return Err(diagnostic(
                "E_PARSE",
                format!(
                    "the {what} of `{operation}` holds printable ASCII characters other than `\\` between \
                     double quotes"
                ),
                token.span,
            ));
        }
        let limit = crate::limits::MAX_RECORD_TEXT_BYTES;
        if inner.len() > limit {
            return Err(diagnostic(
                "E_LIMIT",
                format!(
                    "the {what} of `{operation}` has at most {limit} bytes (`recordTextBytes`), but this one has {}",
                    inner.len()
                ),
                token.span,
            ));
        }
        Ok(inner.to_string())
    }

    /// A rational literal: an unsigned decimal literal or `frac(i, n)`, with
    /// an optional `-` before it. The kernel evaluates it as a constant.
    fn rational(&mut self) -> Result<indexed::PolyExpr, Diagnostic> {
        let negative = self.consume("-");
        let value = if self.at_fraction() {
            self.fraction()?
        } else if matches!(self.peek().kind, TokenKind::Number(_)) {
            indexed::PolyExpr::Natural {
                value: self.poly_literal()?,
            }
        } else {
            return Err(diagnostic(
                "E_PARSE",
                "a rational number is an integer literal or `frac(i, n)`, with an optional `-`",
                self.peek().span,
            ));
        };
        Ok(if negative {
            indexed::PolyExpr::Neg {
                operand: Box::new(value),
            }
        } else {
            value
        })
    }

    /// `measured(v, u = w)`: a measured value and its standard uncertainty,
    /// two rational literals.
    fn measured(
        &mut self,
        operation: &str,
    ) -> Result<(indexed::PolyExpr, indexed::PolyExpr), Diagnostic> {
        if !self.peek().is("measured") {
            return Err(diagnostic(
                "E_PARSE",
                format!("`{operation}` needs a measured value: write `measured(v, u = w)`"),
                self.peek().span,
            ));
        }
        self.advance();
        self.expect("(")?;
        let value = self.rational()?;
        self.indexed_keyword("measured", "u", "an explicit standard uncertainty")?;
        let uncertainty = self.rational()?;
        self.expect(")")?;
        Ok((value, uncertainty))
    }

    /// `: Family<X> = model(hamiltonian = H, reading = r, convention = c,
    /// prepare = i, observe = j, predicts = A, regime = assume("…"))` (Stage
    /// 6, #841): every field named explicitly, in this order.
    fn indexed_model(&mut self) -> Result<DeclarationBody, Diagnostic> {
        let (family, indices) = self.indexed_application()?;
        self.expect("model")?;
        self.expect("(")?;
        self.indexed_first_keyword("model", "hamiltonian", "an explicit hamiltonian")?;
        let hamiltonian = self.type_path()?;
        let reading = self.indexed_selection("model", "reading", "an explicit reading")?;
        let convention = self.indexed_selection("model", "convention", "an explicit convention")?;
        self.indexed_keyword("model", "prepare", "an explicit prepared vector")?;
        let prepare = self.basis_word("model", "prepared vector")?;
        self.indexed_keyword("model", "observe", "an explicit observed vector")?;
        let observe = self.basis_word("model", "observed vector")?;
        let predicts =
            self.indexed_selection("model", "predicts", "an explicit predicted average")?;
        self.indexed_keyword("model", "regime", "an explicit regime")?;
        if !self.peek().is("assume") {
            return Err(diagnostic(
                "E_PARSE",
                "the regime of `model` is a recorded assumption: write `regime = assume(\"…\")`",
                self.peek().span,
            ));
        }
        self.advance();
        self.expect("(")?;
        let regime = self.stage6_text("model", "regime")?;
        self.expect(")")?;
        self.expect(")")?;
        Ok(DeclarationBody::Model {
            family,
            indices,
            hamiltonian,
            reading,
            convention,
            prepare,
            observe,
            predicts,
            regime,
        })
    }

    /// `: Family<X> = calibrate(x = measured(v, u = w), …, method = m,
    /// reference = "…", revision = "…")` (Stage 6, #841): the calibrated
    /// coordinates in source order, then the method `type_a` or `type_b`,
    /// the reference and the revision. `method` ends the coordinates.
    fn indexed_calibration(&mut self) -> Result<DeclarationBody, Diagnostic> {
        let (family, indices) = self.indexed_application()?;
        self.expect("calibrate")?;
        self.expect("(")?;
        let mut parameters = Vec::new();
        while !(self.peek().is("method") && self.second_is("=")) {
            let coordinate = self.coordinate_name()?;
            self.expect("=")?;
            let (value, uncertainty) = self.measured("calibrate")?;
            parameters.push(indexed::Calibrated {
                coordinate,
                value,
                uncertainty,
            });
            if !self.consume(",") {
                return Err(diagnostic(
                    "E_PARSE",
                    "`calibrate` needs an explicit method after its coordinates: write `, method = …`",
                    self.peek().span,
                ));
            }
        }
        self.indexed_first_keyword("calibrate", "method", "an explicit method")?;
        let span = self.peek().span;
        let method = match self.indexed_tag()?.as_str() {
            "type_a" => indexed::CalibrationMethod::TypeA,
            "type_b" => indexed::CalibrationMethod::TypeB,
            _ => {
                return Err(diagnostic(
                    "E_TYPE",
                    "the method of a calibration is `type_a` or `type_b`",
                    span,
                ));
            }
        };
        self.indexed_keyword("calibrate", "reference", "an explicit reference")?;
        let reference = self.stage6_text("calibrate", "reference")?;
        self.indexed_keyword("calibrate", "revision", "an explicit revision")?;
        let revision = self.stage6_text("calibrate", "revision")?;
        self.expect(")")?;
        Ok(DeclarationBody::Calibration {
            family,
            indices,
            parameters,
            method,
            reference,
            revision,
        })
    }

    /// `: Family<X> = measure(model = M, calibration = K, coverage = k,
    /// points = [(x = v, …, value = measured(v, u = w)), …])` (Stage 6, #841):
    /// each point gives coordinates and then its measured value; `value` ends
    /// the coordinates. A dataset of more than `datasetPoints` points is
    /// `E_LIMIT`, as in the kernel.
    fn indexed_dataset(&mut self) -> Result<DeclarationBody, Diagnostic> {
        let (family, indices) = self.indexed_application()?;
        self.expect("measure")?;
        self.expect("(")?;
        self.indexed_first_keyword("measure", "model", "an explicit model")?;
        let model = self.type_path()?;
        let calibration =
            self.indexed_selection("measure", "calibration", "an explicit calibration")?;
        self.indexed_keyword("measure", "coverage", "an explicit coverage factor")?;
        let coverage = self.rational()?;
        self.indexed_keyword("measure", "points", "explicit points")?;
        let open = self.peek().span;
        let points = self.delimited_list("[", "]", |p| {
            if !p.peek().is("(") {
                return Err(diagnostic(
                    "E_PARSE",
                    "a point of a dataset is a parenthesized tuple, as in `(x = 1, value = measured(v, u = w))`",
                    p.peek().span,
                ));
            }
            p.advance();
            let mut coordinates = Vec::new();
            // `value = measured(…)` ends the coordinates; a coordinate may be
            // named `value`, since a rational never begins with `measured`.
            while !(p.peek().is("value")
                && p.second_is("=")
                && p.tokens.get(p.position + 2).is_some_and(|token| token.is("measured")))
            {
                let coordinate = p.coordinate_name()?;
                p.expect("=")?;
                coordinates.push(indexed::PointCoordinate {
                    coordinate,
                    value: p.rational()?,
                });
                if !p.consume(",") {
                    return Err(diagnostic(
                        "E_PARSE",
                        "a point of a dataset ends with its measured value: write `, value = measured(v, u = w)`",
                        p.peek().span,
                    ));
                }
            }
            p.indexed_first_keyword("measure", "value", "the measured value of each point")?;
            let (value, uncertainty) = p.measured("measure")?;
            p.expect(")")?;
            Ok(indexed::DataPoint {
                coordinates,
                value,
                uncertainty,
            })
        })?;
        if points.len() > crate::limits::MAX_DATASET_POINTS {
            return Err(diagnostic(
                "E_LIMIT",
                format!(
                    "a dataset has at most {} points (`datasetPoints`), but this one has {}",
                    crate::limits::MAX_DATASET_POINTS,
                    points.len()
                ),
                open.through(self.previous().span),
            ));
        }
        self.expect(")")?;
        Ok(DeclarationBody::Dataset {
            family,
            indices,
            model,
            calibration,
            coverage,
            points,
        })
    }

    /// `: Family<X> = compare(D, calibration = K, fingerprint = "…", verdict = v)`
    /// (Stage 6, #841): the dataset, its calibration, the recorded fingerprint
    /// of the calibration, and the recorded verdict `consistent` or
    /// `inconsistent`.
    fn indexed_comparison(&mut self) -> Result<DeclarationBody, Diagnostic> {
        let (family, indices) = self.indexed_application()?;
        self.expect("compare")?;
        self.expect("(")?;
        let dataset = self.type_path()?;
        let calibration =
            self.indexed_selection("compare", "calibration", "an explicit calibration")?;
        self.indexed_keyword(
            "compare",
            "fingerprint",
            "the recorded fingerprint of its calibration",
        )?;
        let fingerprint = self.stage6_text("compare", "fingerprint")?;
        self.indexed_keyword("compare", "verdict", "an explicit verdict")?;
        let span = self.peek().span;
        let verdict = match self.indexed_tag()?.as_str() {
            "consistent" => indexed::Verdict::Consistent,
            "inconsistent" => indexed::Verdict::Inconsistent,
            _ => {
                return Err(diagnostic(
                    "E_TYPE",
                    "the verdict of a comparison is `consistent` or `inconsistent`",
                    span,
                ));
            }
        };
        self.expect(")")?;
        Ok(DeclarationBody::Comparison {
            family,
            indices,
            dataset,
            calibration,
            fingerprint,
            verdict,
        })
    }

    /// `, keyword =`: the start of a field that `operation` names explicitly.
    /// A missing keyword is `E_PARSE` naming it, at the token where the
    /// field was expected. No default is ever selected. When the keyword is
    /// written but the comma before it is missing, the diagnostic asks for
    /// the comma; when the keyword was read as a positional argument, because
    /// an argument before it is missing, the diagnostic says so at the
    /// keyword.
    fn indexed_keyword(
        &mut self,
        operation: &str,
        keyword: &str,
        what: &str,
    ) -> Result<(), Diagnostic> {
        let token = self.peek().clone();
        if token.is(keyword) && self.second_is("=") {
            return Err(diagnostic(
                "E_PARSE",
                format!("expected `,` before `{keyword}` in `{operation}`"),
                token.span,
            ));
        }
        if token.is("=") && self.previous().is(keyword) {
            return Err(diagnostic(
                "E_PARSE",
                format!(
                    "`{operation}` is missing an argument before `{keyword} = …`; \
                     `{keyword}` was read in its place"
                ),
                self.previous().span,
            ));
        }
        if !(self.consume(",") && self.consume(keyword)) {
            return Err(diagnostic(
                "E_PARSE",
                format!("`{operation}` needs {what}: write `{keyword} = …`"),
                token.span,
            ));
        }
        self.expect("=")?;
        Ok(())
    }

    /// `, keyword = path` (`indexed_keyword`): the metric or evidence that
    /// `flat` and `sharp` name explicitly, the reading that `interpret`
    /// names, the frames of the frame primitives, and the spectrum or branch
    /// of the spectral observations.
    fn indexed_selection(
        &mut self,
        operation: &str,
        keyword: &str,
        what: &str,
    ) -> Result<TypePath, Diagnostic> {
        self.indexed_keyword(operation, keyword, what)?;
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
        self.peek().is("frac") && self.second_is("(")
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
        ("dim", "dim((Scheme, QQ))"),
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
        (
            "annihilates",
            "annihilates(Smooth, spectrum = S, element = t - 2)",
        ),
        (
            "action_entry",
            "action_entry(Smooth, spectrum = S, element = t - 2, e1, e2)",
        ),
        ("on_branch", "on_branch(Smooth, Line, branch = B)"),
        (
            "branch_differential",
            "branch_differential(Smooth, Cotangent, Line, branch = B)",
        ),
        (
            "branch_projector",
            "branch_projector(Smooth, Line, branch = B, e1, e2)",
        ),
        ("average_at", "average_at(Smooth, Line, average = A)"),
    ];

    /// A package module, for the checks that need more than one item.
    fn parse_module(source: &str) -> Result<(), Diagnostic> {
        parse_module_source(
            SourceInput {
                source,
                file: "module.vast",
                offset: 0,
            },
            vec![],
            true,
            None,
        )
        .map(|_| ())
    }

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
            // the diagnostic says that an argument before `source =` is
            // missing.
            (
                "indexed primitive p = frame_matrix(Smooth, source = b, target = c);",
                "E_PARSE",
                "`frame_matrix` is missing an argument before `source = …`; `source` was read in its place",
                "source",
                "source = b,",
            ),
            // A comma that is missing before a keyword is asked for.
            (
                "indexed primitive p = frame_matrix(Smooth, FrameMap source = b, target = c);",
                "E_PARSE",
                "expected `,` before `source` in `frame_matrix`",
                "source",
                "source = b,",
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

    /// Asserts that `source` is rejected with exactly `code` and `message` at
    /// the token `place`, where `context` starts with `place`, occurs once in
    /// `source` and starts at the place, so a `,` or `)` place is the one
    /// meant.
    #[track_caller]
    fn assert_rejected_at(source: &str, code: &str, message: &str, place: &str, context: &str) {
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

    /// A parsed declaration serializes to the wire and reads back as itself,
    /// spans included.
    #[track_caller]
    fn assert_round_trip(declaration: &indexed::Declaration) {
        let wire = serde_json::to_value(declaration).unwrap();
        let read: indexed::Declaration = serde_json::from_value(wire).unwrap();
        assert_eq!(&read, declaration);
    }

    fn sum(terms: Vec<Value>) -> Value {
        json!({ "op": "sum", "terms": terms })
    }

    fn product(factors: Vec<Value>) -> Value {
        json!({ "op": "product", "factors": factors })
    }

    fn neg(operand: Value) -> Value {
        json!({ "op": "neg", "operand": operand })
    }

    fn pow(base: Value, exponent: &str) -> Value {
        json!({ "op": "pow", "base": base, "exponent": exponent })
    }

    /// The observations of Stage 5 (#806), each with the binding that the
    /// kernel's protocol-9 decoder reads: the positional fields, the
    /// spectrum or branch and the element under their keywords, and the row
    /// and the column as basis names. The positional families come in wire
    /// order, so `branch_differential` lists the cotangent family before the
    /// line, as `differential` does. Every one is algebraic, so it selects
    /// protocol 9.
    #[test]
    fn every_spectral_primitive_parses_to_its_wire_record() {
        let shifted = || sum(vec![coordinate("t"), neg(n("2"))]);
        let cases: Vec<(&str, Value)> = vec![
            (
                "indexed primitive ann = annihilates(Smooth, spectrum = S, element = t - 2);",
                json!({ "op": "annihilates", "map_family": p("Smooth"), "spectrum": p("S"),
                    "element": shifted() }),
            ),
            (
                "indexed primitive act = action_entry(Smooth, spectrum = S, element = t - 2, e1, e2);",
                json!({ "op": "action_entry", "map_family": p("Smooth"), "spectrum": p("S"),
                    "element": shifted(), "row": "e1", "column": "e2" }),
            ),
            (
                "indexed primitive on = on_branch(Smooth, Line, branch = B);",
                json!({ "op": "on_branch", "map_family": p("Smooth"), "line": p("Line"),
                    "branch": p("B") }),
            ),
            (
                "indexed primitive dl = branch_differential(Smooth, Cotangent, Line, branch = B);",
                json!({ "op": "branch_differential", "map_family": p("Smooth"),
                    "cotangent": p("Cotangent"), "line": p("Line"), "branch": p("B") }),
            ),
            (
                "indexed primitive pr = branch_projector(Smooth, Line, branch = B, e1, e2);",
                json!({ "op": "branch_projector", "map_family": p("Smooth"), "line": p("Line"),
                    "branch": p("B"), "row": "e1", "column": "e2" }),
            ),
            // Qualified paths; an element in the chart coordinates and the
            // fiber coordinate, kept as written; a diagonal entry.
            (
                "indexed primitive ann = annihilates(geo::Smooth, spectrum = spectral::S, element = frac(-1, 2) * t^2 + x * t + 1);",
                json!({ "op": "annihilates", "map_family": { "path": ["geo", "Smooth"] },
                    "spectrum": { "path": ["spectral", "S"] },
                    "element": sum(vec![
                        product(vec![fraction("-1", "2"), pow(coordinate("t"), "2")]),
                        product(vec![coordinate("x"), coordinate("t")]),
                        n("1"),
                    ]) }),
            ),
            (
                "indexed primitive act = action_entry(Smooth, spectrum = S, element = 0, e2, e2);",
                json!({ "op": "action_entry", "map_family": p("Smooth"), "spectrum": p("S"),
                    "element": n("0"), "row": "e2", "column": "e2" }),
            ),
            (
                "indexed primitive dl = branch_differential(geo::Smooth, geo::Cotangent, geo::Line, branch = super::B);",
                json!({ "op": "branch_differential",
                    "map_family": { "path": ["geo", "Smooth"] },
                    "cotangent": { "path": ["geo", "Cotangent"] },
                    "line": { "path": ["geo", "Line"] }, "branch": { "path": ["super", "B"] } }),
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
            assert_round_trip(&declaration);
        }
        // The source order is the wire order: the cotangent family precedes
        // the line, as for `differential`.
        let binding = parse_binding(
            "indexed primitive dl = branch_differential(Smooth, Cotangent, Line, branch = B);",
        )
        .unwrap();
        let order: Vec<&str> = binding.fields().map(|(name, _)| name).collect();
        assert_eq!(order, ["map_family", "cotangent", "line", "branch"]);
    }

    /// Malformed observations are rejected at the offending token: a missing
    /// keyword, a row or column that is no basis name, and a wrong number of
    /// fields. The polynomial limits of the element are those of every
    /// polynomial.
    #[test]
    fn malformed_spectral_primitives_are_rejected_at_their_place() {
        let long = "9".repeat(crate::limits::MAX_ALGEBRA_DIGITS + 1);
        let long_element = format!(
            "indexed primitive p = annihilates(Smooth, spectrum = S, element = t - {long});"
        );
        let spectrum = "`annihilates` needs an explicit spectrum: write `spectrum = …`";
        let element = "`annihilates` needs an explicit element: write `element = …`";
        let branch = |op: &str| format!("`{op}` needs an explicit branch: write `branch = …`");
        let on_branch = branch("on_branch");
        let differential = branch("branch_differential");
        let projector = branch("branch_projector");
        // A keyword read as a positional argument: the argument before it is
        // missing.
        let misread = |op: &str, keyword: &str| {
            format!(
                "`{op}` is missing an argument before `{keyword} = …`; `{keyword}` was read in its place"
            )
        };
        let misread_branch = misread("on_branch", "branch");
        let misread_differential = misread("branch_differential", "branch");
        let misread_spectrum = misread("annihilates", "spectrum");
        let cases: Vec<(&str, &str, &str, &str, &str)> = vec![
            // The spectrum, then the element, each under its keyword.
            (
                "indexed primitive p = annihilates(Smooth, S, element = t);",
                "E_PARSE",
                spectrum,
                ",",
                ", S,",
            ),
            (
                "indexed primitive p = annihilates(Smooth, element = t, spectrum = S);",
                "E_PARSE",
                spectrum,
                ",",
                ", element",
            ),
            (
                "indexed primitive p = annihilates(Smooth, spectrum = S);",
                "E_PARSE",
                element,
                ")",
                ");",
            ),
            (
                "indexed primitive p = annihilates(Smooth, spectrum = S, t - 2);",
                "E_PARSE",
                element,
                ",",
                ", t - 2",
            ),
            (
                "indexed primitive p = annihilates(Smooth, spectrum = S, element t);",
                "E_PARSE",
                "expected `=`, found `t`",
                "t",
                "t);",
            ),
            (
                "indexed primitive p = annihilates(Smooth, spectrum = S, element = );",
                "E_PARSE",
                "expected an identifier",
                ")",
                ");",
            ),
            (
                &long_element,
                "E_LIMIT",
                "polynomial literals have at most 64 decimal digits",
                &long,
                &long,
            ),
            (
                "indexed primitive p = annihilates(Smooth, spectrum = S, element = t, e1);",
                "E_PARSE",
                "expected `)`, found `,`",
                ",",
                ", e1",
            ),
            // The row and the column are basis names, positional.
            (
                "indexed primitive p = action_entry(Smooth, spectrum = S, element = t, e1);",
                "E_PARSE",
                "expected `,`, found `)`",
                ")",
                ");",
            ),
            (
                "indexed primitive p = action_entry(Smooth, spectrum = S, element = t, 0, 1);",
                "E_PARSE",
                "the row of `action_entry` is a basis name, as in `e1`",
                "0",
                "0, 1",
            ),
            (
                "indexed primitive p = action_entry(Smooth, spectrum = S, element = t, e1, -e2);",
                "E_PARSE",
                "the column of `action_entry` is a basis name, as in `e1`",
                "-",
                "-e2",
            ),
            (
                "indexed primitive p = action_entry(Smooth, spectrum = S, element = t, row = e1, e2);",
                "E_PARSE",
                "expected `,`, found `=`",
                "=",
                "= e1",
            ),
            (
                "indexed primitive p = action_entry(Smooth, spectrum = S, element = t, V::e1, e2);",
                "E_PARSE",
                "expected `,`, found `::`",
                "::",
                "::e1",
            ),
            (
                "indexed primitive p = action_entry(Smooth, spectrum = S, element = t, e1, e2, e3);",
                "E_PARSE",
                "expected `)`, found `,`",
                ",",
                ", e3",
            ),
            // The branch, under its keyword, after the families.
            (
                "indexed primitive p = on_branch(Smooth, Line, B);",
                "E_PARSE",
                &on_branch,
                ",",
                ", B)",
            ),
            // Without its line, `branch` is read as the line, and the
            // diagnostic says that an argument before `branch =` is missing.
            (
                "indexed primitive p = on_branch(Smooth, branch = B);",
                "E_PARSE",
                &misread_branch,
                "branch",
                "branch = B",
            ),
            // Without its smooth family, `spectrum` is read as the family.
            (
                "indexed primitive p = annihilates(spectrum = S, element = t);",
                "E_PARSE",
                &misread_spectrum,
                "spectrum",
                "spectrum = S",
            ),
            // A comma that is missing before a keyword is asked for.
            (
                "indexed primitive p = annihilates(Smooth, spectrum = S element = t);",
                "E_PARSE",
                "expected `,` before `element` in `annihilates`",
                "element",
                "element = t",
            ),
            (
                "indexed primitive p = on_branch(Smooth, Line, branch = B, e1);",
                "E_PARSE",
                "expected `)`, found `,`",
                ",",
                ", e1",
            ),
            (
                "indexed primitive p = branch_differential(Smooth, Cotangent, Line);",
                "E_PARSE",
                &differential,
                ")",
                ");",
            ),
            (
                "indexed primitive p = branch_differential(Smooth, Cotangent, branch = B);",
                "E_PARSE",
                &misread_differential,
                "branch",
                "branch = B",
            ),
            (
                "indexed primitive p = branch_differential(Smooth, Line, branch = B);",
                "E_PARSE",
                &misread_differential,
                "branch",
                "branch = B",
            ),
            (
                "indexed primitive p = branch_projector(Smooth, Line, branch = B);",
                "E_PARSE",
                "expected `,`, found `)`",
                ")",
                ");",
            ),
            (
                "indexed primitive p = branch_projector(Smooth, Line, e1, e2, branch = B);",
                "E_PARSE",
                &projector,
                ",",
                ", e1",
            ),
            (
                "indexed primitive p = branch_projector(Smooth, Line, branch = B, e1, 2);",
                "E_PARSE",
                "the column of `branch_projector` is a basis name, as in `e1`",
                "2",
                "2)",
            ),
        ];
        for (source, code, message, place, context) in cases {
            assert_rejected_at(source, code, message, place, context);
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

    /// The source and the wire spell the op and the capability of `dim(…)` as
    /// `dim` (#778), and the source `dimension` is neither a contract nor a
    /// capability.
    #[test]
    fn the_dimension_contract_and_capability_are_spelled_dim() {
        let binding = parse_binding("indexed primitive size = dim((Scheme, QQ));").unwrap();
        assert_eq!(binding.op(), "dim");
        let error = parse_binding("indexed primitive size = dimension((Scheme, QQ));")
            .expect_err("`dimension` is no contract");
        assert_eq!(
            (error.code.as_str(), error.message.as_str()),
            ("E_TYPE", "unknown indexed primitive contract")
        );
        let declaration = parse_declaration(
            "indexed implementation Grid(QQ, affine_descriptor) capabilities(origin, dim);",
        )
        .unwrap();
        let wire = serde_json::to_value(&declaration).unwrap();
        assert_eq!(wire["capabilities"], json!(["origin", "dim"]));
        let source =
            "indexed implementation Grid(QQ, affine_descriptor) capabilities(origin, dimension);";
        let error = parse_declaration(source).expect_err("`dimension` is no capability");
        assert_eq!(
            (error.code.as_str(), error.message.as_str()),
            ("E_TYPE", "unsupported implementation capability")
        );
        assert_eq!(&source[error.span.start..error.span.end], "dimension");
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
                "family representation requires token, point, morphism, relative, smooth, cotangent, tangent, tape, metric_form, free_module, endomorphism, spectrum, branch, transition_average, frame, frame_vector, frame_covector, frame_map, reading, physical_metric, model, calibration, dataset or comparison",
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

    /// Every Stage 5 declaration form (#806) with the record that the kernel's
    /// protocol-9 decoder reads, spans omitted. The shapes are S1's
    /// (`indexed::tests::every_spectral_form_serializes_to_its_wire_shape_and_is_algebraic`).
    /// The frontend checks no spectral rule: an empty basis or empty rows,
    /// and naturals of any size up to the decoder's digit bound, are sent as
    /// written for the kernel to judge.
    fn stage5_declarations() -> Vec<(String, Value)> {
        let family = |representation: &str| {
            json!({ "kind": "family",
                "parameters": [{ "kind": "object", "domain": p("CInfAffine") }],
                "constraints": [{ "kind": "canonical", "object": 0 }],
                "representation": representation })
        };
        let free_module = |object: &str, basis: Value| {
            json!({ "kind": "free_module", "family": p("FreeModule"), "indices": [p(object)],
                "basis": basis })
        };
        let endomorphism = |object: &str, module: &str, rows: Value, symmetric: bool| {
            json!({ "kind": "endomorphism", "family": p("Endomorphism"), "indices": [p(object)],
                "module": p(module), "rows": rows, "symmetric": symmetric })
        };
        let invariant = |definition: Value| {
            json!({ "kind": "morphism", "family": p("Smooth"),
                "indices": [p("Plane"), p("Line")], "definition": definition })
        };
        let widest = "9".repeat(crate::limits::MAX_ALGEBRA_DIGITS);
        let x = || coordinate("x");
        let y = || coordinate("y");
        let mut cases: Vec<(String, Value)> = vec![
            (
                "indexed family FreeModule(object(CInfAffine)) = free_module constraints(canonical(0));".into(),
                family("free_module"),
            ),
            (
                "indexed family Endomorphism(object(CInfAffine)) = endomorphism constraints(canonical(0));".into(),
                family("endomorphism"),
            ),
            (
                "indexed family Spectrum(object(CInfAffine)) = spectrum constraints(canonical(0));".into(),
                family("spectrum"),
            ),
            (
                "indexed family Branch(object(CInfAffine)) = branch constraints(canonical(0));".into(),
                family("branch"),
            ),
            (
                "indexed free_module V: FreeModule<Plane> = basis(e1, e2);".into(),
                free_module("Plane", json!(["e1", "e2"])),
            ),
            (
                "indexed free_module W: FreeModule<Pt> = basis();".into(),
                free_module("Pt", json!([])),
            ),
            (
                "indexed endomorphism H: Endomorphism<Plane> = rows((x, y), (y, -x)) of V symmetric;"
                    .into(),
                endomorphism(
                    "Plane",
                    "V",
                    json!([[x(), y()], [y(), neg(x())]]),
                    true,
                ),
            ),
            // Without `symmetric` no claim is made.
            (
                "indexed endomorphism J: Endomorphism<Pt> = rows((2, 1), (0, 2)) of V;".into(),
                endomorphism(
                    "Pt",
                    "V",
                    json!([[n("2"), n("1")], [n("0"), n("2")]]),
                    false,
                ),
            ),
            (
                "indexed endomorphism Z: Endomorphism<Pt> = rows() of W;".into(),
                endomorphism("Pt", "W", json!([]), false),
            ),
            (
                "indexed endomorphism Q: geo::Endomorphism<geo::Plane> = rows((x^2 * y, frac(1, 3))) of spectral::V symmetric;".into(),
                json!({ "kind": "endomorphism", "family": { "path": ["geo", "Endomorphism"] },
                    "indices": [{ "path": ["geo", "Plane"] }],
                    "module": { "path": ["spectral", "V"] },
                    "rows": [[product(vec![pow(x(), "2"), y()]), fraction("1", "3")]],
                    "symmetric": true }),
            ),
            (
                "indexed spectrum S: Spectrum<Plane> = eigen(H, t);".into(),
                json!({ "kind": "spectrum", "family": p("Spectrum"), "indices": [p("Plane")],
                    "endomorphism": p("H"), "fiber": "t" }),
            ),
            (
                "indexed spectrum S: Spectrum<Plane> = eigen(spectral::H, lambda);".into(),
                json!({ "kind": "spectrum", "family": p("Spectrum"), "indices": [p("Plane")],
                    "endomorphism": { "path": ["spectral", "H"] }, "fiber": "lambda" }),
            ),
            (
                "indexed branch B: Branch<Plane> = simple(S, localize = x^2 + y^2, witness = frac(1, 2) * t, exponent = 1);".into(),
                json!({ "kind": "branch", "family": p("Branch"), "indices": [p("Plane")],
                    "spectrum": p("S"),
                    "localize": sum(vec![pow(x(), "2"), pow(y(), "2")]),
                    "witness": product(vec![fraction("1", "2"), coordinate("t")]),
                    "exponent": "1" }),
            ),
            (
                "indexed morphism tr2: Smooth<Plane, Line> = trace_power(H, 2);".into(),
                invariant(json!({ "kind": "trace_power", "endomorphism": p("H"), "power": "2" })),
            ),
            (
                "indexed morphism c0: Smooth<Plane, Line> = char_coefficient(S, 0);".into(),
                invariant(json!({ "kind": "char_coefficient", "spectrum": p("S"), "index": "0" })),
            ),
            // Naturals are kept as written, up to the decoder's digit bound.
            (
                "indexed morphism tr: Smooth<Plane, Line> = trace_power(spectral::H, 007);".into(),
                invariant(json!({ "kind": "trace_power",
                    "endomorphism": { "path": ["spectral", "H"] }, "power": "007" })),
            ),
        ];
        cases.push((
            format!("indexed morphism tr: Smooth<Plane, Line> = trace_power(H, {widest});"),
            invariant(json!({ "kind": "trace_power", "endomorphism": p("H"), "power": widest })),
        ));
        cases.push((
            format!("indexed morphism c: Smooth<Plane, Line> = char_coefficient(S, {widest});"),
            invariant(json!({ "kind": "char_coefficient", "spectrum": p("S"), "index": widest })),
        ));
        cases.push((
            format!(
                "indexed branch B: Branch<Plane> = simple(S, localize = 1, witness = 1, exponent = {widest});"
            ),
            json!({ "kind": "branch", "family": p("Branch"), "indices": [p("Plane")],
                "spectrum": p("S"), "localize": n("1"), "witness": n("1"),
                "exponent": widest }),
        ));
        cases
    }

    /// Each Stage 5 declaration form parses to the record of its S1 wire
    /// shape, which exists only in protocol 9, and reads back as itself.
    #[test]
    fn every_stage5_declaration_parses_to_its_wire_record() {
        for (source, expected) in stage5_declarations() {
            let declaration = parse_declaration(&source)
                .unwrap_or_else(|error| panic!("`{source}` does not parse: {error:?}"));
            assert!(declaration.body.is_algebraic(), "{source}");
            let record = without_spans(serde_json::to_value(&declaration.body).unwrap());
            assert_eq!(record, expected, "{source}");
            assert_eq!(
                &source[declaration.span.start..declaration.span.end],
                source
            );
            assert_round_trip(&declaration);
        }
    }

    /// Malformed Stage 5 declarations are rejected at the offending token.
    #[test]
    fn malformed_stage5_declarations_are_rejected_at_their_place() {
        let long = "9".repeat(crate::limits::MAX_ALGEBRA_DIGITS + 1);
        let long_power =
            format!("indexed morphism tr: Smooth<Plane, Line> = trace_power(H, {long});");
        let long_index =
            format!("indexed morphism c: Smooth<Plane, Line> = char_coefficient(S, {long});");
        let long_exponent = format!(
            "indexed branch B: Branch<Plane> = simple(S, localize = g, witness = t, exponent = {long});"
        );
        let row = "an endomorphism row is a parenthesized tuple of entries, as in `rows((x, y), (y, -x))`";
        let exponent =
            "the exponent of `simple` is a natural literal, written as an unsigned integer";
        let power =
            "the power of `trace_power` is a natural literal, written as an unsigned integer";
        let cases: Vec<(&str, &str, &str, &str, &str)> = vec![
            // A free module lists its basis names in `basis(…)`.
            (
                "indexed free_module V: FreeModule<Plane> = (e1, e2);",
                "E_PARSE",
                "expected `basis`, found `(`",
                "(",
                "(e1",
            ),
            (
                "indexed free_module V: FreeModule<Plane> = basis[e1, e2];",
                "E_PARSE",
                "expected `(`, found `[`",
                "[",
                "[e1",
            ),
            (
                "indexed free_module V: FreeModule<Plane> = basis(e1, 2);",
                "E_PARSE",
                "expected an identifier",
                "2",
                "2)",
            ),
            (
                "indexed free_module V = basis(e1);",
                "E_PARSE",
                "expected `:`, found `=`",
                "=",
                "= basis",
            ),
            // An endomorphism has rows of tuples, then `of` its module, then
            // at most the word `symmetric`.
            (
                "indexed endomorphism H: Endomorphism<Plane> = rows(x, y) of V;",
                "E_PARSE",
                row,
                "x",
                "x, y",
            ),
            (
                "indexed endomorphism H: Endomorphism<Plane> = rows((x, y), y) of V;",
                "E_PARSE",
                row,
                "y",
                "y) of",
            ),
            (
                "indexed endomorphism H: Endomorphism<Plane> = columns((x, y), (y, -x)) of V;",
                "E_PARSE",
                "expected `rows`, found `columns`",
                "columns",
                "columns",
            ),
            (
                "indexed endomorphism H: Endomorphism<Plane> = symmetric rows((x, y), (y, -x)) of V;",
                "E_PARSE",
                "expected `rows`, found `symmetric`",
                "symmetric",
                "symmetric rows",
            ),
            (
                "indexed endomorphism H: Endomorphism<Plane> = rows((x, y), (y, -x)) V symmetric;",
                "E_PARSE",
                "expected `of`, found `V`",
                "V",
                "V symmetric",
            ),
            (
                "indexed endomorphism H: Endomorphism<Plane> = rows((x, y), (y, -x)) of V symmetrical;",
                "E_PARSE",
                "expected `;`, found `symmetrical`",
                "symmetrical",
                "symmetrical",
            ),
            (
                "indexed endomorphism H: Endomorphism<Plane> = rows((x, y), (y, -x)) of V symmetric symmetric;",
                "E_PARSE",
                "expected `;`, found `symmetric`",
                "symmetric",
                "symmetric;",
            ),
            // A spectrum names its endomorphism and an unqualified fiber
            // coordinate.
            (
                "indexed spectrum S: Spectrum<Plane> = spectrum(H, t);",
                "E_PARSE",
                "expected `eigen`, found `spectrum`",
                "spectrum",
                "spectrum(H",
            ),
            (
                "indexed spectrum S: Spectrum<Plane> = eigen(H);",
                "E_PARSE",
                "expected `,`, found `)`",
                ")",
                ");",
            ),
            (
                "indexed spectrum S: Spectrum<Plane> = eigen(H, 2);",
                "E_PARSE",
                "expected an identifier",
                "2",
                "2)",
            ),
            (
                "indexed spectrum S: Spectrum<Plane> = eigen(H, X::t);",
                "E_PARSE",
                "expected `)`, found `::`",
                "::",
                "::t",
            ),
            (
                "indexed spectrum S: Spectrum<Plane> = eigen(H, t, s);",
                "E_PARSE",
                "expected `)`, found `,`",
                ",",
                ", s",
            ),
            // A branch names its localization, witness and exponent, in this
            // order.
            (
                "indexed branch B: Branch<Plane> = simple(S, x^2 + y^2, witness = t, exponent = 1);",
                "E_PARSE",
                "`simple` needs an explicit localization: write `localize = …`",
                ",",
                ", x^2",
            ),
            (
                "indexed branch B: Branch<Plane> = simple(S localize = g, witness = t, exponent = 1);",
                "E_PARSE",
                "expected `,` before `localize` in `simple`",
                "localize",
                "localize",
            ),
            (
                "indexed branch B: Branch<Plane> = simple(S, localize = g, exponent = 1, witness = t);",
                "E_PARSE",
                "`simple` needs an explicit gap witness: write `witness = …`",
                ",",
                ", exponent",
            ),
            (
                "indexed branch B: Branch<Plane> = simple(S, localize = g, witness = t);",
                "E_PARSE",
                "`simple` needs an explicit exponent: write `exponent = …`",
                ")",
                ");",
            ),
            (
                "indexed branch B: Branch<Plane> = simple(S, localize = g, witness = t, exponent = -1);",
                "E_PARSE",
                exponent,
                "-",
                "-1",
            ),
            (
                "indexed branch B: Branch<Plane> = simple(S, localize = g, witness = t, exponent = frac(1, 2));",
                "E_PARSE",
                exponent,
                "frac",
                "frac",
            ),
            (
                "indexed branch B: Branch<Plane> = simple(S, localize = g, witness = t, exponent = e);",
                "E_PARSE",
                exponent,
                "e",
                "e)",
            ),
            (
                &long_exponent,
                "E_LIMIT",
                "the exponent of `simple` has at most 64 decimal digits",
                &long,
                &long,
            ),
            // No certificate is written in the source either.
            (
                "indexed branch B: Branch<Plane> = simple(S, localize = g, witness = t, exponent = 1, quotient = 0);",
                "E_PARSE",
                "expected `)`, found `,`",
                ",",
                ", quotient",
            ),
            // The invariants take their endomorphism or spectrum and a
            // natural literal.
            (
                "indexed morphism tr: Smooth<Plane, Line> = trace_power(H);",
                "E_PARSE",
                "expected `,`, found `)`",
                ")",
                ");",
            ),
            (
                "indexed morphism tr: Smooth<Plane, Line> = trace_power(H, k);",
                "E_PARSE",
                power,
                "k",
                "k)",
            ),
            (
                "indexed morphism tr: Smooth<Plane, Line> = trace_power(H, -2);",
                "E_PARSE",
                power,
                "-",
                "-2",
            ),
            (
                "indexed morphism tr: Smooth<Plane, Line> = trace_power(H, 2, 3);",
                "E_PARSE",
                "expected `)`, found `,`",
                ",",
                ", 3",
            ),
            (
                "indexed morphism c: Smooth<Plane, Line> = char_coefficient(S, frac(1, 2));",
                "E_PARSE",
                "the index of `char_coefficient` is a natural literal, written as an unsigned integer",
                "frac",
                "frac",
            ),
            (
                &long_power,
                "E_LIMIT",
                "the power of `trace_power` has at most 64 decimal digits",
                &long,
                &long,
            ),
            (
                &long_index,
                "E_LIMIT",
                "the index of `char_coefficient` has at most 64 decimal digits",
                &long,
                &long,
            ),
            // The family tags list the new ones.
            (
                "indexed family F(object(CInfAffine)) = free_modules constraints(canonical(0));",
                "E_TYPE",
                "family representation requires token, point, morphism, relative, smooth, cotangent, tangent, tape, metric_form, free_module, endomorphism, spectrum, branch, transition_average, frame, frame_vector, frame_covector, frame_map, reading, physical_metric, model, calibration, dataset or comparison",
                "free_modules",
                "free_modules",
            ),
            // A spectral family states its constraints.
            (
                "indexed family Spectrum(object(CInfAffine)) = spectrum;",
                "E_PARSE",
                "expected `constraints`, found `;`",
                ";",
                ";",
            ),
        ];
        for (source, code, message, place, context) in cases {
            assert_rejected_at(source, code, message, place, context);
        }
    }

    /// The Stage 5 words are contextual: they are reserved nowhere, so
    /// programs that use them as names keep parsing, and they name indexed
    /// declarations, basis names and coordinates next to the new forms.
    #[test]
    fn stage5_words_remain_ordinary_names() {
        for word in STAGE5_WORDS {
            assert!(!super::super::reserved(word), "{word}");
        }
        let functions: String = STAGE5_WORDS
            .iter()
            .map(|w| format!("fn {w}(n: Int) -> Int {{ n }}\n"))
            .collect();
        let calls: Vec<String> = STAGE5_WORDS.iter().map(|w| format!("{w}(1)")).collect();
        let named = format!("{functions}fn main() -> Int {{ {} }}\n", calls.join(" + "));
        let parameters: Vec<String> = STAGE5_WORDS.iter().map(|w| format!("{w}: Int")).collect();
        let lets: String = STAGE5_WORDS
            .iter()
            .map(|w| format!("let {w} = 1; "))
            .collect();
        let bound = format!(
            "fn all({}) -> Int {{ {} }}\nfn main() -> Int {{ {lets}all({}) }}\n",
            parameters.join(", "),
            STAGE5_WORDS.join(" + "),
            STAGE5_WORDS.join(", ")
        );
        for flat in [named, bound] {
            crate::frontend::parse(&flat, "names.vast")
                .unwrap_or_else(|errors| panic!("{errors:?}\n{flat}"));
        }
        let package = "indexed free_module rows: FreeModule<Plane> = basis(basis, symmetric);
indexed endomorphism symmetric: Endomorphism<Plane> = rows((eigen, simple), (simple, element)) of rows symmetric;
indexed spectrum eigen: Spectrum<Plane> = eigen(symmetric, branch);
indexed branch simple: Branch<Plane> = simple(eigen, localize = localize, witness = witness * exponent, exponent = 1);
indexed morphism trace_power: Smooth<Plane, Line> = trace_power(symmetric, 2);
indexed morphism char_coefficient: Smooth<Plane, Line> = char_coefficient(eigen, 0);
indexed primitive element = annihilates(Smooth, spectrum = eigen, element = element);
indexed primitive spectrum = action_entry(Smooth, spectrum = spectrum, element = branch, basis, symmetric);
indexed primitive branch = on_branch(Smooth, Line, branch = branch);
indexed primitive on_branch = branch_projector(Smooth, Line, branch = simple, basis, basis);
fn exponent(witness: Int) -> Int { let localize = witness; localize }
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
            [
                "rows",
                "symmetric",
                "eigen",
                "simple",
                "trace_power",
                "char_coefficient",
                "element",
                "spectrum",
                "branch",
                "on_branch"
            ]
        );
    }

    /// The Stage 6 declarations (#841), each with the record of its wire
    /// shape, which the kernel decodes in protocol 9.
    fn stage6_declarations() -> Vec<(&'static str, Value)> {
        let pow = |name: &str| json!({ "op": "pow", "base": coordinate(name), "exponent": "2" });
        let neg = |value: Value| json!({ "op": "neg", "operand": value });
        vec![
            (
                "indexed average A: TransitionAverage<P> = transition_average(B, from = g, to = e) = ratio(frac(1, 2) * omega^2, delta^2 + omega^2);",
                json!({ "kind": "transition_average", "family": p("TransitionAverage"), "indices": [p("P")],
                    "branch": p("B"), "from": "g", "to": "e",
                    "numerator": { "op": "product", "factors": [fraction("1", "2"), pow("omega")] },
                    "denominator": { "op": "sum", "terms": [pow("delta"), pow("omega")] } }),
            ),
            (
                "indexed average AK: TransitionAverage<X> = transition_average(BK, from = u1, to = u2) = ratio(1, 2);",
                json!({ "kind": "transition_average", "family": p("TransitionAverage"), "indices": [p("X")],
                    "branch": p("BK"), "from": "u1", "to": "u2", "numerator": n("1"), "denominator": n("2") }),
            ),
            (
                "indexed convention c = hbar_one;",
                json!({ "kind": "convention", "value": "hbar_one" }),
            ),
            (
                r#"indexed model M: Model<P> = model(hamiltonian = H, reading = r, convention = c, prepare = g, observe = e, predicts = A, regime = assume("rotating-wave approximation, Omega << Delta"));"#,
                json!({ "kind": "model", "family": p("Model"), "indices": [p("P")], "hamiltonian": p("H"),
                    "reading": p("r"), "convention": p("c"), "prepare": "g", "observe": "e",
                    "predicts": p("A"), "regime": "rotating-wave approximation, Omega << Delta" }),
            ),
            (
                r#"indexed calibration K: Calibration<P> = calibrate(omega = measured(frac(5, 2), u = frac(1, 20)), method = type_b, reference = "JCGM 100:2008", revision = "2026-11-16");"#,
                json!({ "kind": "calibration", "family": p("Calibration"), "indices": [p("P")],
                    "parameters": [{ "coordinate": "omega", "value": fraction("5", "2"),
                        "uncertainty": fraction("1", "20") }],
                    "method": "type_b", "reference": "JCGM 100:2008", "revision": "2026-11-16" }),
            ),
            (
                r#"indexed calibration K2: Calibration<P> = calibrate(delta = measured(-1, u = 1), omega = measured(-frac(1, 2), u = 2), method = type_a, reference = "", revision = "r");"#,
                json!({ "kind": "calibration", "family": p("Calibration"), "indices": [p("P")],
                    "parameters": [
                        { "coordinate": "delta", "value": neg(n("1")), "uncertainty": n("1") },
                        { "coordinate": "omega", "value": neg(fraction("1", "2")), "uncertainty": n("2") }],
                    "method": "type_a", "reference": "", "revision": "r" }),
            ),
            (
                "indexed dataset D: Dataset<P> = measure(model = M, calibration = K, coverage = 2, points = [(delta = 0, value = measured(frac(1, 2), u = frac(1, 50))), (delta = -1, value = measured(frac(9, 20), u = frac(1, 50)))]);",
                json!({ "kind": "dataset", "family": p("Dataset"), "indices": [p("P")], "model": p("M"),
                    "calibration": p("K"), "coverage": n("2"), "points": [
                        { "coordinates": [{ "coordinate": "delta", "value": n("0") }],
                            "value": fraction("1", "2"), "uncertainty": fraction("1", "50") },
                        { "coordinates": [{ "coordinate": "delta", "value": neg(n("1")) }],
                            "value": fraction("9", "20"), "uncertainty": fraction("1", "50") }] }),
            ),
            (
                "indexed dataset DK: Dataset<X> = measure(model = MK, calibration = KK, coverage = frac(196, 100), points = [(value = measured(1, u = 1)),]);",
                json!({ "kind": "dataset", "family": p("Dataset"), "indices": [p("X")], "model": p("MK"),
                    "calibration": p("KK"), "coverage": fraction("196", "100"), "points": [
                        { "coordinates": [], "value": n("1"), "uncertainty": n("1") }] }),
            ),
            (
                "indexed dataset E: Dataset<P> = measure(model = M, calibration = K, coverage = 1, points = []);",
                json!({ "kind": "dataset", "family": p("Dataset"), "indices": [p("P")], "model": p("M"),
                    "calibration": p("K"), "coverage": n("1"), "points": [] }),
            ),
            (
                r#"indexed comparison C: Comparison<P> = compare(D, calibration = K, fingerprint = "fnv1a64:0123456789abcdef", verdict = consistent);"#,
                json!({ "kind": "comparison", "family": p("Comparison"), "indices": [p("P")], "dataset": p("D"),
                    "calibration": p("K"), "fingerprint": "fnv1a64:0123456789abcdef", "verdict": "consistent" }),
            ),
            (
                r#"indexed comparison C2: Comparison<P> = compare(D, calibration = K, fingerprint = "", verdict = inconsistent);"#,
                json!({ "kind": "comparison", "family": p("Comparison"), "indices": [p("P")], "dataset": p("D"),
                    "calibration": p("K"), "fingerprint": "", "verdict": "inconsistent" }),
            ),
        ]
    }

    /// Each Stage 6 declaration form parses to the record of its S1 wire
    /// shape, which exists only in protocol 9, and reads back as itself.
    #[test]
    fn every_stage6_declaration_parses_to_its_wire_record() {
        for (source, expected) in stage6_declarations() {
            let declaration = parse_declaration(source)
                .unwrap_or_else(|error| panic!("`{source}` does not parse: {error:?}"));
            // Only the transition average is algebraic; the model and data
            // forms select protocol 9 as package input (#533).
            assert_eq!(
                declaration.body.is_algebraic(),
                matches!(declaration.body, DeclarationBody::TransitionAverage { .. }),
                "{source}"
            );
            let record = without_spans(serde_json::to_value(&declaration.body).unwrap());
            assert_eq!(record, expected, "{source}");
            assert_eq!(
                &source[declaration.span.start..declaration.span.end],
                source
            );
            assert_round_trip(&declaration);
        }
        // The forms parse after `pub` in a module too.
        for source in [
            "pub indexed average A: TransitionAverage<P> = transition_average(B, from = g, to = e) = ratio(1, 2);",
            r#"pub indexed comparison C: Comparison<P> = compare(D, calibration = K, fingerprint = "f", verdict = consistent);"#,
        ] {
            parse_module(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
        }
    }

    /// Malformed Stage 6 declarations are rejected at the offending token.
    #[test]
    fn malformed_stage6_declarations_are_rejected_at_their_place() {
        let average = "indexed average A: TransitionAverage<P> = transition_average";
        let cases: Vec<(String, &str, &str, &str, &str)> = vec![
            (
                format!("{average}(B, to = e) = ratio(1, 2);"),
                "E_PARSE",
                "`transition_average` needs an explicit source vector: write `from = …`",
                ",",
                ", to",
            ),
            (
                format!("{average}(B, from = g, to = 2) = ratio(1, 2);"),
                "E_PARSE",
                "the target vector of `transition_average` is a basis name, as in `e1`",
                "2",
                "2) = ratio",
            ),
            (
                format!("{average}(B, from = g, to = e) = 1;"),
                "E_PARSE",
                "the closed form of `transition_average` is `ratio(N, D)` of two polynomials",
                "1",
                "1;",
            ),
            (
                format!("{average}(B, from = g, to = e) = ratio;"),
                "E_PARSE",
                "the closed form of `transition_average` is `ratio(N, D)` of two polynomials",
                "ratio",
                "ratio;",
            ),
            (
                format!("{average}(B, from = g, to = e) = ratio(1);"),
                "E_PARSE",
                "expected `,`, found `)`",
                ")",
                ");",
            ),
            (
                format!("{average}(B, from = g, to = e) = ratio(1, 2, 3);"),
                "E_PARSE",
                "expected `)`, found `,`",
                ",",
                ", 3",
            ),
            (
                "indexed convention c = hbar_two;".into(),
                "E_TYPE",
                "a convention is `hbar_one`, the one convention of the profile",
                "hbar_two",
                "hbar_two",
            ),
            (
                r#"indexed model M: Model<P> = model(H, reading = r, convention = c, prepare = g, observe = e, predicts = A, regime = assume("a"));"#.into(),
                "E_PARSE",
                "`model` needs an explicit hamiltonian: write `hamiltonian = …`",
                "H",
                "H,",
            ),
            (
                r#"indexed model M: Model<P> = model(hamiltonian = H, convention = c, prepare = g, observe = e, predicts = A, regime = assume("a"));"#.into(),
                "E_PARSE",
                "`model` needs an explicit reading: write `reading = …`",
                ",",
                ", convention",
            ),
            (
                r#"indexed model M: Model<P> = model(hamiltonian = H, reading = r, convention = c, prepare = g, observe = e, predicts = A, regime = "a");"#.into(),
                "E_PARSE",
                "the regime of `model` is a recorded assumption: write `regime = assume(\"…\")`",
                "\"a\"",
                "\"a\"",
            ),
            (
                "indexed model M: Model<P> = model(hamiltonian = H, reading = r, convention = c, prepare = g, observe = e, predicts = A, regime = assume(a));".into(),
                "E_PARSE",
                "the regime of `model` is a string literal, as in \"…\"",
                "a",
                "a))",
            ),
            (
                r#"indexed model M: Model<P> = model(hamiltonian = H, reading = r, convention = c, prepare = g, observe = e, predicts = A, regime = assume("a\"b"));"#.into(),
                "E_PARSE",
                "the regime of `model` holds printable ASCII characters other than `\\` between double quotes",
                "\"a\\\"b\"",
                "\"a\\\"b\"",
            ),
            (
                "indexed model M: Model<P> = model(hamiltonian = H, reading = r, convention = c, prepare = g, observe = e, predicts = A, regime = assume(\"\u{3a9}\"));".into(),
                "E_PARSE",
                "the regime of `model` holds printable ASCII characters other than `\\` between double quotes",
                "\"\u{3a9}\"",
                "\"\u{3a9}\"",
            ),
            (
                "indexed calibration K: Calibration<P> = calibrate(omega = measured(1, u = 1));".into(),
                "E_PARSE",
                "`calibrate` needs an explicit method after its coordinates: write `, method = …`",
                ")",
                ");",
            ),
            (
                r#"indexed calibration K: Calibration<P> = calibrate(omega = measured(1, u = 1), method = type_c, reference = "a", revision = "b");"#.into(),
                "E_TYPE",
                "the method of a calibration is `type_a` or `type_b`",
                "type_c",
                "type_c",
            ),
            (
                r#"indexed calibration K: Calibration<P> = calibrate(omega = measured(1), method = type_a, reference = "a", revision = "b");"#.into(),
                "E_PARSE",
                "`measured` needs an explicit standard uncertainty: write `u = …`",
                ")",
                "), method",
            ),
            (
                r#"indexed calibration K: Calibration<P> = calibrate(omega = measured(x, u = 1), method = type_a, reference = "a", revision = "b");"#.into(),
                "E_PARSE",
                "a rational number is an integer literal or `frac(i, n)`, with an optional `-`",
                "x",
                "x, u",
            ),
            (
                r#"indexed calibration K: Calibration<P> = calibrate(omega = 1, method = type_a, reference = "a", revision = "b");"#.into(),
                "E_PARSE",
                "`calibrate` needs a measured value: write `measured(v, u = w)`",
                "1",
                "1, method",
            ),
            (
                "indexed calibration K: Calibration<P> = calibrate(omega = measured(1, u = 1), method = type_a, reference = a, revision = \"b\");".into(),
                "E_PARSE",
                "the reference of `calibrate` is a string literal, as in \"…\"",
                "a",
                "a, revision",
            ),
            (
                "indexed dataset D: Dataset<P> = measure(model = M, calibration = K, coverage = 2, points = [(delta = 0)]);".into(),
                "E_PARSE",
                "a point of a dataset ends with its measured value: write `, value = measured(v, u = w)`",
                ")",
                ")]",
            ),
            (
                "indexed dataset D: Dataset<P> = measure(model = M, calibration = K, coverage = 2, points = [delta = 0]);".into(),
                "E_PARSE",
                "a point of a dataset is a parenthesized tuple, as in `(x = 1, value = measured(v, u = w))`",
                "delta",
                "delta = 0]",
            ),
            (
                "indexed dataset D: Dataset<P> = measure(model = M, calibration = K, coverage = k, points = []);".into(),
                "E_PARSE",
                "a rational number is an integer literal or `frac(i, n)`, with an optional `-`",
                "k",
                "k, points",
            ),
            (
                "indexed dataset D: Dataset<P> = measure(calibration = K, model = M, coverage = 1, points = []);".into(),
                "E_PARSE",
                "`measure` needs an explicit model: write `model = …`",
                "calibration",
                "calibration = K, model",
            ),
            (
                "indexed comparison C: Comparison<P> = compare(D, calibration = K, verdict = consistent);".into(),
                "E_PARSE",
                "`compare` needs the recorded fingerprint of its calibration: write `fingerprint = …`",
                ",",
                ", verdict",
            ),
            (
                "indexed comparison C: Comparison<P> = compare(D, calibration = K, fingerprint = f, verdict = consistent);".into(),
                "E_PARSE",
                "the fingerprint of `compare` is a string literal, as in \"…\"",
                "f",
                "f, verdict",
            ),
            (
                r#"indexed comparison C: Comparison<P> = compare(D, fingerprint = "f", calibration = K, verdict = consistent);"#.into(),
                "E_PARSE",
                "`compare` needs an explicit calibration: write `calibration = …`",
                ",",
                ", fingerprint",
            ),
            (
                r#"indexed comparison C: Comparison<P> = compare(D, calibration = K, fingerprint = "f", verdict = stale);"#.into(),
                "E_TYPE",
                "the verdict of a comparison is `consistent` or `inconsistent`",
                "stale",
                "stale",
            ),
        ];
        for (source, code, message, place, context) in &cases {
            assert_rejected_at(source, code, message, place, context);
        }
        let limit = crate::limits::MAX_DATASET_POINTS;
        let points = vec!["(delta = 0, value = measured(1, u = 1))"; limit + 1].join(", ");
        let source = format!(
            "indexed dataset D: Dataset<P> = measure(model = M, calibration = K, coverage = 1, points = [{points}]);"
        );
        let error = parse_declaration(&source).expect_err("too many points");
        assert_eq!(error.code, "E_LIMIT");
        assert_eq!(
            error.message,
            format!(
                "a dataset has at most {limit} points (`datasetPoints`), but this one has {}",
                limit + 1
            )
        );
        assert_eq!(
            &source[error.span.start..error.span.end],
            format!("[{points}]")
        );
        let at_limit = vec!["(delta = 0, value = measured(1, u = 1))"; limit].join(", ");
        parse_declaration(&format!(
            "indexed dataset D: Dataset<P> = measure(model = M, calibration = K, coverage = 1, points = [{at_limit}]);"
        ))
        .expect("a dataset at the limit");
        // A recorded text has at most `recordTextBytes` bytes, at each of the
        // four places that take one.
        let bytes = crate::limits::MAX_RECORD_TEXT_BYTES;
        let texts = |text: &str| {
            [
                format!(
                    "indexed model M: Model<P> = model(hamiltonian = H, reading = r, convention = c, prepare = g, observe = e, predicts = A, regime = assume(\"{text}\"));"
                ),
                format!(
                    "indexed calibration K: Calibration<P> = calibrate(method = type_a, reference = \"{text}\", revision = \"r\");"
                ),
                format!(
                    "indexed calibration K: Calibration<P> = calibrate(method = type_a, reference = \"r\", revision = \"{text}\");"
                ),
                format!(
                    "indexed comparison C: Comparison<P> = compare(D, calibration = K, fingerprint = \"{text}\", verdict = consistent);"
                ),
            ]
        };
        for (source, what) in
            texts(&"~".repeat(bytes))
                .iter()
                .zip(["regime", "reference", "revision", "fingerprint"])
        {
            let declaration = parse_declaration(source).expect("a text at the limit");
            let record = serde_json::to_value(&declaration.body).unwrap();
            assert_eq!(record[what], json!("~".repeat(bytes)), "{source}");
        }
        let long = "a".repeat(bytes + 1);
        for (source, (what, operation)) in texts(&long).iter().zip([
            ("regime", "model"),
            ("reference", "calibrate"),
            ("revision", "calibrate"),
            ("fingerprint", "compare"),
        ]) {
            assert_rejected_at(
                source,
                "E_LIMIT",
                &format!(
                    "the {what} of `{operation}` has at most {bytes} bytes (`recordTextBytes`), but this one has {}",
                    bytes + 1
                ),
                &format!("\"{long}\""),
                &format!("\"{long}\""),
            );
        }
    }

    /// The Stage 6 forms add no token: `/` and `@` keep their errors
    /// everywhere, the Stage 6 declarations included, and a string literal is
    /// read only at the four places that take one.
    #[test]
    fn slash_at_and_strings_keep_their_errors_outside_the_four_text_fields() {
        let first = |source: &str| {
            let error = parse_module(source).expect_err(source);
            (
                error.code,
                error.message,
                source[error.span.start..error.span.end].to_string(),
            )
        };
        let division = (
            "E_UNSUPPORTED".to_string(),
            "division is not supported".to_string(),
            "/".to_string(),
        );
        assert_eq!(first("fn main() -> Int { 4 / 2 }"), division);
        assert_eq!(first("indexed quantity Speed = L / T;"), division);
        assert_eq!(
            first(r#"indexed model M: Model<P> = model(hamiltonian = H / 2);"#),
            division
        );
        assert_eq!(
            first(
                "indexed average A: TransitionAverage<P> = transition_average(B, from = g, to = e) = 1 / 2;"
            ),
            division
        );
        assert_eq!(
            first(
                "indexed average A: TransitionAverage<P> = transition_average(B, from = g, to = e) = ratio(1, 2) / 3;"
            ),
            division
        );
        let (code, _, place) = first("fn main() -> Int { 4 @ 2 }");
        assert_eq!((code.as_str(), place.as_str()), ("E_LEX", "@"));
        let (code, _, place) = first(
            r#"indexed comparison C: Comparison<P> = compare(D, calibration = K @ "f", verdict = consistent);"#,
        );
        assert_eq!((code.as_str(), place.as_str()), ("E_LEX", "@"));
        let (code, _, place) = first(r#"fn main() -> Int { let s = "a"; 0 }"#);
        assert_eq!((code.as_str(), place.as_str()), ("E_UNSUPPORTED", "\"a\""));
        let (code, _, place) = first(
            r#"indexed dataset D: Dataset<P> = measure(model = M, calibration = K, coverage = "2", points = []);"#,
        );
        assert_eq!((code.as_str(), place.as_str()), ("E_PARSE", "\"2\""));
    }

    /// The words of the Stage 6 forms (#841): declaration kinds, family
    /// representations, tags and keywords. `method` is a keyword already.
    const STAGE6_WORDS: [&str; 32] = [
        "average",
        "transition_average",
        "ratio",
        "from",
        "to",
        "convention",
        "hbar_one",
        "model",
        "hamiltonian",
        "prepare",
        "observe",
        "predicts",
        "regime",
        "assume",
        "calibration",
        "calibrate",
        "measured",
        "u",
        "type_a",
        "type_b",
        "reference",
        "revision",
        "dataset",
        "measure",
        "coverage",
        "points",
        "comparison",
        "compare",
        "fingerprint",
        "verdict",
        "consistent",
        "average_at",
    ];

    /// The Stage 6 words are contextual: they are reserved nowhere, so
    /// programs that use them as names keep parsing.
    #[test]
    fn stage6_words_remain_ordinary_names() {
        for word in STAGE6_WORDS.iter().chain(&["inconsistent"]) {
            assert!(!super::super::reserved(word), "{word}");
        }
        let functions: String = STAGE6_WORDS
            .iter()
            .map(|w| format!("fn {w}(n: Int) -> Int {{ n }}\n"))
            .collect();
        let calls: Vec<String> = STAGE6_WORDS.iter().map(|w| format!("{w}(1)")).collect();
        let named = format!("{functions}fn main() -> Int {{ {} }}\n", calls.join(" + "));
        let lets: String = STAGE6_WORDS
            .iter()
            .map(|w| format!("let {w} = 1; "))
            .collect();
        let bound = format!(
            "fn main() -> Int {{ {lets}{} }}\n",
            STAGE6_WORDS.join(" + ")
        );
        for flat in [named, bound] {
            crate::frontend::parse(&flat, "names.vast")
                .unwrap_or_else(|errors| panic!("{errors:?}\n{flat}"));
        }
    }

    /// The words of the Stage 5 forms (#806): declaration kinds, family
    /// representations, definition and observation tags, and keywords.
    const STAGE5_WORDS: [&str; 20] = [
        "free_module",
        "endomorphism",
        "spectrum",
        "branch",
        "basis",
        "rows",
        "symmetric",
        "eigen",
        "simple",
        "localize",
        "witness",
        "exponent",
        "element",
        "trace_power",
        "char_coefficient",
        "annihilates",
        "action_entry",
        "on_branch",
        "branch_differential",
        "branch_projector",
    ];
}
