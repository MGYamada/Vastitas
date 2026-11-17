//! Unresolved declaration-driven source IR. The kernel reconstructs every ID
//! from its enclosing package/module and independently checks each contract.

use crate::ir::{Span, TypePath};
use serde::de::Error as _;
use serde::ser::SerializeMap;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;

/// A library's explicit export of the finite legacy geometry dialect, as the
/// `geometry_compat` table of a manifest spells it. Paths remain unresolved
/// until the independent kernel checks every role. The request carries the
/// export as a [`WireGeometryProfile`].
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeometrySetting {
    pub domain: String,
    pub marker: String,
    pub base_object: String,
    pub affine: String,
    pub base: String,
    pub origin: String,
    pub identity: String,
    pub dimension: String,
}

/// The `geometry_compat` table of a manifest: the two settings and the roles
/// that they share.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeometryProfile {
    pub scheme: GeometrySetting,
    pub smooth: GeometrySetting,
    pub point: String,
    pub morphism: String,
    pub pointed: String,
    pub compose: String,
    pub apply: String,
}

/// A geometry setting in the wire request. Its spelling is separate from the
/// manifest's (#533): the slot of `dim(…)` is `dimension` in the manifest and
/// `dim` on the wire.
#[derive(Debug, Serialize)]
pub struct WireGeometrySetting {
    pub domain: String,
    pub marker: String,
    pub base_object: String,
    pub affine: String,
    pub base: String,
    pub origin: String,
    pub identity: String,
    pub dim: String,
}

/// The `geometry_compat` export of a package in the wire request.
#[derive(Debug, Serialize)]
pub struct WireGeometryProfile {
    pub scheme: WireGeometrySetting,
    pub smooth: WireGeometrySetting,
    pub point: String,
    pub morphism: String,
    pub pointed: String,
    pub compose: String,
    pub apply: String,
}

impl From<GeometrySetting> for WireGeometrySetting {
    fn from(setting: GeometrySetting) -> Self {
        let GeometrySetting {
            domain,
            marker,
            base_object,
            affine,
            base,
            origin,
            identity,
            dimension,
        } = setting;
        WireGeometrySetting {
            domain,
            marker,
            base_object,
            affine,
            base,
            origin,
            identity,
            dim: dimension,
        }
    }
}

impl From<GeometryProfile> for WireGeometryProfile {
    fn from(profile: GeometryProfile) -> Self {
        let GeometryProfile {
            scheme,
            smooth,
            point,
            morphism,
            pointed,
            compose,
            apply,
        } = profile;
        WireGeometryProfile {
            scheme: scheme.into(),
            smooth: smooth.into(),
            point,
            morphism,
            pointed,
            compose,
            apply,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Declaration {
    pub name: String,
    #[serde(flatten)]
    pub body: DeclarationBody,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum DeclarationBody {
    Marker,
    Implementation {
        marker: TypePath,
        representation: Representation,
        capabilities: Vec<Capability>,
    },
    Classification {
        parents: Vec<TypePath>,
        domain: Vec<TypePath>,
    },
    Global {
        implementation: TypePath,
    },
    Family {
        parameters: Vec<Parameter>,
        constraints: Vec<Constraint>,
        representation: FamilyRepresentation,
    },
    Package {
        cases: Vec<PackageShape>,
    },
    Primitive {
        binding: Primitive,
    },
    /// A presented affine object `spec[generators] relations(...) over base by(...)`.
    /// The kernel expands, bounds and checks every polynomial.
    Affine {
        implementation: TypePath,
        generators: Vec<String>,
        relations: Vec<PolyExpr>,
        base: Option<TypePath>,
        bindings: Vec<Binding>,
    },
    /// A declared morphism `family<X, Y, S>` over a base.
    Morphism {
        family: TypePath,
        indices: Vec<TypePath>,
        definition: MorphismDefinition,
    },
    /// The fiber product `left ×_B right` over `left`'s base.
    AffineFiber {
        implementation: TypePath,
        left: TypePath,
        right: TypePath,
        via: Option<FiberVia>,
    },
    /// The principal open `D(element)` of `object`.
    AffineLocalization {
        implementation: TypePath,
        object: TypePath,
        element: PolyExpr,
        inverse: String,
    },
    /// Evidence that two declared morphisms are mutually inverse.
    Iso {
        forward: TypePath,
        inverse: TypePath,
    },
    /// Evidence that a declared square is Cartesian.
    Cartesian {
        first: TypePath,
        second: TypePath,
        fiber: TypePath,
        inverse: TypePath,
    },
    /// An object glued from two charts along a transition (Stage 7, #878):
    /// the opens of the charts, the coordinates of the second open in those
    /// of the first, and the coordinates of the first open in those of the
    /// second. The kernel checks the site, the charts and the transition.
    Glued {
        implementation: TypePath,
        opens: Vec<TypePath>,
        forward: Vec<Binding>,
        inverse: Vec<Binding>,
    },
    /// A cover of an object by opens of it (Stage 7), with the coefficients
    /// of the identity `Σ aᵢ fᵢ = 1`, which the kernel checks.
    Cover {
        object: TypePath,
        opens: Vec<TypePath>,
        coefficients: Vec<PolyExpr>,
    },
    /// A separation claim of a Zariski gluing (Stage 7): the witness gives
    /// the inverse coordinate of the first open.
    Separated {
        glued: TypePath,
        witness: Binding,
    },
    /// A manifold claim of a smooth gluing (Stage 7), with the dimension as
    /// an unsigned decimal string and the witness of `Separated`.
    Manifold {
        glued: TypePath,
        dimension: String,
        witness: Binding,
    },
    /// A projective claim `proj(P)[s, t] chart(…) inverse(…) …` (Stage 7).
    Projective {
        glued: TypePath,
        homogeneous: Vec<String>,
        charts: Vec<ProjectiveChart>,
    },
    /// A smooth object `Affine(dimension)[coordinates]`. The
    /// kernel checks the dimension against the coordinates.
    SmoothAffine {
        implementation: TypePath,
        dimension: String,
        coordinates: Vec<String>,
    },
    /// A metric `family<object>` with a constant Gram matrix.
    /// The kernel evaluates and checks every entry.
    Metric {
        family: TypePath,
        indices: Vec<TypePath>,
        gram: MetricGram,
    },
    /// Evidence for a metric. The kernel computes the
    /// certificate; the wire never carries one.
    Evidence {
        metric: TypePath,
        evidence: EvidenceKind,
    },
    /// A frame `family<object>` of a smooth object (Stage 4): its
    /// columns in the coordinate frame, and the inverse that a frame
    /// polynomial in the point declares. The kernel computes the inverse of a
    /// constant frame.
    Frame {
        family: TypePath,
        indices: Vec<TypePath>,
        columns: FrameColumns,
        inverse: Option<FrameColumns>,
    },
    /// A nominal base dimension (Stage 4).
    BaseDimension,
    /// A nominal quantity kind of a dimension (Stage 4).
    Quantity {
        dimension: Vec<DimensionFactor>,
    },
    /// A physical reading `family<object>` of a chart: one quantity per
    /// coordinate (Stage 4).
    Reading {
        family: TypePath,
        indices: Vec<TypePath>,
        quantities: Vec<ReadingEntry>,
    },
    /// A scale of a quantity: a constant magnitude (Stage 4).
    Scale {
        quantity: TypePath,
        magnitude: PolyExpr,
    },
    /// A physical interpretation `family<object>` of a metric under a
    /// reading (Stage 4). The kernel checks its dimensions.
    PhysicalMetric {
        family: TypePath,
        indices: Vec<TypePath>,
        metric: TypePath,
        reading: TypePath,
        value: Option<Vec<DimensionFactor>>,
        entries: PhysicalGram,
    },
    /// A free module `family<object>` over the coordinate ring of a smooth
    /// object, with its named ordered basis (Stage 5).
    FreeModule {
        family: TypePath,
        indices: Vec<TypePath>,
        basis: Vec<String>,
    },
    /// An endomorphism `family<object>` of a free module: rows of
    /// polynomials in the object's coordinates, and whether `symmetric` is
    /// declared (Stage 5). The kernel checks the claim.
    Endomorphism {
        family: TypePath,
        indices: Vec<TypePath>,
        module: TypePath,
        rows: Vec<Vec<PolyExpr>>,
        symmetric: bool,
    },
    /// The spectrum `family<object>` of an endomorphism, with the name of its
    /// fiber coordinate (Stage 5). The kernel computes the
    /// certificate; the wire never carries one.
    Spectrum {
        family: TypePath,
        indices: Vec<TypePath>,
        endomorphism: TypePath,
        fiber: String,
    },
    /// A simple branch `family<object>` of a spectrum on the principal open
    /// of `localize`, with its gap witness and its exponent, an unsigned
    /// decimal string (Stage 5). The kernel computes the
    /// quotient; the wire never carries one.
    Branch {
        family: TypePath,
        indices: Vec<TypePath>,
        spectrum: TypePath,
        localize: PolyExpr,
        witness: PolyExpr,
        exponent: String,
    },
    /// A dephased transition average `family<object>` of a simple branch,
    /// from the basis vector `from` to the basis vector `to` of the module of
    /// its field, with its closed form `numerator / denominator` (Stage 6).
    /// The kernel computes the certificate; the wire never carries
    /// one.
    TransitionAverage {
        family: TypePath,
        indices: Vec<TypePath>,
        branch: TypePath,
        from: String,
        to: String,
        numerator: PolyExpr,
        denominator: PolyExpr,
    },
    /// A convention of `nature::model` (Stage 6).
    Convention {
        value: ConventionKind,
    },
    /// A model `family<object>` of `nature::model`: its field, reading,
    /// convention, prepared and observed basis vectors, predicted average and
    /// regime, a recorded assumption (Stage 6).
    Model {
        family: TypePath,
        indices: Vec<TypePath>,
        hamiltonian: TypePath,
        reading: TypePath,
        convention: TypePath,
        prepare: String,
        observe: String,
        predicts: TypePath,
        regime: String,
    },
    /// A calibration `family<object>` of `nature::errorbar`: measured values
    /// of some coordinates, the method of evaluation, a reference and a
    /// revision (Stage 6).
    Calibration {
        family: TypePath,
        indices: Vec<TypePath>,
        parameters: Vec<Calibrated>,
        method: CalibrationMethod,
        reference: String,
        revision: String,
    },
    /// A dataset `family<object>` of `nature::errorbar` of a model under a
    /// calibration: a constant coverage factor and its points (Stage 6).
    Dataset {
        family: TypePath,
        indices: Vec<TypePath>,
        model: TypePath,
        calibration: TypePath,
        coverage: PolyExpr,
        points: Vec<DataPoint>,
    },
    /// A comparison `family<object>` of `nature::errorbar`: a dataset, the
    /// recorded fingerprint of its calibration and the recorded verdict,
    /// which the kernel recomputes (Stage 6).
    Comparison {
        family: TypePath,
        indices: Vec<TypePath>,
        dataset: TypePath,
        calibration: TypePath,
        fingerprint: String,
        verdict: Verdict,
    },
}

/// The convention of a model (Stage 6): `hbar_one` writes energies as
/// angular frequencies.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ConventionKind {
    HbarOne,
}

/// How the uncertainties of a calibration were evaluated (Stage 6): type A
/// or type B of the guide to the expression of uncertainty in measurement.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CalibrationMethod {
    TypeA,
    TypeB,
}

/// The recorded verdict of a comparison (Stage 6).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Verdict {
    Consistent,
    Inconsistent,
}

/// One calibrated coordinate of a calibration (Stage 6): its constant value
/// and its standard uncertainty.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Calibrated {
    pub coordinate: String,
    pub value: PolyExpr,
    pub uncertainty: PolyExpr,
}

/// The constant value of one coordinate at a point of a dataset (Stage 6).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PointCoordinate {
    pub coordinate: String,
    pub value: PolyExpr,
}

/// One point of a dataset (Stage 6): the values of the coordinates that the
/// calibration does not give, and the measured value of the observable with
/// its standard uncertainty.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DataPoint {
    pub coordinates: Vec<PointCoordinate>,
    pub value: PolyExpr,
    pub uncertainty: PolyExpr,
}

/// The columns of a frame: `coordinates`, the coordinate frame, or
/// polynomial columns in the object's coordinates.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum FrameColumns {
    Coordinates,
    Columns { columns: Vec<Vec<PolyExpr>> },
}

/// One factor of a physical dimension: a base dimension and its integer
/// exponent, a decimal string with an optional leading `-`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DimensionFactor {
    pub base: TypePath,
    pub exponent: String,
}

/// The quantity of one coordinate of a reading.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReadingEntry {
    pub coordinate: String,
    pub quantity: TypePath,
}

/// One factor of a scale monomial: a scale and its integer exponent.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ScaleFactor {
    pub scale: TypePath,
    pub exponent: String,
}

/// A constant coefficient times powers of scales.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ScaleMonomial {
    pub coefficient: PolyExpr,
    pub factors: Vec<ScaleFactor>,
}

/// The scale of one coordinate of a normalized physical metric.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CoordinateScale {
    pub coordinate: String,
    pub scale: TypePath,
}

/// The Gram matrix of a physical metric in terms of scales.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum PhysicalGram {
    /// The identity matrix of the object's dimension.
    Euclidean,
    /// Rows of scale monomials.
    Gram { rows: Vec<Vec<ScaleMonomial>> },
    /// One scale per coordinate: the diagonal of their inverse squares.
    Normalized { scales: Vec<CoordinateScale> },
}

/// The Gram matrix of a metric declaration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum MetricGram {
    /// The identity matrix of the object's dimension.
    Euclidean,
    /// Rows of constant polynomial expressions.
    Gram { rows: Vec<Vec<PolyExpr>> },
}

/// The kind of evidence that the kernel computes for a metric.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EvidenceKind {
    /// An exact inverse of the Gram matrix.
    Nondegenerate,
    /// An exact `L D Lᵀ` factorization with positive `D`.
    Riemannian,
}

/// A chosen isomorphism between separately declared fiber bases.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FiberVia {
    pub forward: Vec<Binding>,
    pub inverse: Vec<Binding>,
}

/// One chart entry of a projective claim (Stage 7): the chart, the
/// homogeneous coordinate that is a unit on it, the other coordinate over it
/// in the chart's coordinates, and the chart's coordinates in the one
/// coordinate of the standard chart.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProjectiveChart {
    pub chart: TypePath,
    pub dehomogenized: String,
    pub image: PolyExpr,
    pub inverse: Vec<Binding>,
}

/// How a declared morphism `X → Y` over `S` is given.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum MorphismDefinition {
    /// The images of the target's coordinates in the source's coordinates.
    Pullback {
        images: Vec<Binding>,
    },
    Identity,
    Structure,
    First,
    Second,
    /// `D(φ^#(f)) → D(f)` for a declared morphism `φ`.
    Restrict {
        morphism: TypePath,
    },
    /// `trace_power(H, k)`: the smooth map `p ↦ tr(H(p)^k)` of an
    /// endomorphism (Stage 5). The power is an unsigned decimal string.
    TracePower {
        endomorphism: TypePath,
        power: String,
    },
    /// `char_coefficient(S, i)`: the coefficient of `t^i` in the
    /// characteristic polynomial of a spectrum (Stage 5). The index is an
    /// unsigned decimal string.
    CharCoefficient {
        spectrum: TypePath,
        index: String,
    },
}

impl DeclarationBody {
    /// Stage 2 algebraic, Stage 3 smooth and metric, Stage 4 frame and
    /// physical dimension, and Stage 5 and 6 spectral forms (the transition
    /// average and `average_at` included), whose families have `algebraic` set
    /// in the kernel's `families`. The model and data forms of Stage 6 are
    /// not. A program with one of these forms has no `legacy_geometry`
    /// (`packages::legacy_geometry`).
    pub fn is_algebraic(&self) -> bool {
        match self {
            DeclarationBody::Affine { .. }
            | DeclarationBody::Morphism { .. }
            | DeclarationBody::AffineFiber { .. }
            | DeclarationBody::AffineLocalization { .. }
            | DeclarationBody::Iso { .. }
            | DeclarationBody::Cartesian { .. }
            | DeclarationBody::Glued { .. }
            | DeclarationBody::Cover { .. }
            | DeclarationBody::Separated { .. }
            | DeclarationBody::Manifold { .. }
            | DeclarationBody::Projective { .. }
            | DeclarationBody::SmoothAffine { .. }
            | DeclarationBody::Metric { .. }
            | DeclarationBody::Evidence { .. }
            | DeclarationBody::Frame { .. }
            | DeclarationBody::BaseDimension
            | DeclarationBody::Quantity { .. }
            | DeclarationBody::Reading { .. }
            | DeclarationBody::Scale { .. }
            | DeclarationBody::PhysicalMetric { .. }
            | DeclarationBody::FreeModule { .. }
            | DeclarationBody::Endomorphism { .. }
            | DeclarationBody::Spectrum { .. }
            | DeclarationBody::Branch { .. }
            | DeclarationBody::TransitionAverage { .. } => true,
            DeclarationBody::Primitive { binding } => binding.family().algebraic,
            DeclarationBody::Implementation { representation, .. } => matches!(
                representation,
                Representation::PresentedAffine { .. } | Representation::SmoothAffine
            ),
            DeclarationBody::Family {
                parameters,
                constraints,
                representation,
            } => {
                matches!(
                    representation,
                    FamilyRepresentation::Relative
                        | FamilyRepresentation::Smooth
                        | FamilyRepresentation::Cotangent
                        | FamilyRepresentation::Tangent
                        | FamilyRepresentation::Tape
                        | FamilyRepresentation::MetricForm
                        | FamilyRepresentation::Frame
                        | FamilyRepresentation::FrameVector
                        | FamilyRepresentation::FrameCovector
                        | FamilyRepresentation::FrameMap
                        | FamilyRepresentation::Reading
                        | FamilyRepresentation::PhysicalMetric
                        | FamilyRepresentation::FreeModule
                        | FamilyRepresentation::Endomorphism
                        | FamilyRepresentation::Spectrum
                        | FamilyRepresentation::Branch
                        | FamilyRepresentation::TransitionAverage
                ) || constraints.iter().any(|c| {
                    matches!(
                        c,
                        Constraint::Structural { .. } | Constraint::Canonical { .. }
                    )
                }) || parameters
                    .iter()
                    .any(|p| matches!(p, Parameter::Frame { .. }))
            }
            _ => false,
        }
    }
}

/// The image of one base coordinate under a structure map.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Binding {
    pub name: String,
    pub image: PolyExpr,
}

/// Unexpanded polynomial syntax. Literals stay decimal strings; sums and
/// products are n-ary so long polynomials stay shallow.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
pub enum PolyExpr {
    Natural {
        value: String,
    },
    Fraction {
        numerator: String,
        denominator: String,
    },
    Coordinate {
        name: String,
    },
    Neg {
        operand: Box<PolyExpr>,
    },
    Sum {
        terms: Vec<PolyExpr>,
    },
    Product {
        factors: Vec<PolyExpr>,
    },
    Pow {
        base: Box<PolyExpr>,
        exponent: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", deny_unknown_fields)]
pub enum Representation {
    AffineDescriptor,
    ScalarBase {
        setting: GeometricSetting,
        coefficient: CoefficientKind,
    },
    LinearDescriptor {
        base: TypePath,
        coefficient: CoefficientKind,
    },
    PresentedAffine {
        field: ExactField,
    },
    /// The smooth real affine spaces `Affine(n)`.
    SmoothAffine,
}

/// Exact coefficient fields of presented affine objects.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ExactField {
    Rational,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CoefficientKind {
    Real,
    Complex,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GeometricSetting {
    Scheme,
    Smooth,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Capability {
    Origin,
    /// The capability of the operation `dim` (#778), spelled `dim` in the
    /// source and on the wire.
    #[serde(rename = "dim")]
    Dimension,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FamilyRepresentation {
    Token,
    Point,
    Morphism,
    Relative,
    Smooth,
    /// `Cotangent(X)`: covectors at points of a smooth object.
    Cotangent,
    /// `Tangent(X)`: vectors at points of a smooth object.
    Tangent,
    /// `Tape(X, Y)`: the saved forward values of a smooth map at a point.
    /// Only `linearize` constructs a tape.
    Tape,
    /// `MetricForm(X)`: indexes the metrics of a smooth object.
    /// No value has this type.
    MetricForm,
    /// `Frame(X)`: indexes the frames of a smooth object (Stage 4). No value
    /// has this type.
    Frame,
    /// `Coords(b)`: the coordinates of vectors in the frame `b` (Stage 4).
    FrameVector,
    /// `CoCoords(b)`: the coordinates of covectors in the frame `b`
    /// (Stage 4).
    FrameCovector,
    /// `FrameMap(b, c)`: matrices of linear maps in the frames `b` and `c`
    /// (Stage 4).
    FrameMap,
    /// `Reading(X)`: indexes the physical readings of a chart (Stage 4). No
    /// value has this type.
    Reading,
    /// `PhysicalMetric(X)`: indexes the physical interpretations of the
    /// metrics of a chart (Stage 4). No value has this type.
    PhysicalMetric,
    /// `FreeModule(X)`: indexes the free modules over a smooth object
    /// (Stage 5). No value has this type.
    FreeModule,
    /// `Endomorphism(X)`: indexes the endomorphisms of free modules over a
    /// smooth object (Stage 5). No value has this type.
    Endomorphism,
    /// `Spectrum(X)`: indexes the spectra of endomorphisms over a smooth
    /// object (Stage 5). No value has this type.
    Spectrum,
    /// `Branch(X)`: indexes the simple branches of spectra over a smooth
    /// object (Stage 5). No value has this type.
    Branch,
    /// `TransitionAverage(X)`: indexes the transition averages of simple
    /// branches over a smooth object (Stage 6). No value has this
    /// type.
    TransitionAverage,
    /// `Model(X)`: indexes the models of `nature::model` over a smooth object
    /// (Stage 6). No value has this type.
    Model,
    /// `Calibration(X)`: indexes the calibrations of `nature::errorbar` over a
    /// smooth object (Stage 6). No value has this type.
    Calibration,
    /// `Dataset(X)`: indexes the datasets of `nature::errorbar` over a smooth
    /// object (Stage 6). No value has this type.
    Dataset,
    /// `Comparison(X)`: indexes the comparisons of `nature::errorbar` over a
    /// smooth object (Stage 6). No value has this type.
    Comparison,
}

/// How a cotangent pullback obtains forward values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PullbackMode {
    Saved,
    Recomputed,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Parameter {
    Domain,
    Marker,
    Natural,
    Object {
        domain: TypePath,
    },
    /// A frame of the family `family` (Stage 4).
    Frame {
        family: TypePath,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Constraint {
    SameObject { left: u32, right: u32 },
    SameBase { left: u32, right: u32 },
    Over { object: u32, marker: u32 },
    Structural { object: u32, base: u32 },
    Canonical { object: u32 },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObjectType {
    pub domain: TypePath,
    pub marker: TypePath,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PackageShape {
    pub witness_type: ObjectType,
    pub fields: Vec<BoundApplication>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundApplication {
    pub family: TypePath,
    pub indices: Vec<BoundIndex>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum BoundIndex {
    Witness,
    Global { declaration: TypePath },
    Domain { declaration: TypePath },
    Marker { declaration: TypePath },
    Natural { value: String },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Argument {
    Name { reference: TypePath },
    Natural { value: String },
}

/// The kind of one field of an indexed primitive's wire form. The table
/// spells the kinds as the kernel's `Source.WireKind.wire` does: `path`,
/// `object_type`, `coordinate`, `polynomial`, `pullback_mode` and `natural`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WireKind {
    /// An unresolved declaration path.
    Path,
    /// An object type `(domain, marker)`.
    ObjectType,
    /// A coordinate name, possibly qualified.
    Coordinate,
    /// An unexpanded polynomial expression.
    Polynomial,
    /// How a cotangent pullback obtains forward values.
    PullbackMode,
    /// A natural number as an unsigned decimal string, such as the index of
    /// a frame component (Stage 4). The kernel bounds its digits.
    Natural,
}

/// The wire form of one indexed primitive: the `op`, whether it is one of the
/// Stage 2 and later forms, and the exact fields in wire order. `src/primitive_table.rs`
/// holds one family per op, generated from the kernel's `families`
/// (`lean-kernel/VastitasKernel/IndexedPrimitiveFamilies.lean`) by
/// `scripts/check_primitive_table.py`; no other Rust table lists the ops.
#[derive(Debug, PartialEq, Eq)]
pub struct PrimitiveFamily {
    pub op: &'static str,
    pub algebraic: bool,
    pub fields: &'static [(&'static str, WireKind)],
}

/// Every indexed primitive family, in the kernel's order.
pub fn primitive_families() -> &'static [PrimitiveFamily] {
    crate::primitive_table::FAMILIES
}

/// The family of the wire `op`, if the table has one.
pub fn primitive_family(op: &str) -> Option<&'static PrimitiveFamily> {
    primitive_families().iter().find(|family| family.op == op)
}

/// The value of one field of a primitive. It serializes as the bare value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WireValue {
    Path(TypePath),
    ObjectType(ObjectType),
    Coordinate(String),
    Polynomial(PolyExpr),
    PullbackMode(PullbackMode),
    /// An unsigned decimal string, serialized as the bare string.
    Natural(String),
}

impl WireValue {
    pub fn kind(&self) -> WireKind {
        match self {
            WireValue::Path(_) => WireKind::Path,
            WireValue::ObjectType(_) => WireKind::ObjectType,
            WireValue::Coordinate(_) => WireKind::Coordinate,
            WireValue::Polynomial(_) => WireKind::Polynomial,
            WireValue::PullbackMode(_) => WireKind::PullbackMode,
            WireValue::Natural(_) => WireKind::Natural,
        }
    }

    fn from_json(kind: WireKind, value: serde_json::Value) -> serde_json::Result<Self> {
        Ok(match kind {
            WireKind::Path => WireValue::Path(serde_json::from_value(value)?),
            WireKind::ObjectType => WireValue::ObjectType(serde_json::from_value(value)?),
            WireKind::Coordinate => WireValue::Coordinate(serde_json::from_value(value)?),
            WireKind::Polynomial => WireValue::Polynomial(serde_json::from_value(value)?),
            WireKind::PullbackMode => WireValue::PullbackMode(serde_json::from_value(value)?),
            WireKind::Natural => WireValue::Natural(serde_json::from_value(value)?),
        })
    }
}

impl Serialize for WireValue {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            WireValue::Path(path) => path.serialize(serializer),
            WireValue::ObjectType(object) => object.serialize(serializer),
            WireValue::Coordinate(name) => name.serialize(serializer),
            WireValue::Polynomial(expression) => expression.serialize(serializer),
            WireValue::PullbackMode(mode) => mode.serialize(serializer),
            WireValue::Natural(value) => value.serialize(serializer),
        }
    }
}

/// An indexed primitive binding: a family of the table and one value per
/// field. `Primitive::new` admits exactly the family's fields, so a binding
/// never carries an op or a field that the table does not know.
#[derive(Clone, PartialEq, Eq)]
pub struct Primitive {
    family: &'static PrimitiveFamily,
    values: Vec<WireValue>,
}

impl Primitive {
    /// The binding `op(fields)`. The table must have `op`, and `fields` must
    /// be its fields, with their names and kinds, in wire order.
    pub fn new(op: &str, fields: Vec<(&str, WireValue)>) -> Result<Self, String> {
        let family =
            primitive_family(op).ok_or_else(|| format!("unknown indexed primitive `{op}`"))?;
        let expected: Vec<&str> = family.fields.iter().map(|(name, _)| *name).collect();
        let given: Vec<&str> = fields.iter().map(|(name, _)| *name).collect();
        if given != expected {
            return Err(format!(
                "`{op}` takes the fields {expected:?} in this order, not {given:?}"
            ));
        }
        let mut values = Vec::with_capacity(fields.len());
        for (&(name, kind), (_, value)) in family.fields.iter().zip(fields) {
            if value.kind() != kind {
                return Err(format!(
                    "the field `{name}` of `{op}` is {kind:?}, not {:?}",
                    value.kind()
                ));
            }
            values.push(value);
        }
        Ok(Primitive { family, values })
    }

    pub fn family(&self) -> &'static PrimitiveFamily {
        self.family
    }

    pub fn op(&self) -> &'static str {
        self.family.op
    }

    /// The fields with their values, in wire order.
    pub fn fields(&self) -> impl Iterator<Item = (&'static str, &WireValue)> + '_ {
        self.family
            .fields
            .iter()
            .map(|(name, _)| *name)
            .zip(&self.values)
    }

    pub fn field(&self, name: &str) -> Option<&WireValue> {
        self.fields()
            .find(|(field, _)| *field == name)
            .map(|(_, value)| value)
    }
}

impl fmt::Debug for Primitive {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Primitive")
            .field("op", &self.op())
            .field("fields", &self.fields().collect::<Vec<_>>())
            .finish()
    }
}

/// `{"op": op, field: value, …}` with the fields in wire order: the object
/// that the former `#[serde(tag = "op")]` enum wrote, byte for byte.
impl Serialize for Primitive {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut object = serializer.serialize_map(Some(1 + self.values.len()))?;
        object.serialize_entry("op", self.op())?;
        for (name, value) in self.fields() {
            object.serialize_entry(name, value)?;
        }
        object.end()
    }
}

/// Reads what `Serialize` writes. Like the former enum, it requires the
/// family's fields and ignores any other field.
impl<'de> Deserialize<'de> for Primitive {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let mut object = serde_json::Map::<String, serde_json::Value>::deserialize(deserializer)?;
        let op = match object.remove("op") {
            Some(serde_json::Value::String(op)) => op,
            Some(_) => return Err(D::Error::custom("`op` must be a string")),
            None => return Err(D::Error::missing_field("op")),
        };
        let family = primitive_family(&op)
            .ok_or_else(|| D::Error::custom(format!("unknown indexed primitive `{op}`")))?;
        let mut values = Vec::with_capacity(family.fields.len());
        for &(name, kind) in family.fields {
            let value = object
                .remove(name)
                .ok_or_else(|| D::Error::missing_field(name))?;
            values.push(WireValue::from_json(kind, value).map_err(D::Error::custom)?);
        }
        Ok(Primitive { family, values })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn path(name: &str) -> TypePath {
        TypePath {
            path: vec![name.to_string()],
            span: Span {
                start: 0,
                end: 0,
                line: 1,
                column: 1,
            },
        }
    }

    fn primitive(op: &str, fields: Vec<(&str, WireValue)>) -> DeclarationBody {
        DeclarationBody::Primitive {
            binding: Primitive::new(op, fields).unwrap(),
        }
    }

    fn paths(names: &[(&'static str, &str)]) -> Vec<(&'static str, WireValue)> {
        names
            .iter()
            .map(|&(field, name)| (field, WireValue::Path(path(name))))
            .collect()
    }

    #[test]
    fn every_smooth_form_is_algebraic() {
        let forms = [
            DeclarationBody::SmoothAffine {
                implementation: path("SmoothR"),
                dimension: "1".into(),
                coordinates: vec!["t".into()],
            },
            DeclarationBody::Implementation {
                marker: path("CInfReal"),
                representation: Representation::SmoothAffine,
                capabilities: Vec::new(),
            },
            DeclarationBody::Family {
                parameters: Vec::new(),
                constraints: Vec::new(),
                representation: FamilyRepresentation::Smooth,
            },
            DeclarationBody::Family {
                parameters: Vec::new(),
                constraints: vec![Constraint::Canonical { object: 0 }],
                representation: FamilyRepresentation::Token,
            },
            primitive("smooth_compose", paths(&[("family", "Smooth")])),
            primitive("smooth_equal", paths(&[("family", "Smooth")])),
            primitive("smooth_composite", paths(&[("family", "Smooth")])),
            primitive(
                "smooth_int_point",
                paths(&[("family", "Smooth"), ("object", "Line"), ("point", "Pt")]),
            ),
            primitive(
                "fiber_vector",
                paths(&[
                    ("family", "Cotangent"),
                    ("map_family", "Smooth"),
                    ("object", "Line"),
                ]),
            ),
            primitive(
                "fiber_at",
                paths(&[("family", "Cotangent"), ("map_family", "Smooth")]),
            ),
            primitive("fiber_equal", paths(&[("family", "Cotangent")])),
            primitive(
                "fiber_component",
                vec![
                    ("family", WireValue::Path(path("Cotangent"))),
                    ("object", WireValue::Path(path("Line"))),
                    ("coordinate", WireValue::Coordinate("t".into())),
                ],
            ),
            primitive(
                "fiber_pairing",
                paths(&[("cotangent", "Cotangent"), ("tangent", "Tangent")]),
            ),
            primitive(
                "cotangent_pullback",
                vec![
                    ("map_family", WireValue::Path(path("Smooth"))),
                    ("cotangent", WireValue::Path(path("Cotangent"))),
                    ("mode", WireValue::PullbackMode(PullbackMode::Recomputed)),
                ],
            ),
            primitive(
                "differential",
                paths(&[
                    ("map_family", "Smooth"),
                    ("cotangent", "Cotangent"),
                    ("line", "Line"),
                ]),
            ),
            primitive(
                "linearize",
                paths(&[("map_family", "Smooth"), ("tape", "Tape")]),
            ),
            primitive(
                "cotangent_backward",
                paths(&[("tape", "Tape"), ("cotangent", "Cotangent")]),
            ),
            primitive(
                "flat",
                paths(&[
                    ("tangent", "Tangent"),
                    ("cotangent", "Cotangent"),
                    ("metric", "Skew"),
                ]),
            ),
            primitive(
                "sharp",
                paths(&[
                    ("cotangent", "Cotangent"),
                    ("tangent", "Tangent"),
                    ("metric", "Skew"),
                    ("evidence", "SkewInvertible"),
                ]),
            ),
            DeclarationBody::Metric {
                family: path("MetricForm"),
                indices: vec![path("Plane")],
                gram: MetricGram::Euclidean,
            },
            DeclarationBody::Metric {
                family: path("MetricForm"),
                indices: vec![path("Plane")],
                gram: MetricGram::Gram {
                    rows: vec![vec![PolyExpr::Natural { value: "1".into() }]],
                },
            },
            DeclarationBody::Evidence {
                metric: path("Skew"),
                evidence: EvidenceKind::Nondegenerate,
            },
            DeclarationBody::Evidence {
                metric: path("Skew"),
                evidence: EvidenceKind::Riemannian,
            },
        ];
        for form in &forms {
            assert!(form.is_algebraic(), "{form:?}");
        }
        for representation in [
            FamilyRepresentation::Cotangent,
            FamilyRepresentation::Tangent,
            FamilyRepresentation::Tape,
            FamilyRepresentation::MetricForm,
        ] {
            let family = DeclarationBody::Family {
                parameters: Vec::new(),
                constraints: Vec::new(),
                representation,
            };
            assert!(family.is_algebraic(), "{family:?}");
        }
    }

    /// The frame and physical dimension forms of Stage 4 serialize to the
    /// wire shapes that the kernel decodes, read back, and are algebraic.
    #[test]
    fn every_frame_and_dimension_form_serializes_to_its_wire_shape_and_is_algebraic() {
        let p = |name: &str| serde_json::to_value(path(name)).unwrap();
        let natural = |value: &str| PolyExpr::Natural {
            value: value.into(),
        };
        let coordinate = |name: &str| PolyExpr::Coordinate { name: name.into() };
        let factor = |base: &str, exponent: &str| DimensionFactor {
            base: path(base),
            exponent: exponent.into(),
        };
        let cases: Vec<(DeclarationBody, serde_json::Value)> = vec![
            (
                DeclarationBody::Frame {
                    family: path("Frame"),
                    indices: vec![path("Plane")],
                    columns: FrameColumns::Columns {
                        columns: vec![
                            vec![natural("1"), natural("0")],
                            vec![coordinate("x"), natural("2")],
                        ],
                    },
                    inverse: Some(FrameColumns::Columns {
                        columns: vec![vec![natural("1")]],
                    }),
                },
                serde_json::json!({
                    "kind": "frame", "family": p("Frame"), "indices": [p("Plane")],
                    "columns": {"kind": "columns", "columns": [
                        [{"op": "natural", "value": "1"}, {"op": "natural", "value": "0"}],
                        [{"op": "coordinate", "name": "x"}, {"op": "natural", "value": "2"}]]},
                    "inverse": {"kind": "columns", "columns": [[{"op": "natural", "value": "1"}]]}
                }),
            ),
            (
                DeclarationBody::Frame {
                    family: path("Frame"),
                    indices: vec![path("Plane")],
                    columns: FrameColumns::Coordinates,
                    inverse: None,
                },
                serde_json::json!({
                    "kind": "frame", "family": p("Frame"), "indices": [p("Plane")],
                    "columns": {"kind": "coordinates"}, "inverse": null
                }),
            ),
            (
                DeclarationBody::BaseDimension,
                serde_json::json!({"kind": "base_dimension"}),
            ),
            (
                DeclarationBody::Quantity {
                    dimension: vec![factor("L", "1"), factor("T", "-2")],
                },
                serde_json::json!({"kind": "quantity", "dimension": [
                    {"base": p("L"), "exponent": "1"}, {"base": p("T"), "exponent": "-2"}]}),
            ),
            (
                DeclarationBody::Reading {
                    family: path("Reading"),
                    indices: vec![path("Chart")],
                    quantities: vec![
                        ReadingEntry {
                            coordinate: "x".into(),
                            quantity: path("Length"),
                        },
                        ReadingEntry {
                            coordinate: "t".into(),
                            quantity: path("Time"),
                        },
                    ],
                },
                serde_json::json!({
                    "kind": "reading", "family": p("Reading"), "indices": [p("Chart")],
                    "quantities": [{"coordinate": "x", "quantity": p("Length")},
                        {"coordinate": "t", "quantity": p("Time")}]
                }),
            ),
            (
                DeclarationBody::Scale {
                    quantity: path("Length"),
                    magnitude: natural("3"),
                },
                serde_json::json!({"kind": "scale", "quantity": p("Length"),
                    "magnitude": {"op": "natural", "value": "3"}}),
            ),
            (
                DeclarationBody::PhysicalMetric {
                    family: path("PhysicalMetric"),
                    indices: vec![path("Chart")],
                    metric: path("G"),
                    reading: path("phys"),
                    value: None,
                    entries: PhysicalGram::Euclidean,
                },
                serde_json::json!({
                    "kind": "physical_metric", "family": p("PhysicalMetric"), "indices": [p("Chart")],
                    "metric": p("G"), "reading": p("phys"), "value": null,
                    "entries": {"kind": "euclidean"}
                }),
            ),
            (
                DeclarationBody::PhysicalMetric {
                    family: path("PhysicalMetric"),
                    indices: vec![path("Chart")],
                    metric: path("G"),
                    reading: path("phys"),
                    value: Some(vec![factor("L", "2")]),
                    entries: PhysicalGram::Gram {
                        rows: vec![vec![ScaleMonomial {
                            coefficient: natural("1"),
                            factors: vec![ScaleFactor {
                                scale: path("l0"),
                                exponent: "-2".into(),
                            }],
                        }]],
                    },
                },
                serde_json::json!({
                    "kind": "physical_metric", "family": p("PhysicalMetric"), "indices": [p("Chart")],
                    "metric": p("G"), "reading": p("phys"), "value": [{"base": p("L"), "exponent": "2"}],
                    "entries": {"kind": "gram", "rows": [[{"coefficient": {"op": "natural", "value": "1"},
                        "factors": [{"scale": p("l0"), "exponent": "-2"}]}]]}
                }),
            ),
            (
                DeclarationBody::PhysicalMetric {
                    family: path("PhysicalMetric"),
                    indices: vec![path("Chart")],
                    metric: path("G"),
                    reading: path("phys"),
                    value: None,
                    entries: PhysicalGram::Normalized {
                        scales: vec![CoordinateScale {
                            coordinate: "x".into(),
                            scale: path("l0"),
                        }],
                    },
                },
                serde_json::json!({
                    "kind": "physical_metric", "family": p("PhysicalMetric"), "indices": [p("Chart")],
                    "metric": p("G"), "reading": p("phys"), "value": null,
                    "entries": {"kind": "normalized", "scales": [{"coordinate": "x", "scale": p("l0")}]}
                }),
            ),
            (
                DeclarationBody::Family {
                    parameters: vec![Parameter::Frame {
                        family: path("Frame"),
                    }],
                    constraints: Vec::new(),
                    representation: FamilyRepresentation::Token,
                },
                serde_json::json!({
                    "kind": "family", "parameters": [{"kind": "frame", "family": p("Frame")}],
                    "constraints": [], "representation": "token"
                }),
            ),
        ];
        for (body, expected) in &cases {
            assert!(body.is_algebraic(), "{body:?}");
            let json = serde_json::to_value(body).unwrap();
            assert_eq!(&json, expected, "{body:?}");
            assert_eq!(
                &serde_json::from_value::<DeclarationBody>(json).unwrap(),
                body
            );
        }
        for (representation, wire) in [
            (FamilyRepresentation::Frame, "frame"),
            (FamilyRepresentation::FrameVector, "frame_vector"),
            (FamilyRepresentation::FrameCovector, "frame_covector"),
            (FamilyRepresentation::FrameMap, "frame_map"),
            (FamilyRepresentation::Reading, "reading"),
            (FamilyRepresentation::PhysicalMetric, "physical_metric"),
        ] {
            assert_eq!(serde_json::to_value(representation).unwrap(), wire);
            let family = DeclarationBody::Family {
                parameters: Vec::new(),
                constraints: Vec::new(),
                representation,
            };
            assert!(family.is_algebraic(), "{family:?}");
        }
        // The nested records with fields reject an unknown field, as the
        // kernel does. As for `MetricGram`, serde does not check the fields of
        // a variant without fields.
        let unknown = [
            serde_json::json!({"kind": "frame", "family": p("Frame"), "indices": [],
                "columns": {"kind": "columns", "columns": [], "extra": 1}, "inverse": null}),
            serde_json::json!({"kind": "quantity", "dimension": [
                {"base": p("L"), "exponent": "1", "extra": 1}]}),
            serde_json::json!({"kind": "reading", "family": p("Reading"), "indices": [],
                "quantities": [{"coordinate": "x", "quantity": p("Length"), "extra": 1}]}),
            serde_json::json!({"kind": "physical_metric", "family": p("PhysicalMetric"), "indices": [],
                "metric": p("G"), "reading": p("phys"), "value": null,
                "entries": {"kind": "gram", "rows": [], "extra": 1}}),
            serde_json::json!({"kind": "physical_metric", "family": p("PhysicalMetric"), "indices": [],
                "metric": p("G"), "reading": p("phys"), "value": null,
                "entries": {"kind": "gram", "rows": [[{"coefficient": {"op": "natural", "value": "1"},
                    "factors": [{"scale": p("l0"), "exponent": "-2", "extra": 1}]}]]}}),
            serde_json::json!({"kind": "physical_metric", "family": p("PhysicalMetric"), "indices": [],
                "metric": p("G"), "reading": p("phys"), "value": null,
                "entries": {"kind": "normalized", "scales": [{"coordinate": "x", "scale": p("l0"), "extra": 1}]}}),
        ];
        for json in unknown {
            assert!(
                serde_json::from_value::<DeclarationBody>(json.clone()).is_err(),
                "{json}"
            );
        }
    }

    /// The spectral forms of Stage 5 serialize to the wire shapes that the
    /// kernel decodes, read back, and are algebraic. No form has a field for a
    /// certificate.
    #[test]
    fn every_spectral_form_serializes_to_its_wire_shape_and_is_algebraic() {
        let p = |name: &str| serde_json::to_value(path(name)).unwrap();
        let natural = |value: &str| PolyExpr::Natural {
            value: value.into(),
        };
        let coordinate = |name: &str| PolyExpr::Coordinate { name: name.into() };
        let cases: Vec<(DeclarationBody, serde_json::Value)> = vec![
            (
                DeclarationBody::FreeModule {
                    family: path("FreeModule"),
                    indices: vec![path("Plane")],
                    basis: vec!["e1".into(), "e2".into()],
                },
                serde_json::json!({
                    "kind": "free_module", "family": p("FreeModule"), "indices": [p("Plane")],
                    "basis": ["e1", "e2"]
                }),
            ),
            (
                DeclarationBody::Endomorphism {
                    family: path("Endomorphism"),
                    indices: vec![path("Plane")],
                    module: path("V"),
                    rows: vec![
                        vec![coordinate("x"), coordinate("y")],
                        vec![
                            coordinate("y"),
                            PolyExpr::Neg {
                                operand: Box::new(coordinate("x")),
                            },
                        ],
                    ],
                    symmetric: true,
                },
                serde_json::json!({
                    "kind": "endomorphism", "family": p("Endomorphism"), "indices": [p("Plane")],
                    "module": p("V"), "rows": [
                        [{"op": "coordinate", "name": "x"}, {"op": "coordinate", "name": "y"}],
                        [{"op": "coordinate", "name": "y"},
                            {"op": "neg", "operand": {"op": "coordinate", "name": "x"}}]],
                    "symmetric": true
                }),
            ),
            (
                DeclarationBody::Spectrum {
                    family: path("Spectrum"),
                    indices: vec![path("Plane")],
                    endomorphism: path("H"),
                    fiber: "t".into(),
                },
                serde_json::json!({
                    "kind": "spectrum", "family": p("Spectrum"), "indices": [p("Plane")],
                    "endomorphism": p("H"), "fiber": "t"
                }),
            ),
            (
                DeclarationBody::Branch {
                    family: path("Branch"),
                    indices: vec![path("Plane")],
                    spectrum: path("S"),
                    localize: natural("1"),
                    witness: coordinate("t"),
                    exponent: "1".into(),
                },
                serde_json::json!({
                    "kind": "branch", "family": p("Branch"), "indices": [p("Plane")],
                    "spectrum": p("S"), "localize": {"op": "natural", "value": "1"},
                    "witness": {"op": "coordinate", "name": "t"}, "exponent": "1"
                }),
            ),
            (
                DeclarationBody::Morphism {
                    family: path("Smooth"),
                    indices: vec![path("Plane"), path("Line")],
                    definition: MorphismDefinition::TracePower {
                        endomorphism: path("H"),
                        power: "2".into(),
                    },
                },
                serde_json::json!({
                    "kind": "morphism", "family": p("Smooth"), "indices": [p("Plane"), p("Line")],
                    "definition": {"kind": "trace_power", "endomorphism": p("H"), "power": "2"}
                }),
            ),
            (
                DeclarationBody::Morphism {
                    family: path("Smooth"),
                    indices: vec![path("Plane"), path("Line")],
                    definition: MorphismDefinition::CharCoefficient {
                        spectrum: path("S"),
                        index: "0".into(),
                    },
                },
                serde_json::json!({
                    "kind": "morphism", "family": p("Smooth"), "indices": [p("Plane"), p("Line")],
                    "definition": {"kind": "char_coefficient", "spectrum": p("S"), "index": "0"}
                }),
            ),
            (
                primitive(
                    "annihilates",
                    vec![
                        ("map_family", WireValue::Path(path("Smooth"))),
                        ("spectrum", WireValue::Path(path("S"))),
                        ("element", WireValue::Polynomial(coordinate("t"))),
                    ],
                ),
                serde_json::json!({
                    "kind": "primitive", "binding": {"op": "annihilates", "map_family": p("Smooth"),
                        "spectrum": p("S"), "element": {"op": "coordinate", "name": "t"}}
                }),
            ),
            (
                primitive(
                    "action_entry",
                    vec![
                        ("map_family", WireValue::Path(path("Smooth"))),
                        ("spectrum", WireValue::Path(path("S"))),
                        ("element", WireValue::Polynomial(coordinate("t"))),
                        ("row", WireValue::Coordinate("e1".into())),
                        ("column", WireValue::Coordinate("e2".into())),
                    ],
                ),
                serde_json::json!({
                    "kind": "primitive", "binding": {"op": "action_entry", "map_family": p("Smooth"),
                        "spectrum": p("S"), "element": {"op": "coordinate", "name": "t"},
                        "row": "e1", "column": "e2"}
                }),
            ),
            (
                primitive(
                    "on_branch",
                    paths(&[("map_family", "Smooth"), ("line", "Line"), ("branch", "B")]),
                ),
                serde_json::json!({
                    "kind": "primitive", "binding": {"op": "on_branch", "map_family": p("Smooth"),
                        "line": p("Line"), "branch": p("B")}
                }),
            ),
            (
                primitive(
                    "branch_differential",
                    paths(&[
                        ("map_family", "Smooth"),
                        ("cotangent", "Cotangent"),
                        ("line", "Line"),
                        ("branch", "B"),
                    ]),
                ),
                serde_json::json!({
                    "kind": "primitive", "binding": {"op": "branch_differential",
                        "map_family": p("Smooth"), "cotangent": p("Cotangent"), "line": p("Line"),
                        "branch": p("B")}
                }),
            ),
            (
                primitive(
                    "branch_projector",
                    vec![
                        ("map_family", WireValue::Path(path("Smooth"))),
                        ("line", WireValue::Path(path("Line"))),
                        ("branch", WireValue::Path(path("B"))),
                        ("row", WireValue::Coordinate("e1".into())),
                        ("column", WireValue::Coordinate("e2".into())),
                    ],
                ),
                serde_json::json!({
                    "kind": "primitive", "binding": {"op": "branch_projector", "map_family": p("Smooth"),
                        "line": p("Line"), "branch": p("B"), "row": "e1", "column": "e2"}
                }),
            ),
        ];
        for (body, expected) in &cases {
            assert!(body.is_algebraic(), "{body:?}");
            let json = serde_json::to_value(body).unwrap();
            assert_eq!(&json, expected, "{body:?}");
            assert_eq!(
                &serde_json::from_value::<DeclarationBody>(json).unwrap(),
                body
            );
        }
        for (representation, wire) in [
            (FamilyRepresentation::FreeModule, "free_module"),
            (FamilyRepresentation::Endomorphism, "endomorphism"),
            (FamilyRepresentation::Spectrum, "spectrum"),
            (FamilyRepresentation::Branch, "branch"),
        ] {
            assert_eq!(serde_json::to_value(representation).unwrap(), wire);
            let family = DeclarationBody::Family {
                parameters: Vec::new(),
                constraints: Vec::new(),
                representation,
            };
            assert!(family.is_algebraic(), "{family:?}");
        }
        // A morphism definition rejects an unknown field, as the kernel does.
        let certificate = serde_json::json!({"kind": "trace_power", "endomorphism": p("H"),
            "power": "2", "certificate": []});
        assert!(serde_json::from_value::<MorphismDefinition>(certificate).is_err());
    }

    /// The Stage 6 forms (#841): the transition average of
    /// `std::linalg::spectral`, the convention and the model of
    /// `nature::model`, the calibration, the dataset and the comparison of
    /// `nature::errorbar`, their family representations and `average_at`
    /// serialize to the wire shapes that the kernel decodes and read back. The
    /// transition average, its family and `average_at` are algebraic; the
    /// model and data forms are not. No form has a field for a certificate. The nested
    /// records of a calibrated coordinate and of a data point reject an unknown
    /// field, as the kernel does; the frontend never decodes a request.
    #[test]
    fn every_stage6_form_serializes_to_its_wire_shape() {
        let p = |name: &str| serde_json::to_value(path(name)).unwrap();
        let natural = |value: &str| PolyExpr::Natural {
            value: value.into(),
        };
        let fraction = |numerator: &str, denominator: &str| PolyExpr::Fraction {
            numerator: numerator.into(),
            denominator: denominator.into(),
        };
        let coordinate = |name: &str| PolyExpr::Coordinate { name: name.into() };
        let n = |value: &str| serde_json::json!({"op": "natural", "value": value});
        let f = |numerator: &str, denominator: &str| serde_json::json!({"op": "fraction", "numerator": numerator, "denominator": denominator});
        let c = |name: &str| serde_json::json!({"op": "coordinate", "name": name});
        let cases: Vec<(DeclarationBody, serde_json::Value)> = vec![
            (
                DeclarationBody::TransitionAverage {
                    family: path("TransitionAverage"),
                    indices: vec![path("P")],
                    branch: path("B"),
                    from: "g".into(),
                    to: "e".into(),
                    numerator: coordinate("omega"),
                    denominator: coordinate("delta"),
                },
                serde_json::json!({
                    "kind": "transition_average", "family": p("TransitionAverage"),
                    "indices": [p("P")], "branch": p("B"), "from": "g", "to": "e",
                    "numerator": c("omega"), "denominator": c("delta")
                }),
            ),
            (
                DeclarationBody::Convention {
                    value: ConventionKind::HbarOne,
                },
                serde_json::json!({"kind": "convention", "value": "hbar_one"}),
            ),
            (
                DeclarationBody::Model {
                    family: path("Model"),
                    indices: vec![path("P")],
                    hamiltonian: path("H"),
                    reading: path("r"),
                    convention: path("c"),
                    prepare: "g".into(),
                    observe: "e".into(),
                    predicts: path("A"),
                    regime: "rotating-wave approximation".into(),
                },
                serde_json::json!({
                    "kind": "model", "family": p("Model"), "indices": [p("P")],
                    "hamiltonian": p("H"), "reading": p("r"), "convention": p("c"),
                    "prepare": "g", "observe": "e", "predicts": p("A"),
                    "regime": "rotating-wave approximation"
                }),
            ),
            (
                DeclarationBody::Calibration {
                    family: path("Calibration"),
                    indices: vec![path("P")],
                    parameters: vec![Calibrated {
                        coordinate: "omega".into(),
                        value: fraction("5", "2"),
                        uncertainty: fraction("1", "20"),
                    }],
                    method: CalibrationMethod::TypeB,
                    reference: "JCGM 100:2008".into(),
                    revision: "1".into(),
                },
                serde_json::json!({
                    "kind": "calibration", "family": p("Calibration"), "indices": [p("P")],
                    "parameters": [{"coordinate": "omega", "value": f("5", "2"),
                        "uncertainty": f("1", "20")}],
                    "method": "type_b", "reference": "JCGM 100:2008", "revision": "1"
                }),
            ),
            (
                DeclarationBody::Dataset {
                    family: path("Dataset"),
                    indices: vec![path("P")],
                    model: path("M"),
                    calibration: path("K"),
                    coverage: natural("2"),
                    points: vec![DataPoint {
                        coordinates: vec![PointCoordinate {
                            coordinate: "delta".into(),
                            value: natural("0"),
                        }],
                        value: fraction("1", "2"),
                        uncertainty: fraction("1", "50"),
                    }],
                },
                serde_json::json!({
                    "kind": "dataset", "family": p("Dataset"), "indices": [p("P")],
                    "model": p("M"), "calibration": p("K"), "coverage": n("2"),
                    "points": [{"coordinates": [{"coordinate": "delta", "value": n("0")}],
                        "value": f("1", "2"), "uncertainty": f("1", "50")}]
                }),
            ),
            (
                DeclarationBody::Comparison {
                    family: path("Comparison"),
                    indices: vec![path("P")],
                    dataset: path("D"),
                    calibration: path("K"),
                    fingerprint: "0123456789abcdef".into(),
                    verdict: Verdict::Consistent,
                },
                serde_json::json!({
                    "kind": "comparison", "family": p("Comparison"), "indices": [p("P")],
                    "dataset": p("D"), "calibration": p("K"),
                    "fingerprint": "0123456789abcdef", "verdict": "consistent"
                }),
            ),
            (
                primitive(
                    "average_at",
                    paths(&[("map_family", "Smooth"), ("line", "Line"), ("average", "A")]),
                ),
                serde_json::json!({
                    "kind": "primitive", "binding": {"op": "average_at", "map_family": p("Smooth"),
                        "line": p("Line"), "average": p("A")}
                }),
            ),
        ];
        for (body, expected) in &cases {
            let spectral = matches!(
                body,
                DeclarationBody::TransitionAverage { .. } | DeclarationBody::Primitive { .. }
            );
            assert_eq!(body.is_algebraic(), spectral, "{body:?}");
            let json = serde_json::to_value(body).unwrap();
            assert_eq!(&json, expected, "{body:?}");
            assert_eq!(
                &serde_json::from_value::<DeclarationBody>(json).unwrap(),
                body
            );
        }
        for (representation, wire) in [
            (
                FamilyRepresentation::TransitionAverage,
                "transition_average",
            ),
            (FamilyRepresentation::Model, "model"),
            (FamilyRepresentation::Calibration, "calibration"),
            (FamilyRepresentation::Dataset, "dataset"),
            (FamilyRepresentation::Comparison, "comparison"),
        ] {
            assert_eq!(serde_json::to_value(representation).unwrap(), wire);
            let family = DeclarationBody::Family {
                parameters: Vec::new(),
                constraints: Vec::new(),
                representation,
            };
            assert_eq!(
                family.is_algebraic(),
                representation == FamilyRepresentation::TransitionAverage,
                "{family:?}"
            );
        }
        for (method, wire) in [
            (CalibrationMethod::TypeA, "type_a"),
            (CalibrationMethod::TypeB, "type_b"),
        ] {
            assert_eq!(serde_json::to_value(method).unwrap(), wire);
        }
        assert_eq!(
            serde_json::to_value(Verdict::Inconsistent).unwrap(),
            "inconsistent"
        );
        // A calibrated coordinate and a point reject an unknown field, as
        // the kernel does; no record carries a certificate or a fingerprint
        // that the kernel computes.
        let unit = serde_json::json!({"coordinate": "omega", "value": n("1"),
            "uncertainty": n("1"), "unit": "Hz"});
        assert!(serde_json::from_value::<Calibrated>(unit).is_err());
        let weight = serde_json::json!({"coordinates": [], "value": n("1"),
            "uncertainty": n("1"), "weight": n("1")});
        assert!(serde_json::from_value::<DataPoint>(weight).is_err());
    }

    #[test]
    fn descriptor_forms_are_not_algebraic() {
        let forms = [
            DeclarationBody::Implementation {
                marker: path("CInfReal"),
                representation: Representation::AffineDescriptor,
                capabilities: Vec::new(),
            },
            DeclarationBody::Family {
                parameters: Vec::new(),
                constraints: vec![Constraint::SameBase { left: 0, right: 1 }],
                representation: FamilyRepresentation::Morphism,
            },
            primitive("compose", paths(&[("map_family", "Morphism")])),
        ];
        for form in &forms {
            assert!(!form.is_algebraic(), "{form:?}");
        }
    }

    /// The allow-list of the algebraic ops before the table (#622): `is_algebraic` now
    /// reads the generated table, which must keep these ops, and only these,
    /// algebraic, and keep the seven Stage 1 ops.
    #[test]
    fn the_table_keeps_the_former_allow_list() {
        let stage1 = [
            "descriptor",
            "global",
            "origin",
            "identity",
            "dim",
            "compose",
            "apply",
        ];
        let mut algebraic = vec![
            "relative_compose",
            "relative_view",
            "relative_equal",
            "relative_coefficient",
            "relative_int_point",
            "relative_pair",
            "smooth_compose",
            "smooth_equal",
            "smooth_composite",
            "smooth_int_point",
            "fiber_vector",
            "fiber_at",
            "fiber_equal",
            "fiber_component",
            "fiber_pairing",
            "cotangent_pullback",
            "differential",
            "linearize",
            "cotangent_backward",
            "flat",
            "sharp",
            "frame_encode",
            "frame_decode",
            "frame_vector",
            "frame_matrix",
            "frame_transition",
            "frame_apply",
            "frame_coapply",
            "frame_compose",
            "frame_pairing",
            "frame_component",
            "frame_entry",
            "frame_equal",
            "frame_at",
            "annihilates",
            "action_entry",
            "on_branch",
            "branch_differential",
            "branch_projector",
            "average_at",
        ];
        let mut table: Vec<&str> = primitive_families()
            .iter()
            .filter(|family| family.algebraic)
            .map(|family| family.op)
            .collect();
        algebraic.sort_unstable();
        table.sort_unstable();
        assert_eq!(table, algebraic);
        let mut ordinary: Vec<&str> = primitive_families()
            .iter()
            .filter(|family| !family.algebraic)
            .map(|family| family.op)
            .collect();
        ordinary.sort_unstable();
        let mut stage1 = stage1.to_vec();
        stage1.sort_unstable();
        assert_eq!(ordinary, stage1);
        let mut ops: Vec<&str> = primitive_families().iter().map(|f| f.op).collect();
        ops.sort_unstable();
        ops.dedup();
        assert_eq!(ops.len(), primitive_families().len(), "duplicate op");
    }

    #[test]
    fn a_binding_has_exactly_the_fields_of_its_family() {
        let pullback =
            |fields: Vec<(&str, WireValue)>| Primitive::new("cotangent_pullback", fields);
        let mode = || WireValue::PullbackMode(PullbackMode::Saved);
        let accepted = pullback(vec![
            ("map_family", WireValue::Path(path("Smooth"))),
            ("cotangent", WireValue::Path(path("Cotangent"))),
            ("mode", mode()),
        ])
        .unwrap();
        assert_eq!(accepted.op(), "cotangent_pullback");
        assert_eq!(
            accepted.field("mode"),
            Some(&WireValue::PullbackMode(PullbackMode::Saved))
        );
        assert_eq!(accepted.field("line"), None);
        let rejected = [
            // An op the table does not know.
            Primitive::new("gradient", paths(&[("map_family", "Smooth")])),
            // A missing, an extra, a foreign and a reordered field.
            pullback(paths(&[
                ("map_family", "Smooth"),
                ("cotangent", "Cotangent"),
            ])),
            pullback(vec![
                ("map_family", WireValue::Path(path("Smooth"))),
                ("cotangent", WireValue::Path(path("Cotangent"))),
                ("mode", mode()),
                ("line", WireValue::Path(path("Line"))),
            ]),
            pullback(vec![
                ("map_family", WireValue::Path(path("Smooth"))),
                ("covector", WireValue::Path(path("Cotangent"))),
                ("mode", mode()),
            ]),
            pullback(vec![
                ("cotangent", WireValue::Path(path("Cotangent"))),
                ("map_family", WireValue::Path(path("Smooth"))),
                ("mode", mode()),
            ]),
            // A field of the wrong kind.
            pullback(paths(&[
                ("map_family", "Smooth"),
                ("cotangent", "Cotangent"),
                ("mode", "Saved"),
            ])),
        ];
        for result in rejected {
            assert!(result.is_err(), "{result:?}");
        }
    }

    /// The object is `{"op": …}` followed by the fields in table order, and
    /// it reads back to the same binding.
    #[test]
    fn a_binding_serializes_in_table_order_and_reads_back() {
        let binding = Primitive::new(
            "relative_coefficient",
            vec![
                ("family", WireValue::Path(path("Over"))),
                ("source", WireValue::Path(path("D"))),
                ("target", WireValue::Path(path("Line"))),
                ("coordinate", WireValue::Coordinate("X::x".into())),
                (
                    "monomial",
                    WireValue::Polynomial(PolyExpr::Coordinate { name: "e".into() }),
                ),
            ],
        )
        .unwrap();
        let path_json = |name: &str| serde_json::to_string(&path(name)).unwrap();
        let expected = format!(
            r#"{{"op":"relative_coefficient","family":{},"source":{},"target":{},"coordinate":"X::x","monomial":{{"op":"coordinate","name":"e"}}}}"#,
            path_json("Over"),
            path_json("D"),
            path_json("Line"),
        );
        let json = serde_json::to_string(&binding).unwrap();
        assert_eq!(json, expected);
        assert_eq!(serde_json::from_str::<Primitive>(&json).unwrap(), binding);
        let unknown = r#"{"op":"gradient","map_family":{"path":["S"],"span":{"start":0,"end":0,"line":1,"column":1}}}"#;
        assert!(serde_json::from_str::<Primitive>(unknown).is_err());
    }
}
