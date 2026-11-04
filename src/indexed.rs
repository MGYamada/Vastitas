//! Unresolved declaration-driven source IR. The kernel reconstructs every ID
//! from its enclosing package/module and independently checks each contract.

use crate::ir::{Span, TypePath};
use serde::{Deserialize, Serialize};

/// A library's explicit export of the finite legacy geometry dialect.
/// Paths remain unresolved until the independent kernel checks every role.
#[derive(Debug, Deserialize, Serialize)]
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

#[derive(Debug, Deserialize, Serialize)]
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
    /// A presented affine object `spec[generators] relations(...) over base by(...)`
    /// (protocol 9). The kernel expands, bounds and checks every polynomial.
    Affine {
        implementation: TypePath,
        generators: Vec<String>,
        relations: Vec<PolyExpr>,
        base: Option<TypePath>,
        bindings: Vec<Binding>,
    },
    /// A declared morphism `family<X, Y, S>` over a base (protocol 9).
    Morphism {
        family: TypePath,
        indices: Vec<TypePath>,
        definition: MorphismDefinition,
    },
    /// The fiber product `left ×_B right` over `left`'s base (protocol 9).
    AffineFiber {
        implementation: TypePath,
        left: TypePath,
        right: TypePath,
        via: Option<FiberVia>,
    },
    /// The principal open `D(element)` of `object` (protocol 9).
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
    /// A smooth object `Affine(dimension)[coordinates]` (protocol 9). The
    /// kernel checks the dimension against the coordinates.
    SmoothAffine {
        implementation: TypePath,
        dimension: String,
        coordinates: Vec<String>,
    },
}

/// A chosen isomorphism between separately declared fiber bases.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FiberVia {
    pub forward: Vec<Binding>,
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
}

impl DeclarationBody {
    /// Stage 2 algebraic and Stage 3 smooth forms. They exist only in
    /// protocol 9.
    pub fn is_algebraic(&self) -> bool {
        match self {
            DeclarationBody::Affine { .. }
            | DeclarationBody::Morphism { .. }
            | DeclarationBody::AffineFiber { .. }
            | DeclarationBody::AffineLocalization { .. }
            | DeclarationBody::Iso { .. }
            | DeclarationBody::Cartesian { .. }
            | DeclarationBody::SmoothAffine { .. } => true,
            DeclarationBody::Primitive { binding } => matches!(
                binding,
                Primitive::RelativeCompose { .. }
                    | Primitive::RelativeView { .. }
                    | Primitive::RelativeEqual { .. }
                    | Primitive::RelativeCoefficient { .. }
                    | Primitive::RelativeIntPoint { .. }
                    | Primitive::RelativePair { .. }
                    | Primitive::SmoothCompose { .. }
                    | Primitive::SmoothEqual { .. }
                    | Primitive::SmoothComposite { .. }
                    | Primitive::SmoothIntPoint { .. }
                    | Primitive::FiberVector { .. }
                    | Primitive::FiberAt { .. }
                    | Primitive::FiberEqual { .. }
                    | Primitive::FiberComponent { .. }
                    | Primitive::FiberPairing { .. }
                    | Primitive::CotangentPullback { .. }
                    | Primitive::Differential { .. }
                    | Primitive::Linearize { .. }
                    | Primitive::CotangentBackward { .. }
            ),
            DeclarationBody::Implementation { representation, .. } => matches!(
                representation,
                Representation::PresentedAffine { .. } | Representation::SmoothAffine
            ),
            DeclarationBody::Family {
                constraints,
                representation,
                ..
            } => {
                matches!(
                    representation,
                    FamilyRepresentation::Relative
                        | FamilyRepresentation::Smooth
                        | FamilyRepresentation::Cotangent
                        | FamilyRepresentation::Tangent
                        | FamilyRepresentation::Tape
                ) || constraints.iter().any(|c| {
                    matches!(
                        c,
                        Constraint::Structural { .. } | Constraint::Canonical { .. }
                    )
                })
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
    /// The smooth real affine spaces `Affine(n)` (protocol 9).
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
    /// `Cotangent(X)`: covectors at points of a smooth object (protocol 9).
    Cotangent,
    /// `Tangent(X)`: vectors at points of a smooth object (protocol 9).
    Tangent,
    /// `Tape(X, Y)`: the saved forward values of a smooth map at a point
    /// (protocol 9). Only `linearize` constructs a tape.
    Tape,
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
    Object { domain: TypePath },
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum Primitive {
    Descriptor {
        implementation: TypePath,
    },
    Global {
        declaration: TypePath,
    },
    Origin {
        domain: ObjectType,
        point_family: TypePath,
        base_object: TypePath,
    },
    Identity {
        domain: ObjectType,
        map_family: TypePath,
    },
    Dimension {
        domain: ObjectType,
    },
    Compose {
        map_family: TypePath,
    },
    Apply {
        map_family: TypePath,
        point_family: TypePath,
    },
    RelativeCompose {
        family: TypePath,
    },
    RelativeView {
        family: TypePath,
        source: TypePath,
        target: TypePath,
    },
    RelativeEqual {
        family: TypePath,
    },
    RelativeCoefficient {
        family: TypePath,
        source: TypePath,
        target: TypePath,
        coordinate: String,
        monomial: PolyExpr,
    },
    RelativeIntPoint {
        family: TypePath,
        object: TypePath,
        base: TypePath,
    },
    RelativePair {
        family: TypePath,
        fiber: TypePath,
    },
    SmoothCompose {
        family: TypePath,
    },
    SmoothEqual {
        family: TypePath,
    },
    SmoothComposite {
        family: TypePath,
    },
    SmoothIntPoint {
        family: TypePath,
        object: TypePath,
        point: TypePath,
    },
    /// A fiber of `family` over `object` from a point in `map_family` and
    /// one integer per coordinate.
    FiberVector {
        family: TypePath,
        map_family: TypePath,
        object: TypePath,
    },
    FiberAt {
        family: TypePath,
        map_family: TypePath,
    },
    FiberEqual {
        family: TypePath,
    },
    /// The component of a fiber at the coordinate `coordinate` of `object`.
    FiberComponent {
        family: TypePath,
        object: TypePath,
        coordinate: String,
    },
    FiberPairing {
        cotangent: TypePath,
        tangent: TypePath,
    },
    CotangentPullback {
        map_family: TypePath,
        cotangent: TypePath,
        mode: PullbackMode,
    },
    /// `line` is a 1-dimensional smooth object.
    Differential {
        map_family: TypePath,
        cotangent: TypePath,
        line: TypePath,
    },
    Linearize {
        map_family: TypePath,
        tape: TypePath,
    },
    CotangentBackward {
        tape: TypePath,
        cotangent: TypePath,
    },
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

    fn primitive(binding: Primitive) -> DeclarationBody {
        DeclarationBody::Primitive { binding }
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
            primitive(Primitive::SmoothCompose {
                family: path("Smooth"),
            }),
            primitive(Primitive::SmoothEqual {
                family: path("Smooth"),
            }),
            primitive(Primitive::SmoothComposite {
                family: path("Smooth"),
            }),
            primitive(Primitive::SmoothIntPoint {
                family: path("Smooth"),
                object: path("Line"),
                point: path("Pt"),
            }),
        ];
        for form in &forms {
            assert!(form.is_algebraic(), "{form:?}");
        }
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
            primitive(Primitive::Compose {
                map_family: path("Morphism"),
            }),
        ];
        for form in &forms {
            assert!(!form.is_algebraic(), "{form:?}");
        }
    }
}
