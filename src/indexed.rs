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
}

impl DeclarationBody {
    /// Stage 2 algebraic forms. They exist only in protocol 9.
    pub fn is_algebraic(&self) -> bool {
        match self {
            DeclarationBody::Affine { .. } | DeclarationBody::Morphism { .. } => true,
            DeclarationBody::Primitive { binding } => matches!(
                binding,
                Primitive::RelativeCompose { .. }
                    | Primitive::RelativeView { .. }
                    | Primitive::RelativeEqual { .. }
                    | Primitive::RelativeCoefficient { .. }
                    | Primitive::RelativeIntPoint { .. }
            ),
            DeclarationBody::Implementation { representation, .. } => {
                matches!(representation, Representation::PresentedAffine { .. })
            }
            DeclarationBody::Family {
                constraints,
                representation,
                ..
            } => {
                *representation == FamilyRepresentation::Relative
                    || constraints
                        .iter()
                        .any(|c| matches!(c, Constraint::Structural { .. }))
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
}
