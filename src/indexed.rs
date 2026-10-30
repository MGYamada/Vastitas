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
}
