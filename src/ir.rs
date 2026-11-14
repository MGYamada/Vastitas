//! Versioned, deliberately untrusted frontend IR. The Lean backend checks it again.

use serde::{Deserialize, Serialize};

// The wire protocols of a request. Flat input writes 2, or 4 when it holds
// abstract declarations (`frontend::parse_sources`). A package request writes
// the first of 9 down to 3 that the declarations of the program, or the
// `geometry_compat` export of a manifest, select (`packages::request_protocol`);
// 9 also carries the algebraic forms.
pub const PROTOCOL_VERSION: u32 = 2;
pub(crate) const PACKAGE_PROTOCOL: u32 = 3;
pub const ABSTRACT_PROTOCOL_VERSION: u32 = 4;
pub(crate) const EDIT_PROTOCOL: u32 = 5;
pub(crate) const AUTHORITY_PROTOCOL: u32 = 6;
pub(crate) const INDEXED_PROTOCOL: u32 = 7;
pub(crate) const RESOURCE_PROTOCOL: u32 = 8;
pub(crate) const NAMED_RECIPIENT_PROTOCOL: u32 = 9;
/// The protocols that the driver writes, in the order of `--version`.
pub(crate) const PUBLIC_PROTOCOLS: [u32; 8] = [
    PROTOCOL_VERSION,
    PACKAGE_PROTOCOL,
    ABSTRACT_PROTOCOL_VERSION,
    EDIT_PROTOCOL,
    AUTHORITY_PROTOCOL,
    INDEXED_PROTOCOL,
    RESOURCE_PROTOCOL,
    NAMED_RECIPIENT_PROTOCOL,
];

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub column: usize,
}

impl Span {
    pub fn through(self, end: Span) -> Self {
        Self {
            end: end.end,
            ..self
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Diagnostic {
    pub code: String,
    pub message: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Module {
    pub version: u32,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub input: Option<String>,
    pub file: String,
    pub functions: Vec<Function>,
    pub generics: Vec<Generic>,
    pub methods: Vec<Method>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub abstract_types: Vec<AbstractType>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub subtypes: Vec<Subtype>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub abstract_methods: Vec<AbstractMethod>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypePath {
    pub path: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AbstractType {
    pub name: String,
    pub parents: Vec<TypePath>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Subtype {
    pub scalar: String,
    pub target: TypePath,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Generic {
    pub name: String,
    pub params: Vec<GenericParam>,
    pub domain: Vec<Vec<Type>>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GenericParam {
    pub name: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Method {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Type,
    pub requires: Vec<String>,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AbstractMethod {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Type,
    pub requires: Vec<String>,
    pub domain: Vec<Vec<TypePath>>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Function {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Type,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Param {
    pub name: String,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Type {
    IndexedObject {
        domain: Box<TypePath>,
        marker: Box<TypePath>,
    },
    IndexedApply {
        family: Box<TypePath>,
        arguments: Vec<crate::indexed::Argument>,
    },
    Pair {
        element: String,
    },
    Function {
        params: Vec<Type>,
        return_type: Box<Type>,
    },
    Named {
        name: String,
    },
    Point {
        target: Index,
        source: Index,
    },
    Morphism {
        source: Index,
        target: Index,
    },
    Pointed {
        setting: String,
        base: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Index {
    Name { name: String },
    Base { ring: String },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub result: Box<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Expr {
    #[serde(flatten)]
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ExprKind {
    IndexedPack {
        package: Box<Type>,
        witness: Box<Expr>,
        fields: Vec<Expr>,
    },
    Lambda {
        params: Vec<Param>,
        return_type: Type,
        body: Block,
    },
    Invoke {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
    Integer {
        value: String,
    },
    Boolean {
        value: bool,
    },
    Unit,
    Variable {
        name: String,
    },
    Call {
        callee: String,
        args: Vec<Expr>,
    },
    Unary {
        op: String,
        operand: Box<Expr>,
    },
    Binary {
        op: String,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    If {
        condition: Box<Expr>,
        then_branch: Block,
        else_branch: Block,
    },
    Block {
        body: Block,
    },
    Pack {
        scheme: Box<Expr>,
        point: Box<Expr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Statement {
    #[serde(flatten)]
    pub kind: StatementKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum StatementKind {
    UnpackFields {
        value: Expr,
        witness: String,
        fields: Vec<String>,
    },
    Let {
        name: String,
        annotation: Option<Type>,
        value: Expr,
    },
    Unpack {
        value: Expr,
        scheme: String,
        point: String,
    },
}
