//! Versioned, deliberately untrusted frontend IR. The Lean backend checks it again.

use serde::{Deserialize, Serialize};

/// The wire schema epoch (#533): the one protocol that the driver writes and
/// the kernel accepts, and the one that `--version` reports. The kernel holds
/// the same number in `currentProtocol` (`lean-kernel/VastitasKernel/
/// Protocol.lean`); `build.rs` reads it there, and the build fails when the two
/// differ.
pub const PROTOCOL: u32 = 10;

const _: () = assert!(
    PROTOCOL == crate::driver::KERNEL_PROTOCOL,
    "src/ir.rs PROTOCOL differs from currentProtocol of lean-kernel/VastitasKernel/Protocol.lean"
);

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
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

/// A flat compilation unit: one file, with its `--lib` inputs. The driver
/// sends it as the one package of `packages::flat_request`; the wire has no
/// flat envelope.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Module {
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
    /// The `show!` of the top-level `let` statements of `fn main` (#836).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub observations: Vec<Observation>,
}

/// One `show!(expr)` of the entry point (#836): the `statement`-th top-level
/// statement of the body of `fn main` is `let name = show!(expr);`, which the
/// request sends as `let name = expr;`. The program writes `label = value`
/// when it binds the value. The label is the source text of `expr` with each
/// run of whitespace replaced by one space; it is presentation only.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Observation {
    pub statement: usize,
    pub label: String,
    /// The place of `show!(expr)`, for the frontend's own diagnostics. Not
    /// part of the request.
    #[serde(skip)]
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
