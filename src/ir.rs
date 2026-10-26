//! Versioned, deliberately untrusted frontend IR. The Lean backend checks it again.

use serde::{Deserialize, Serialize};

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
    pub file: String,
    pub functions: Vec<Function>,
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
    Named { name: String },
    Point { target: Index, source: Index },
    Morphism { source: Index, target: Index },
    Pointed { setting: String, base: String },
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
