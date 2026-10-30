//! Explicit, untrusted resource-plan input. The Lean resource checker derives
//! allocation identities, ownership, initialization and alias facts from these
//! transitions. No serialized state, certificate, or initialized flag is accepted.

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Scalar {
    F64,
    ComplexF64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Layout {
    pub offset: u64,
    pub rows: u64,
    pub columns: u64,
    pub leading: u64,
    pub transposed: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Access {
    Read,
    Write,
    ReadWrite,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Source {
    Owner { name: u32 },
    Loan { name: u32 },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Literal {
    F64 { bits: u64 },
    ComplexF64 { real: u64, imaginary: u64 },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
pub enum Action {
    Allocate {
        owner: u32,
        scalar: Scalar,
        elements: u64,
    },
    Move {
        source: u32,
        target: u32,
    },
    Drop {
        owner: u32,
    },
    Borrow {
        name: u32,
        source: Source,
        layout: Layout,
        access: Access,
    },
    Release {
        loan: u32,
    },
    Transpose {
        loan: u32,
    },
    Fill {
        loan: u32,
        value: Literal,
    },
    Store {
        loan: u32,
        row: u64,
        column: u64,
        value: Literal,
    },
    Expect {
        loan: u32,
        row: u64,
        column: u64,
        value: Literal,
    },
    Copy {
        source: u32,
        target: u32,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Statement {
    Action {
        action: Action,
    },
    Branch {
        condition: bool,
        yes: Vec<Statement>,
        no: Vec<Statement>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Plan {
    pub statements: Vec<Statement>,
}
