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
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Coefficient<Name> {
    Literal { value: Literal },
    Loan { loan: Name },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GemmMode {
    Overwrite,
    Accumulate,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum NumericalPolicy {
    NativeFast,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Diagonal {
    pub uniform: bool,
    pub entries: Vec<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
pub enum Action {
    DiagonalAdjoint {
        input: u32,
        output: u32,
        source: Diagonal,
        target: Diagonal,
        conjugate: bool,
        policy: NumericalPolicy,
    },
    DiagonalScale {
        input: u32,
        output: u32,
        diagonal: Diagonal,
        conjugate: bool,
        policy: NumericalPolicy,
    },
    DiagonalPair {
        left: u32,
        right: u32,
        output: u32,
        scratch: u32,
        layout: Layout,
        write_loan: u32,
        read_loan: u32,
        left_child: u32,
        diagonal: Diagonal,
        conjugate_left: bool,
        conjugate_right: bool,
        policy: NumericalPolicy,
    },
    CaptureDependency {
        name: u32,
        source: u32,
        target: u32,
    },
    RequireDependency {
        name: u32,
    },
    ForgetDependency {
        name: u32,
    },
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
    Pack3 {
        source: u32,
        target: u32,
        i: u64,
        k: u64,
        j: u64,
    },
    Regroup3 {
        source: u32,
        target: u32,
        dimensions: Vec<u64>,
        input: source::TensorGrouping,
        output: source::TensorGrouping,
    },
    // Internal resource operation only. Public source additionally needs
    // nominal endpoint/frame/metric validation before selecting this backend.
    Gemm {
        left: u32,
        right: u32,
        output: u32,
        conjugate_left: bool,
        conjugate_right: bool,
        mode: GemmMode,
        policy: NumericalPolicy,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        alpha: Option<Coefficient<u32>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        beta: Option<Coefficient<u32>>,
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

/// Internal affine function component. These IDs and contracts do not supply
/// package visibility, edit authority, public protocol acceptance, or trusted
/// initialization. Lean reconstructs every call against the actual resources.
pub mod functions {
    use super::{Access, Action, Layout, Scalar};
    use serde::{Deserialize, Serialize};

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct OwnedType {
        pub scalar: Scalar,
        pub elements: u64,
        pub initialized: Vec<Layout>,
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
    pub enum Parameter {
        Owned {
            name: u32,
            #[serde(rename = "type")]
            ty: OwnedType,
        },
        Borrowed {
            name: u32,
            scalar: Scalar,
            rows: u64,
            columns: u64,
            access: Access,
            initializes: bool,
        },
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct Result {
        pub name: u32,
        #[serde(rename = "type")]
        pub ty: OwnedType,
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
    pub enum Statement {
        Action {
            action: Action,
        },
        Call {
            callee: u32,
            arguments: Vec<u32>,
            results: Vec<u32>,
        },
        Branch {
            condition: bool,
            yes: Vec<Statement>,
            no: Vec<Statement>,
        },
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct Function {
        pub id: u32,
        pub parameters: Vec<Parameter>,
        pub results: Vec<Result>,
        pub body: Vec<Statement>,
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct Program {
        pub functions: Vec<Function>,
        pub entry: u32,
    }
}

/// Unresolved package resource source. Owners, local symbols and call targets
/// are assigned independently by Lean, alongside the ordinary package checker.
pub mod source {
    use super::{
        Access, Coefficient, GemmMode, Layout, Literal, NumericalPolicy, Scalar,
        functions::OwnedType,
    };
    use crate::ir::{Block, Span, Type, TypePath};
    use serde::{Deserialize, Serialize};

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
    pub enum Parameter {
        Value {
            name: String,
            #[serde(rename = "type")]
            ty: Type,
            span: Span,
        },
        Owned {
            name: String,
            #[serde(rename = "type")]
            ty: OwnedType,
            span: Span,
        },
        Borrowed {
            name: String,
            scalar: Scalar,
            rows: u64,
            columns: u64,
            access: Access,
            initializes: bool,
            span: Span,
        },
        Space {
            name: String,
            implementation: TypePath,
            dimension: u64,
            span: Span,
        },
        Basis {
            name: String,
            space: String,
            span: Span,
        },
        Involution {
            name: String,
            space: String,
            span: Span,
        },
        DualSpace {
            name: String,
            parent: String,
            span: Span,
        },
        ConjugateSpace {
            name: String,
            parent: String,
            involution: String,
            span: Span,
        },
        DerivedBasis {
            name: String,
            parent: String,
            space: String,
            span: Span,
        },
        Metric {
            name: String,
            basis: String,
            involution: String,
            orthonormal: bool,
            span: Span,
        },
        Vector {
            name: String,
            basis: String,
            access: Access,
            initializes: bool,
            span: Span,
        },
        Map {
            name: String,
            source: String,
            target: String,
            access: Access,
            initializes: bool,
            span: Span,
        },
        OwnedMap {
            name: String,
            source: String,
            target: String,
            span: Span,
        },
        OwnedMapTo {
            name: String,
            source: String,
            dimension: u64,
            span: Span,
        },
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
    pub enum NumericalResult {
        OwnedMap { source: String, target: String },
        OwnedMapTo { source: String, dimension: u64 },
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(untagged)]
    pub enum ResultType {
        Owned(OwnedType),
        Numerical(NumericalResult),
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct Result {
        pub name: String,
        #[serde(rename = "type")]
        pub ty: ResultType,
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
    pub enum Action {
        Allocate {
            owner: String,
            scalar: Scalar,
            elements: u64,
        },
        Move {
            source: String,
            target: String,
        },
        Drop {
            owner: String,
        },
        Borrow {
            name: String,
            source: String,
            layout: Layout,
            access: Access,
        },
        Release {
            loan: String,
        },
        Transpose {
            loan: String,
        },
        Fill {
            loan: String,
            value: Literal,
        },
        Store {
            loan: String,
            row: u64,
            column: u64,
            value: Literal,
        },
        Expect {
            loan: String,
            row: u64,
            column: u64,
            value: Literal,
        },
        Copy {
            source: String,
            target: String,
        },
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
    pub enum Gram {
        Identity,
        ScaledIdentity { entry: String },
        Diagonal { entries: Vec<String> },
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
    pub enum Transform {
        Dual {
            source: String,
            target: String,
        },
        Conjugate {
            source: String,
            target: String,
            involution: String,
        },
        Adjoint {
            source_metric: String,
            target_metric: String,
        },
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
    pub enum Evaluation {
        Dual,
        Hermitian { metric: String },
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
    pub enum Numerical {
        Space {
            name: String,
            implementation: TypePath,
            dimension: u64,
        },
        Basis {
            name: String,
            space: String,
        },
        Involution {
            name: String,
            space: String,
        },
        DualSpace {
            name: String,
            parent: String,
        },
        ConjugateSpace {
            name: String,
            parent: String,
            involution: String,
        },
        DerivedBasis {
            name: String,
            parent: String,
            space: String,
        },
        Metric {
            name: String,
            basis: String,
            involution: String,
            gram: Gram,
        },
        AdjointInto {
            input: String,
            output: String,
            source_metric: String,
            target_metric: String,
            policy: NumericalPolicy,
        },
        HermitianDiagonal {
            left: String,
            right: String,
            output: String,
            metric: String,
            scratch: String,
            layout: Layout,
            policy: NumericalPolicy,
        },
        Transform {
            name: String,
            parent: String,
            operation: Transform,
        },
        Vector {
            name: String,
            loan: String,
            basis: String,
        },
        ConjugateVector {
            name: String,
            parent: String,
            basis: String,
            involution: String,
        },
        Evaluate {
            left: String,
            right: String,
            output: String,
            operation: Evaluation,
            mode: GemmMode,
            policy: NumericalPolicy,
            #[serde(default, skip_serializing_if = "Option::is_none")]
            alpha: Option<Coefficient<String>>,
            #[serde(default, skip_serializing_if = "Option::is_none")]
            beta: Option<Coefficient<String>>,
        },
        Map {
            name: String,
            loan: String,
            source: String,
            target: String,
        },
        OwnedMap {
            name: String,
            owner: String,
            layout: Layout,
            source: String,
            target: String,
        },
        PackMap {
            name: String,
            owner: String,
        },
        UnpackMap {
            package: String,
            space: String,
            basis: String,
            owner: String,
        },
        OwnedView {
            name: String,
            loan: String,
            owner: String,
        },
        BorrowOwned {
            name: String,
            owner: String,
            access: Access,
        },
        Gemm {
            left: String,
            right: String,
            output: String,
            mode: GemmMode,
            policy: NumericalPolicy,
            #[serde(default, skip_serializing_if = "Option::is_none")]
            alpha: Option<Coefficient<String>>,
            #[serde(default, skip_serializing_if = "Option::is_none")]
            beta: Option<Coefficient<String>>,
        },
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct TensorGrouping {
        pub order: Vec<u64>,
        pub split: u64,
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
    pub enum Tensor {
        CachedPack {
            name: String,
            source: String,
            target: String,
        },
        CachedContract3 {
            cache: String,
            left: String,
            right: String,
            output: String,
            policy: NumericalPolicy,
        },
        View {
            name: String,
            loan: String,
            axes: Vec<String>,
            grouping: TensorGrouping,
        },
        Pack {
            source: String,
            target: String,
        },
        Contract3 {
            left: String,
            right: String,
            output: String,
            policy: NumericalPolicy,
        },
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(rename_all = "snake_case")]
    pub enum PortRole {
        Input,
        Output,
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct NetworkPort {
        pub occurrence: String,
        pub role: PortRole,
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct Occurrence {
        pub name: String,
        pub value: String,
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct NetworkEdge {
        pub dual: NetworkPort,
        pub primal: NetworkPort,
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct NetworkGraph {
        pub occurrences: Vec<Occurrence>,
        pub edges: Vec<NetworkEdge>,
        pub inputs: Vec<NetworkPort>,
        pub outputs: Vec<NetworkPort>,
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct TreePort {
        pub occurrence: String,
        pub axis: u64,
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct TreeEdge {
        pub name: String,
        pub dual: TreePort,
        pub primal: TreePort,
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct TreeGraph {
        pub occurrences: Vec<Occurrence>,
        pub edges: Vec<TreeEdge>,
        pub boundary: Vec<TreePort>,
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
    pub enum TreeStep {
        Action {
            action: Action,
        },
        View {
            name: String,
            loan: String,
            axes: Vec<String>,
            grouping: TensorGrouping,
        },
        Regroup {
            component: String,
            target: String,
        },
        Rebind {
            component: String,
            view: String,
        },
        Join {
            name: String,
            edge: String,
            left: String,
            right: String,
            output: String,
        },
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
    pub enum Statement {
        Value {
            name: String,
            #[serde(rename = "type")]
            ty: Type,
            body: Block,
            span: Span,
        },
        CallValue {
            callee: String,
            arguments: Vec<String>,
            results: Vec<String>,
            value: String,
            #[serde(rename = "type")]
            ty: Type,
            span: Span,
        },
        BranchValue {
            condition: String,
            yes: Vec<Statement>,
            no: Vec<Statement>,
            span: Span,
        },
        Tree {
            graph: TreeGraph,
            output: String,
            policy: NumericalPolicy,
            plan: Vec<TreeStep>,
            span: Span,
        },
        Tensor {
            operation: Tensor,
            span: Span,
        },
        Network {
            graph: NetworkGraph,
            output: String,
            policy: NumericalPolicy,
            span: Span,
        },
        Action {
            action: Action,
            span: Span,
        },
        Numerical {
            operation: Numerical,
            span: Span,
        },
        Call {
            callee: String,
            arguments: Vec<String>,
            results: Vec<String>,
            span: Span,
        },
        Branch {
            condition: bool,
            yes: Vec<Statement>,
            no: Vec<Statement>,
            span: Span,
        },
    }

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    pub struct Function {
        pub name: String,
        pub parameters: Vec<Parameter>,
        pub results: Vec<Result>,
        pub body: Vec<Statement>,
        pub value_type: Type,
        pub value_body: Block,
        pub span: Span,
    }
}
