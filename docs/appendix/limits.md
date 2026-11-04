# Appendix D: Compiler limits

The compiler rejects an input that exceeds a limit, usually with `E_LIMIT`. It
never accepts part of an input or skips an unused body to stay within a budget.
These are defensive implementation limits, not mathematical restrictions.

## Checker limits

The authoritative values are in
[`lean-kernel/compiler-limits.json`](https://github.com/MGYamada/Vastitas/blob/main/lean-kernel/compiler-limits.json).
The Lean kernel and the Rust driver both take their values from this file when
they are built. Distinct budgets stay distinct even when their values coincide.

| Key | Value | What it bounds | Specified in |
| --- | --- | --- | --- |
| `parseNesting` | 64 | Combined type and expression recursive parsing in the frontend | [Core language](../stage0.md#compiler-behavior-and-limits) |
| `astDepth` | 128 | Syntax-tree depth, including left-associated operator chains | [Core language](../stage0.md#compiler-behavior-and-limits) |
| `moduleNesting` | 64 | Logical module nesting | [Modules and paths](../packages.md#modules-and-paths) |
| `packageNesting` | 64 | Dependency nesting | [Modules and paths](../packages.md#modules-and-paths) |
| `typeNesting` | 64 | Nesting of a declared type | Kernel source |
| `sourceNesting` | 512 | Recursive decoding steps in the protocol decoder | [Core language](../stage0.md#compiler-behavior-and-limits) |
| `namespaceNesting` | 1024 | Recursion of the namespace checker through a function body | Kernel source |
| `captureDiagnostic` | 8192 | Traversal used to locate a capture violation for its diagnostic | Kernel source |
| `bodyChecking` | 4096 | Fuel for checking one function body, or one function instance | [Core language](../stage0.md#compiler-behavior-and-limits) · [Specialization](../stage1b.md#checking-and-specialization) |
| `elaborationWork` | 1,000,000 | Aggregate elaboration units per pass | [Specialization](../stage1b.md#checking-and-specialization) |
| `resourceWork` | 32,000,000 | Weighted units across all resource probes and the executable entry | [Resource checking work](../storage/checked-storage.md#storage-functions--resource-checking-work) |
| `generatedLets` | 4096 | Generated Lean `let` bindings per function | [Core language](../stage0.md#compiler-behavior-and-limits) |
| `specializations` | 4096 | Higher-order instances per pass | [Specialization](../stage1b.md#checking-and-specialization) |
| `dispatchKeys` | 4096 | Argument tuples enumerated for one generic | [Dispatch](../stage1a.md#selection-and-whole-program-checking) |
| `dispatchArity` | 6 | Generic arity; the seventh argument would exceed 4,096 tuples | [Dispatch](../stage1a.md#selection-and-whole-program-checking) |
| `dispatchWork` | 16,000,000 | Dispatch-table work for one generic family, charged before the work runs | [Wire protocols](../protocol.md) |
| `nominalTypes` | 64 | Nominal types, including `Nat`, `Int`, `Bool`, `Unit`, `Number` and `Any` | [Abstract selectors](../stage1a.md#abstract-types) |
| `namespaceResolution` | 4096 | Member work for one path resolution | [Modules and paths](../packages.md#modules-and-paths) |
| `namespaceImportWork` | 1,000,000 | Member visits across all import declarations | [Modules and paths](../packages.md#modules-and-paths) |
| `namespaceProgramWork` | 4,000,000 | Wire input price plus namespace queries in the body passes | [Modules and paths](../packages.md#modules-and-paths) |
| `dependencyGraph` | 4096 | Units for traversing the package dependency graph | Kernel source |
| `assemblyEvents` | 4096 | Events in an edit assembly | [Wire extension](../packages.md#wire-extension) |
| `authorityTraceWork` | 200,000,000 | Audit work shared by one edit-assembly trace | [Wire extension](../packages.md#wire-extension) |
| `contributionMethods` | 4096 | Methods in one contribution | [Wire extension](../packages.md#wire-extension) |

### Exact affine algebra (Stage 2)

These budgets belong to the exact QQ polynomial core of
[presented affine geometry](../affine-geometry.md) (historical Stage 2), reached
through protocol 9. Source polynomials are bounded before they are expanded.
Every check-time substitution — structure maps, pullbacks, base chains, base
isomorphisms and evidence composites — runs within `algebraWork` and
`algebraTerms`, in the checker and the audit alike.

| Key | Value | What it bounds |
| --- | --- | --- |
| `algebraGenerators` | 16 | Generators of one presented algebra |
| `algebraRelations` | 32 | Relations of one presented algebra |
| `algebraTerms` | 512 | Terms of every produced polynomial, including intermediate products |
| `algebraBasis` | 64 | Elements of a stored or computed basis |
| `algebraWork` | 8,000,000 | Work of one budgeted run: basis computation and verification, or one substitution check |
| `algebraDegree` | 16 | Degree and exponents of a source polynomial |
| `algebraCoefficientDigits` | 64 | Digits of a source literal |
| `algebraChain` | 16 | Length of a declared base chain |
| `algebraNesting` | 64 | Nesting of a polynomial expression on the wire |

"Kernel source" means the limit is enforced in
[`lean-kernel/VastitasKernel`](https://github.com/MGYamada/Vastitas/tree/main/lean-kernel/VastitasKernel)
but not yet described elsewhere in this book.

## Input limits

The driver enforces these before checking. See the
[CLI reference](../guide/cli.md).

| Limit | Value |
| --- | --- |
| One input file | 16 MiB |
| All inputs of one compilation | 64 MiB |
| File loads per compilation | 8,192 |
| Logical modules in a package closure, including inline modules and repeated file uses | 4,096 |

A reused source file consumes the byte budget again.

## Other documented bounds

| Bound | Value | Specified in |
| --- | --- | --- |
| Conditions in one standalone `if`/`else if` chain | 62 | [Core language](../stage0.md#compiler-behavior-and-limits) |
| Generated Lean `maxRecDepth` / `maxHeartbeats` | 32768 / 2000000 | [Core language](../stage0.md#compiler-behavior-and-limits) |
| Function-specialization worklist requests per pass | 2,000,000 | [Specialization](../stage1b.md#checking-and-specialization) |
| Storage plan nodes and traversal depth | 4096 each | [Checked storage](../storage/checked-storage.md#storage-ir) |
| Resource definitions, parameters/results each, initialized regions per owned type, source statements | 4096, 64, 64, 4096 | [Resource functions](../storage/checked-storage.md#storage-functions--all-body-checking-and-exact-expansion) |
| Events in one contraction-tree plan | 1024 | [Contraction trees](../linalg/networks-and-packing.md#contraction-trees) |
| Explicit diagonal metric entries | 4096 | [Declared Hermitian forms](../linalg/transforms-and-metrics.md#declared-hermitian-forms) |
| Notes on one resource diagnostic | 32 | [Resource diagnostics](../storage/resource-programs.md#resource-diagnostics) |

Runtime-shape programs have their own execution limits; see
[Execution costs and limits](../storage/resource-programs.md#execution-costs-and-limits).

Work budgets count admission units, not elapsed time, allocation bytes or
native instructions. Total compiler wall time has no separate bound.
