# Appendix D: Compiler limits

The compiler rejects an input that exceeds a limit, usually with `E_LIMIT`. It
never accepts part of an input or skips an unused body to stay within a budget.
These are defensive implementation limits, not mathematical restrictions.
The compilation of reverse passes into Core is the one exception: its budgets
bound how much of a checked program it compiles, and it rejects nothing. A
function whose compiled Core would exceed `generatedLets` keeps every one of
its reverse sites as a call of the
[runtime reverse pass](glossary.md#runtime-reverse-pass). A site keeps it too
when its declarations would exceed the 4096 declaration ids of a Core module.
The reading of a site's maps charges at most `reverseLeaves` maps:

- a `let`-bound map whose recorded maps exceed the remaining budget is one
  [opaque step](glossary.md#opaque-step);
- below as many levels as there are `let`s in scope, plus 64, the rest of the
  map is one opaque step, and a `let` nested deeper than its own reading
  reaches is one opaque step wherever it is read;
- a map operand whose own `compose` calls exceed the budget is one opaque step
  as a whole, so none of its maps is compiled.

## Checker limits

The authoritative values are in
[`lean-kernel/compiler-limits.json`](https://github.com/MGYamada/Vastitas/blob/main/lean-kernel/compiler-limits.json).
The Lean kernel and the Rust driver both take their values from this file when
they are built. Distinct budgets stay distinct even when their values coincide.

| Key | Value | What it bounds | Specified in |
| --- | --- | --- | --- |
| `parseNesting` | 64 | Combined type and expression recursive parsing in the frontend | [Budgets](#parser-and-checker-budgets) |
| `astDepth` | 128 | Syntax-tree depth, including left-associated operator chains | [Budgets](#parser-and-checker-budgets) |
| `moduleNesting` | 64 | Logical module nesting | [Modules](../language/modules.md) |
| `packageNesting` | 64 | Dependency nesting | [Package graph](../packages.md#the-package-graph) |
| `typeNesting` | 64 | Nesting of a declared type | Kernel source |
| `sourceNesting` | 512 | Recursive decoding steps in the protocol decoder | [Budgets](#parser-and-checker-budgets) |
| `namespaceNesting` | 1024 | Recursion of the namespace checker through a function body | Kernel source |
| `captureDiagnostic` | 8192 | Traversal used to locate a capture violation for its diagnostic | Kernel source |
| `bodyChecking` | 4096 | Depth of one checking path through a function body or function instance | [Budgets](#parser-and-checker-budgets) · [Function specialization](../internals/checking-pipeline.md#function-specialization) |
| `elaborationWork` | 1,000,000 | Aggregate elaboration units per pass | [Function specialization](../internals/checking-pipeline.md#function-specialization) |
| `resourceWork` | 32,000,000 | Weighted units across all resource probes and the executable entry | [Resource checking work](../storage/checked-storage.md#storage-functions--resource-checking-work) |
| `generatedLets` | 4096 | Generated Lean `let` bindings per function. A function whose compiled reverse Core would exceed it keeps its reverse passes as calls of the [runtime reverse pass](glossary.md#runtime-reverse-pass) | [Budgets](#parser-and-checker-budgets) |
| `reverseLeaves` | 256 | Maps of one reverse pass that the compilation into Core reads through `let`s and `compose`; a map beyond it is one [opaque step](glossary.md#opaque-step), pulled back by the runtime reverse pass | [Kernel source](https://github.com/MGYamada/Vastitas/blob/main/lean-kernel/VastitasKernel/IndexedReverse.lean) |
| `specializations` | 4096 | Specialized instances per pass: every lambda instance and every higher-order instance | [Specialization](../stage1b.md#specialization) · [Function specialization](../internals/checking-pipeline.md#function-specialization) |
| `dispatchKeys` | 4096 | Keys enumerated for one generic | [Generic declarations](../stage1a.md#generic-declarations) |
| `dispatchArity` | 6 | Parameters of a generic; a seventh parameter would exceed 4096 keys | [Generic declarations](../stage1a.md#generic-declarations) |
| `dispatchWork` | 16,000,000 | Dispatch-table work for one generic family, charged before the work runs | [Selection](../stage1a.md#selection) · [Wire protocols](../protocol.md) |
| `nominalTypes` | 64 | Nominal types, including `Nat`, `Int`, `Bool`, `Unit`, `Number` and `Any` | [Abstract selectors](../stage1a.md#abstract-types) |
| `namespaceResolution` | 4096 | Member work for one path resolution | [Protocol 3](../protocol.md#protocol-3-package-namespaces) |
| `namespaceImportWork` | 1,000,000 | Member visits across all import declarations | [Protocol 3](../protocol.md#protocol-3-package-namespaces) |
| `namespaceProgramWork` | 4,000,000 | Wire input price plus namespace queries in the body passes | [Protocol 3](../protocol.md#protocol-3-package-namespaces) |
| `dependencyGraph` | 4096 | Units for traversing the package dependency graph | Kernel source |
| `assemblyEvents` | 4096 | Events in an edit assembly | [Assemblies](../language/edit-authority.md#assemblies) · [Protocol 5](../protocol.md#protocol-5-scoped-edits-and-assembly) |
| `authorityTraceWork` | 200,000,000 | Audit work shared by one edit-assembly trace | [Protocol 5](../protocol.md#protocol-5-scoped-edits-and-assembly) |
| `contributionMethods` | 4096 | Methods in all contributions of the package graph | [Protocol 5](../protocol.md#protocol-5-scoped-edits-and-assembly) |

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
| `algebraNesting` | 64 | Levels of a [polynomial expression](../language/smooth-declarations.md#polynomial-expressions): one for every literal, coordinate, sum, product, negation and power on a path. It also bounds the nesting of parentheses |

### Smooth objects and maps

[Smooth affine declarations](../language/smooth-declarations.md) reuse the
exact affine algebra budgets above. The kernel elaborates each image of a
smooth map within one `algebraWork` run. An input beyond a bound is an error
(`E_LIMIT`).

| Key | Value | What it bounds |
| --- | --- | --- |
| `algebraGenerators` | 16 | Coordinates of a smooth affine object, so the dimension of every smooth map, tangent or cotangent fiber, tape and Gram matrix |
| `algebraCoefficientDigits` | 64 | Digits of an `Affine(n)` dimension, and of a literal in an image or a Gram entry |
| `algebraDegree` | 16 | Degree and exponents of an image or a Gram entry |
| `algebraNesting` | 64 | Levels of an image or a Gram entry |
| `algebraTerms` | 512 | Terms of each expanded image or Gram entry |
| `algebraWork` | 8,000,000 | Work of elaborating one image, or all Gram entries of one metric |

These bounds apply when a program is checked. In a compiled program, `same`
and `composite` expand a composite map at run time without a budget, and the
reverse pass has no work bound. The length of a chain of `compose` nodes has
no bound either, nor have the exponents and the number of terms of a
composite. The runtime runs all three in loops, so they cost time and memory,
not native stack ([#630](https://github.com/MGYamada/Vastitas/issues/630));
see [Stack-safe runtime code](../verification.md#stack-safe-runtime-code).

### Smooth metrics

The kernel evaluates all Gram entries of one metric within one `algebraWork`
run. It then bounds the size of each entry, and then the size of the whole
matrix. A larger entry or matrix is an error (`E_LIMIT`). The kernel checks
both bounds when it elaborates the metric, before it computes a certificate
for any [metric evidence](../language/smooth-declarations.md#metric-evidence).
See [metric forms](../protocol.md#protocol-9-metric-forms).

| Key | Value | What it bounds |
| --- | --- | --- |
| `metricEntryBits` | 512 | Bits of the numerator and of the denominator of one elaborated Gram entry |
| `metricMatrixBits` | 16,384 | Bits of the [matrix bound](glossary.md#matrix-bound) ‖A₁‖ ⋯ ‖Aₙ‖ · max Dᵢ of one Gram matrix |

In the matrix bound, Dᵢ is the least common denominator of row i of the Gram
matrix, and Aᵢ is row i times Dᵢ, a row of integers. ‖Aᵢ‖ is its Euclidean
norm, and a zero row counts as 1. [Metrics](../language/smooth-declarations.md#metrics)
states the rule.

The entry bound does not limit the work of the inverse, of the `L D Lᵀ`
factorization or of their checks. The entries of the inverse grow with the
least common denominators of the rows: a 16 × 16 matrix whose entries have
pairwise distinct 400-bit denominators has an inverse with entries of about
100,000 bits. The matrix bound limits that work. By Hadamard's inequality,
the numerator and the denominator of every entry of the inverse, and of every
entry of L, D and L⁻¹, have at most `metricMatrixBits` bits. With at most
`algebraGenerators` coordinates, this bounds the work of a certificate and of
its check. Every Gram matrix with integer entries and every diagonal Gram
matrix within the entry bound is within the matrix bound.

"Kernel source" means the limit is enforced in
[`lean-kernel/VastitasKernel`](https://github.com/MGYamada/Vastitas/tree/main/lean-kernel/VastitasKernel)
but not yet described elsewhere in this book.

## Parser and checker budgets

The frontend parses types and expressions recursively, to a combined depth of
64 levels (`parseNesting`). A syntax tree has a depth of at most 128 nodes
(`astDepth`), including a chain of left-associated operators. A standalone
`if`/`else if` chain uses one nesting level for each condition, and each
condition and each branch result uses further levels. A chain whose
conditions are single comparisons has at most 62 conditions. The protocol decoder takes at most 512
recursive decoding steps (`sourceNesting`).

The kernel checks the body of each function with 4096 units of fuel
(`bodyChecking`). The fuel bounds the depth of one path through the body, not a
total count. Each nested expression, each later statement of a block and each
argument of a call of a defined function uses one unit along its own path. The
kernel checks sibling subexpressions with the same remaining fuel: both
operands, both branches, the fields of `pack` and the arguments of generic and
primitive calls.

`check` and `build` also allow at most 4096 generated Lean `let` bindings in
one function (`generatedLets`), counted over all branches and nested
expressions. A source `let` contributes one binding and an `unpack` three.
Exceeding a budget of this section is an error (`E_LIMIT`). The generated Lean
sets `maxRecDepth` to 32768 and `maxHeartbeats` to 2000000. Tests cover these
limits. They do not protect a build against failures of its environment.

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
| Conditions in one standalone `if`/`else if` chain whose conditions are single comparisons | 62 | [Budgets](#parser-and-checker-budgets) |
| Generated Lean `maxRecDepth` / `maxHeartbeats` | 32768 / 2000000 | [Budgets](#parser-and-checker-budgets) |
| Function-specialization worklist requests per pass | 2,000,001, or a structural bound when that is smaller | [Function specialization](../internals/checking-pipeline.md#function-specialization) |
| Storage plan nodes and traversal depth | 4096 each | [Checked storage](../storage/checked-storage.md#storage-ir) |
| Resource definitions, parameters/results each, initialized regions per owned type, source statements | 4096, 64, 64, 4096 | [Resource functions](../storage/checked-storage.md#storage-functions--all-body-checking-and-exact-expansion) |
| Events in one contraction-tree plan | 1024 | [Contraction trees](../linalg/networks-and-packing.md#contraction-trees) |
| Explicit diagonal metric entries | 4096 | [Declared Hermitian forms](../linalg/transforms-and-metrics.md#metrics) |
| Notes on one resource diagnostic | 32 | [Diagnostics](../storage/resource-programs.md#diagnostics) |

Runtime-shape programs have their own execution limits; see
[Execution costs and limits](../internals/resource-checking.md#execution-costs-and-limits).

Work budgets count admission units, not elapsed time, allocation bytes or
native instructions. Total compiler wall time has no separate bound.
