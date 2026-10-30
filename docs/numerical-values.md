# Internal nominal numerical values

`StorageNumerical` connects the common indexed declaration environment to the
actual resource-function compiler and its GEMM schedule. It is an internal Lean
component. The public protocol-8 decoder and Rust source grammar do not yet
expose these constructors or typed GEMM. Existing component JSON does not gain
an unchecked declaration table or a numerical certificate field.

## Objects, bases and views

A space constructor requires a concrete `linearDescriptor` implementation from
the independently audited indexed environment. It retains the implementation,
coefficient marker and kind, nominal geometric base, setting, dimension and a
fresh local `Indexed.ObjectRef`. A complex smooth space has complex dimension
`n` and underlying real dimension `2*n`. An affine descriptor, a classification,
a marker or a dimension alone cannot provide linear structure.

Each basis constructor introduces a fresh identity tied to an existing space.
Two bases of the same space are distinct. Two separately constructed spaces of
the same implementation and dimension are also distinct, including across
successive function activations. Numeric values share the compiler's monotone
fresh-name supply with resource bindings. They remain local to their function
or branch and cannot be returned as owners. Typed numerical parameters and
results are still pending.

A map view explicitly interprets a buffer in a source and target basis. Its
logical row count is the target dimension and its column count is the source
dimension. Both spaces must have the same implementation, coefficient and
geometric base. The actual allocation's scalar must implement that coefficient
kind. This construction does not assert that existing floating-point data
satisfy additional algebraic laws.

The view retains the complete actual loan: allocation identity, layout, access
and parent. Every use rechecks that snapshot against the current resource state.
Released, suspended or transposed loans cannot reuse stale views, even when a
square transpose preserves dimensions. Payload writes do not change endpoint
typing; no retained payload-dependent mathematical evidence is introduced.

## Checked product and native schedule

For `A : V → W` and `B : U → V`, the destination must represent `U → W`.
The common middle object **and basis**, and both destination endpoints, must
match exactly. The initial product is bilinear: no conjugation or metric is
inserted. Dual, conjugate, adjoint and general metric operations are separate
remaining work.

`checkProduct` reconstructs the three actual views and validates their complete
value provenance, declaration environment and live resource state. It then
calls the existing `Storage.checkGemm` on those exact loans. Readability,
initialization, output exclusivity and physical input/output separation remain
mandatory. `overwrite` does not require initialized output; `accumulate` does.

`StorageFunctions` runs that check during each actual call, separately from
all-body signature probes. A `NumericalReceipt` records the returned product
certificate, exact emitted GEMM, and exact resource transition. Generation
rechecks the function program and then the existing storage/native plan. The
public resource checker now supplies its exact accepted declaration environment
to this compiler; the pending source syntax must independently resolve profile
paths through that same namespace.

The nominal values erase before native execution. The closed real and complex
fixtures generate three destination/input allocations, no tensor copies or
extra numerical metadata allocations, and preserve caller-selected output
storage. These counters and successful BLAS calls are not evidence that **Fast
like C** has been achieved; equivalent-C measurements remain a completion gate.

## Evidence and remaining boundaries

`VastitasStorageTest.NumericalRegression` tests actual declaration checking,
real/complex products, distinct nominal objects/bases, fresh call identities,
both branches, unused bodies, scalar/base mismatch, scope escape, stale loans
and forged metadata. `scripts/check_gemm_checked.py` also executes generated
rectangular real and complex fixtures with exact expected bit patterns and
allocation/copy counters, using pinned OpenBLAS 0.3.34.

`VastitasOracle.StorageNumerical` proves profile validity, nominal endpoint and
basis equality, actual loan/layout identity, composition with the resource
checker, and the relation to the emitted request. Existing resource and native
audit theorems still apply to that same schedule. These facts do not prove
ideal field/module laws, floating-point accuracy, source operational
correspondence or native refinement.

Public syntax, dependent numerical function interfaces, dual/conjugate/metric
evidence, finite tensor networks, dynamic dimensions, packing and end-to-end C
performance comparisons remain open in the [Stage 1 gate](stage1-completion.md).
