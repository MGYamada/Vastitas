# Nominal numerical values and typed GEMM (protocol 8)

`StorageNumerical` connects the common indexed declaration environment to the
actual resource-function compiler and its GEMM schedule. Public protocol 8
exposes local space/basis/map constructors and bilinear GEMM inside resource
functions. Rust sends unresolved profile paths and local names; Lean independently
resolves them in the same namespace as the complete authority/Fn/dispatch checker.
No checked declaration ID, allocation ID or numerical certificate is accepted.

## Public source and build

Inside a resource function, with three live loans of the corresponding shapes:

```vast
space u = linear(profiles::RealSmooth, 2);
space v = linear(profiles::RealSmooth, 3);
space w = linear(profiles::RealSmooth, 2);
basis bu = basis(u);
basis bv = basis(v);
basis bw = basis(w);
map left = view(input_a, bv, bw);
map right = view(input_b, bu, bv);
map destination = view(output, bu, bw);
gemm(left, right, destination, overwrite, NativeFast);
```

The [complete example](../examples/packages/numerical/src/main.vast) calls sibling
`real` and `complex` modules, checks rectangular products and then accumulates
into the same destination. Each module lives in its own directory with `mod.vast`.
The real product is `[[1,2,3],[4,5,6]] * [[7,8],[9,10],[11,12]]`, giving
`[[58,64],[139,154]]`. The complex example from [#91](https://github.com/MGYamada/Vastitas/issues/91)
uses `[[1,i,2],[0,1,-i]] * [[1,0],[2,1],[0,i]]`, giving
`[[1+2i,3i],[2,2]]`. These are general matrices, not rank-one factor pairs.
Both examples check every output cell and then double the result by accumulating
another product. No conjugation is implicit. The initial public operation fixes
alpha to one and beta to zero (`overwrite`) or one (`accumulate`); arbitrary
scalar arguments, including the issue's beta=0.5 example, remain pending.
The inputs are initialized by their individual stores, with no preliminary
zero-fill. The actual bounded initialization checker combines those write
regions before admitting a read or GEMM input. In the shared generated real and
complex GEMM fixture, removing the four redundant fills reduces recorded written
bytes from 768 to 480, preserving six allocations, zero copied bytes and 256 peak
live data bytes. These are operation counters, not elapsed-time measurements or
evidence of C parity; see [initialization coverage](storage-ir.md#layout-and-initialization).

```sh
cargo run --locked -- check --manifest-path examples/packages/numerical/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/numerical/Vastitas.toml \
  --openblas-prefix /path/to/openblas-0.3.34 -o /tmp/numerical-example
/tmp/numerical-example
```

On Linux, add `--native-cc cc` for the host libc used by the pinned OpenBLAS
build. This explicit option selects the numerical consumer compiler/linker and
retains the pinned Lean support libraries; it does not alter ordinary builds.
The prefix must supply the sequential LP64 OpenBLAS 0.3.34 headers and static
archive described in [the adapter contract](numerical-adapter.md).

`check` and kernel emission do not need OpenBLAS. The driver requires an explicit
prefix only when the actual checked entry emits GEMM. An ordinary or storage-only
entry, including one with unused numerical definitions, does not link OpenBLAS.
Unused numerical definitions still undergo all-body checks. Numerical build
options are rejected for `check` and for entries without numerical operations.
Failed checking, prefix resolution or native compilation preserves an existing
output artifact.

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
public resource checker supplies its exact accepted declaration environment
to this compiler, audits each independently resolved profile reference and
checks that all returned product receipts retain that same environment.

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
`tests/numerical_source.rs` tests the actual public source and wire boundaries,
visibility and aliases, wrong bases/objects, scope/capture, old versions and
forged fields. Both OS numerical CI jobs explicitly run its OpenBLAS-dependent
test for generated real/complex execution, runtime assertion failure and output
protection. Normal compiler CI runs the remaining tests without OpenBLAS.

`VastitasOracle.StorageNumerical` proves profile validity, nominal endpoint and
basis equality, actual loan/layout identity, composition with the resource
checker, and the relation to the emitted request. Existing resource and native
audit theorems still apply to that same schedule. These facts do not prove
ideal field/module laws, floating-point accuracy, source operational
correspondence or native refinement.
`ResourceSource.numerical_provenance` and `public_product_origin` connect profile
resolution and the actual returned product receipts to the same accepted public
source and declaration environment.

Dependent numerical function interfaces, dual/conjugate/metric
evidence, finite tensor networks, dynamic dimensions, packing and end-to-end C
performance comparisons remain open in the [Stage 1 gate](stage1-completion.md).
