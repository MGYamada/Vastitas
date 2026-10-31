# Explicit diagonal metrics (protocol 8)

Resource functions can materialize metric adjoints into caller destinations and
evaluate diagonal Hermitian forms using caller scratch. These operations use the
actual declared `Metric` and its exact nominal basis/involution. A same-shaped
buffer, a raw coefficient table, or matching dimensions does not supply a metric.
The existing allocation-free, orthonormal `adjoint` view remains unchanged.

```vast
metric hv = diagonal(bv, sigma, [2, -4]);
metric hw = diagonal(bw, sigma, [3, 5, -2]);
adjoint_into(input, output, hv, hw, NativeFast);

// xc explicitly interprets a conjugate-space vector, as in vector evaluation.
hermitian_diagonal(xc, y, scalar_out, hv,
    scratch(scratch_owner, layout(8, 2, 1, 3, false)), overwrite, NativeFast);
```

`input` is a readable map from `bv` to `bw`; `output` is a writable map with
those exact bases reversed. Both forms must select the same involution.
The output has ordinary coordinates; its declared view cannot already carry a
conjugation. For an input coordinate matrix A, the intended ideal formula is
`A†[i,j] = star(A[j,i]) * gw[j] / gv[i]`. An already conjugated input uses the
opposite native conjugation flag. The materialized output is distinct from a
transpose, and has no hidden inverse, Gram matrix, temporary matrix or BLAS call.

The pairing takes a readable right vector in `hv`'s exact basis and an explicit
left vector in the corresponding conjugate basis. Its intended coordinate
formula is `sum(xc[i] * gv[i] * y[i])`; constructing `xc` from ordinary x by
explicit conjugation gives the usual Hermitian formula. The output is one
writable coefficient scalar of the same real/complex type. This initial
operation supports default-alpha overwrite only; it does not read old output.

## Realization and resource contract

The existing forms are identity, scaled identity with an exact `Int`, or an
explicit list of exact `Int` entries. Positive-dimensional realization requires
every entry to be nonzero with absolute value at most 2^53, so it is exactly
representable in binary64. Encoding and decoding use integer/bit arithmetic;
there is no tolerance test or host-float rounding when admitting the metric.
Explicit diagonals retain the existing 4,096-entry bound. Negative entries are
allowed: nondegeneracy does not assert positivity. Empty spaces follow actual
`Metric.nondegenerate`: even a zero or oversized scaled identity is vacuously
valid, and its unused native coefficients canonicalize to identity.

`Metric<bv,sigma>` dependent parameters remain general declared-form contracts.
The concrete call rechecks the native realization bound. Synthetic body probes
are separate from actual arguments and do not prove that every possible metric
argument is realizable. Existing static dimensions and source nominal identities
are preserved; no dynamic floating Core values or shape interface is added.

The scratch argument is a caller-owned allocation without outstanding loans.
It cannot be an opaque `OwnedMapTo` package or a borrowed handle. The checker
reconstructs and accepts this exact sequence:

1. Borrow scratch for writing; read and weight the right vector into it.
2. Return that write loan; create a fresh initialized read loan of scratch.
3. Create a read child of the left vector with the required row orientation.
4. Execute the existing overwrite GEMM into the scalar output.
5. Return both children, restoring caller loans and allocation owners.

The public compiler also replays the sequence independently and records its
equality with the single compound resource action. There is no access upgrade
or invented source read loan. Scratch and output are marked written once each,
invalidating cached dependencies on either allocation. Adjoint writes invalidate
dependencies on its destination. Both branch arms, unused bodies, original
caller arguments and the final schedule are independently checked.

## Native costs and failure boundary

`adjoint_into` executes one O(mn) pass and writes mn scalar-width bytes.
`hermitian_diagonal` executes one O(n) weighting pass and one existing GEMM,
writing (n+1) scalar-width bytes, or just the zero scalar when n=0. Both reuse
caller storage and add no data allocation or data copy. They perform explicit
`NativeFast` multiplication/division, with normal floating rounding, overflow
and nonfinite propagation; exact metric coefficients do not imply exact results.

Every returned preflight error preserves destination data, scratch, write
counters and the GEMM report. The compound pairing validates the backend,
all actual layouts/scalars, source/output and scratch separation, all diagonal
entries, bounds and total write-counter overflow before its first write. After
preflight it performs no fallible adapter operation between weighting and GEMM.
This is a synchronous native implementation contract, not a theorem about
backend crashes or arbitrary foreign pointers.

Generated coefficient payloads are immutable Lean `ByteArray` constants borrowed
for the duration of each FFI call. FFI retains no coefficient pointer afterward.
Their payload is 8(n+m) bytes for two explicit adjoint diagonals and 8n bytes for
pairing; identity/scaled identity uses eight bytes per form, plus Lean object
and container overhead. A static hex string holds twice the payload bytes; a
reserved linear decoder constructs each table once, with a temporary UTF-8 copy
of that hex text. Generated C does not retain every array-literal prefix. These
are metadata, not arena data allocations, and are
not counted by arena data counters. Foreign C callers must provide readable
immutable tables of the declared byte length for the complete synchronous call;
concurrent mutation or forged pointer extents are outside the trusted ABI.
The pinned Lean-generated C fixture initializes the two distinct closed tables
once on first use and reuses them across repeated operations; the checked-native
test audits this placement. Initial construction and retained metadata still
cost memory/time, and this inspection is not a general native-refinement proof.

Standalone adjoint uses only the optional storage native runtime, without
OpenBLAS. Pairing links the pinned sequential LP64 OpenBLAS 0.3.34 adapter.
The [prepared adapter/C experiment](../experiments/diagonal_metrics/README.md)
reports actual costs and performance gaps. It excludes public-source/FFI and
lifecycle costs and does not close the [Fast like C gate](storage-ownership.md#713-performance-evidence-and-acceptance).

## Checking, proofs and examples

Rust and Lean strictly decode `adjoint_into` and `hermitian_diagonal` numerical
operations in protocol 8. Operands are unresolved names and explicit scratch
layout, never supplied Gram bytes, allocation identities or acceptance receipts.
Protocols 2–7 and unknown fields reject these payloads. `StorageMetric` obtains
metrics from the actual accepted value environment, retains exact realization,
resource transition and replay evidence; `StorageFunctions` retains the precise
emitted action, and `ResourceSource` audits every executable receipt's original
declaration environment. `StorageCodegen` reconstructs and checks the native
instruction against the original schedule before generating code.

`VastitasOracle.StorageMetric` extracts those actual-checker guarantees.
`StorageMetricLaws` interprets the exact certificate metric fields over a lawful
characteristic-zero commutative field with an explicit additive/multiplicative
involution. Nonzero coordinate weights follow from the actual selected metric
validity, not an extra arbitrary nondegeneracy assumption. It proves pairing
linearity/semilinearity and Hermitian symmetry, adjoint additivity/star scaling,
the defining adjoint pairing equation and finite composition contravariance.
Composition requires equality of the full intermediate `Metric`; equal shape
does not suffice. These laws concern ideal coordinate formulas. They do not
prove that an unrelated composite buffer holds a matrix product, source/native
refinement, numerical error bounds, or floating-point field identities.

```sh
cargo run --locked -- check --manifest-path examples/packages/diagonal-metrics/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/diagonal-metrics/Vastitas.toml \
  --openblas-prefix /path/to/openblas-0.3.34 -o /tmp/diagonal-metrics
/tmp/diagonal-metrics
```

The example checks real/complex padded rectangular adjoints and repeated
scratch-backed pairings, then prints `42`. `MetricRegression`, source/wire tests,
standalone native sanitizers and exact checked-schedule execution cover stale
dependencies, incorrect metric/basis/loan provenance, malformed coefficients,
zero dimensions, aliasing, forged native flags, resource restoration and costs.
Dense Gram adoption, basis transport, solves, arbitrary runtime coefficients,
dynamic interfaces, AD and complete native refinement remain outside this
increment. #67, #91, #183 and historical Stage 1 remain open.
