# Transforms, vector evaluation and metrics

Dual and conjugate spaces retain their origins. Vector evaluation and the supported metric operations require the corresponding bases, loans and explicit metric evidence.

<a id="linear-transforms"></a>

## Typed dual, conjugate and metric adjoint (protocol 8)

Resource functions now construct selected dual and conjugate spaces, corresponding
bases, explicit canonical scalar involutions, declared coordinate Hermitian forms,
and read-only transformed maps. These operations compose with actual dependent
function inputs, nested resource loans and checked GEMM. This is an implementation
of finite coordinate operations, not general tensor evaluation or a proof of
floating-point algebraic laws. [#67](https://github.com/MGYamada/Vastitas/issues/67)
and [#91](https://github.com/MGYamada/Vastitas/issues/91) remain open.

### Objects, involutions and bases

```vast
space v = linear(profiles::ComplexSmooth, 3);
basis bv = basis(v);
involution sigma = canonical(v);
space vd = dual(v);
space vc = conjugate(v, sigma);
basis bvd = derived(bv, vd);
basis bvc = derived(bv, vc);
```

`canonical` explicitly selects identity for an admitted real profile and complex
conjugation for an admitted complex profile. Its declaration/profile, nominal
scalar base, coefficient kind and geometric setting are reconstructed from the
same independently accepted indexed environment. Equal dimensions cannot supply
an involution or make real and complex profiles interchangeable.

Each space constructor selects a fresh nominal representation object. Derived
spaces retain their original space and operation, including the selected
involution for conjugation. Reusing that value through a function argument
preserves its identity; a second constructor does not implicitly identify two
objects. Double duals/conjugates do not silently become their original object.
General canonical transports and coherence laws are separate obligations.

`derived` selects the corresponding coordinate basis from an actual parent
basis and a matching derived space. An arbitrary `basis(vd)` is a basis on `vd`,
but is not automatically the dual basis of `bv`. Dual and conjugate origins
remain distinct even over real scalars. The full value audit checks every origin
and rejects cyclic references, forged profile data, and mismatched parents.

### Declared Hermitian forms

```vast
metric h = orthonormal(bv, sigma);
metric scaled = scaled_identity(bv, sigma, 2);
metric indefinite = diagonal(bv, sigma, [1, -2, 3]);
```

These declarations define coordinate forms by exact Gram data. In the ideal
real/complex interpretation, the convention is conjugate-linear in the first
ordinary-space argument and linear in the second: `h(x,y) = sigma(x)^T G y`.
`orthonormal` defines `G = I`; it does not assert that a sampled float matrix
has been measured orthonormal. The other constructors retain exact integer
diagonal entries, not machine-float observations. Nonzero diagonal entries are
required; their number must equal the dimension, with at most 4096 explicit
entries. `scaled_identity` stores one entry without expanding a large diagonal.
The zero-dimensional form has the usual empty, nondegenerate interpretation.

Negative entries are allowed: positive-definiteness is separate from
nondegeneracy. Direct adjoint lowering requires the declared Gram data to equal
identity in the used basis. All-one diagonal data is accepted; a form with
nonidentity Gram data is retained but requires an explicit supported Gram
realization before adjunction. No tolerance-based evidence, hidden Gram solve,
metric selection or conversion from conjugate space to dual space is inserted.

The checker proves the exact declared-data conditions and their connection to
the accepted operation. These conditions are not a theorem about an arbitrary
native matrix or a completed formal model of all Hermitian-module laws.

### Map operations and resources

For `a: V@bv -> W@bw`:

| Source operation | Effective endpoints | Coordinate operation |
| --- | --- | --- |
| `dual(a, bwd, bvd)` | `Wdual@bwd -> Vdual@bvd` | Transpose, with existing conjugation unchanged |
| `conjugate(a, bvc, bwc, sigma)` | `Conj<V>@bvc -> Conj<W>@bwc` | Explicit scalar conjugation, with axes unchanged |
| `adjoint(a, hv, hw)` | `W@bw -> V@bv` | Conjugate transpose for the declared orthonormal forms; real conjugation is identity |

```vast
map transformed = adjoint(a, hv, hw);
gemm(transformed, right, output, overwrite, NativeFast);
release(transformed);
```

The source and target metrics must name the exact used bases and the same
admitted involution. For example, `A=[i], Gv=[2], Gw=[3]` mathematically requires
`adjoint(A)=[-3i/2]`; this implementation rejects direct lowering for those forms
instead of incorrectly using `[-i]`. In orthonormal bases, the executable example
distinguishes `dual([i])=[i]` from `adjoint([i])=[-i]` and `conjugate([i])=[-i]`.

Every map transformation creates a real checked read child loan of the original
map loan. It retains the allocation, physical offset, leading dimension and byte
region; dual/adjoint toggle only the logical transpose. The parent is suspended
until the child is returned. Nested transformations require inside-out release.
The parent must already be readable and initialized. A lazy transformed map
cannot acquire write authority or escape as an owned result. Materializing its
product into an explicitly supplied destination uses the ordinary checked GEMM
and owned-result rules.

The operation record retains its original map, exact derived bases or metric
references, conjugation and complete child-loan snapshot. Function argument
reborrowing preserves this interpretation, including conjugation, and actual
calls check the caller's layout, initialization and aliases. A later raw
transpose/release cannot make a stale interpretation valid. The output of GEMM
must be an ordinary writable coordinate view, not a lazy conjugated destination.

Metadata, transforms and reborrows add no native allocation or copy. Only the
checked physical layouts and explicit flags reach the pinned GEMM adapter.
OpenBLAS may use internal packing/workspace; those costs and full-operation
equivalent-C timings remain part of the [Fast like C gate](../storage-ownership.md#713-performance-evidence-and-acceptance).

### Dependent function contracts

The following types refer to earlier parameters:

| Contract | Checked relation |
| --- | --- |
| `Involution<v>` | Admitted canonical involution for `v`'s actual profile |
| `DualSpace<v>` | Selected space with actual dual origin `v` |
| `ConjugateSpace<v,sigma>` | Selected space with that conjugate origin and involution |
| `DerivedBasis<bv,vd>` | Actual parent basis `bv` and selected derived space `vd` |
| `Metric<bv,sigma>` | Nondegenerate declared coordinate form for that basis and involution |
| `OrthonormalMetric<bv,sigma>` | The same contract, additionally requiring exact identity Gram data |

Plain `Space<profile,n>` and `Basis<v>` remain usable for operations that need
only those properties. Headers do not infer derived-basis or metric facts from
them. All-body synthetic probes reconstruct the declared dependencies; a helper
requiring direct adjunction must request the orthonormal contract. Probes never
become executable receipts. Every actual call independently checks the real
arguments and their borrowed or owned resources.

<a id="linear-transforms--wire-and-proof-boundary"></a>

### Wire and proof boundary

Protocol 8 adds `dual_space`, `conjugate_space`, `derived_basis`, `involution`,
`metric` and `transform` numerical operations. The last has an unresolved parent
name and a strict nested operation (`dual`, `conjugate`, or `adjoint`), naming
bases, an involution or metrics. Gram entries are exact decimal strings in a
strict `identity`, `scaled_identity`, or `diagonal` object. The dependent
parameter forms use the corresponding tags; metric headers explicitly record
the orthonormal requirement. These are source names and declared data, never
trusted IDs, raw native flags, prechecked tags or tolerance certificates. Unknown
nested fields and old protocol envelopes are rejected. Older protocol-8 kernels
reject the new operations; use a matching frontend/kernel revision.

`StorageNumerical.checkTransform` checks the original live map, exact metric
contract, actual resource borrow, full value provenance and returned live view.
`StorageFunctions` replays the borrow and records its exact emitted schedule.
The public checker audits transform receipt origins against the declaration
environment of the same full authority/Fn/dispatch source check.

The oracle's `actual_transform`, `transform_storage`, `dual_flags`,
`conjugate_flags`, `adjoint_flags`, `adjoint_forms`, `declared_metric` and extended
`input_map_reborrow` refer to these actual certificates.
`public_numerical_transform_origin` connects them to the accepted public request.
These prove structural types, explicit form selection, resource provenance and
the exact lowering connection, not general source/native refinement, float field
laws or all mathematical adjoint identities.

### Example and regression evidence

```sh
cargo run --locked -- check --manifest-path examples/packages/numerical/linear-transforms/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/numerical/linear-transforms/Vastitas.toml \
  --openblas-prefix /path/to/openblas-0.3.34 -o /tmp/linear-transforms
/tmp/linear-transforms
```

On Linux, add the explicit `--native-cc cc` numerical consumer option as in
[the adapter guide](maps-and-gemm.md#numerical-adapter). The example uses three original
buffers, padded layouts, two levels of function calls and one reused destination.
It checks every one-dimensional output, then prints `42`.

`TransformRegression` checks rectangular real/complex transformed composition,
origin and metric mutations, actual allocation retention, parent suspension,
nested loan returns and forged native flags. Public source/wire tests cover
wrong nominal objects and bases, missing/degenerate forms, non-orthonormal bases,
incompatible involutions, weak or forged contracts, unused invalid helpers,
old envelopes and output-file preservation. Optional numerical CI executes
real/complex rectangular examples through actual source check/build and native
GEMM. A metadata-only entry with unused valid numerical helpers builds and runs
without OpenBLAS.

[Vector evaluation](#vector-evaluation) now executes bilinear dual evaluation
and explicitly conjugated Hermitian pairing for declared orthonormal forms.
[Explicit diagonal metrics](#diagonal-metrics) additionally support materialized
adjoints and scratch-backed Hermitian pairing, with actual declared coefficient
realization and conditional ideal laws. Dense metric realization/transport remains work, as do
general generative numerical packages, dynamic scalar/shape interfaces, general
networks and equivalent-C performance acceptance. Bounded [contraction trees](networks-and-packing.md#contraction-trees)
and [packing caches](networks-and-packing.md#cached-packing) have their own implemented contracts. This increment does not close Stage 1.

<a id="vector-evaluation"></a>

## Bilinear vector evaluation and explicit Hermitian pairing

Package-only protocol 8 checks coordinate vectors, explicit vector conjugation,
algebraic dual evaluation and an orthonormal Hermitian pairing. The actual
source checker connects nominal bases and derived-space origins to live storage
loans, the exact GEMM schedule and native execution. This advances
[#67](https://github.com/MGYamada/Vastitas/issues/67) and the finite-network
foundation under [#69](https://github.com/MGYamada/Vastitas/issues/69); neither
issue is completed by this increment.

### Values and operations

```vast
space v = linear(profiles::ComplexSmooth, 3);
basis bv = basis(v);
space vd = dual(v);
basis bvd = derived(bv, vd);
involution sigma = canonical(v);
space vc = conjugate(v, sigma);
basis bvc = derived(bv, vc);
metric h = orthonormal(bv, sigma);
vector x = view(vector_loan, bv);
vector phi = view(covector_loan, bvd);
evaluate(phi, x, scalar_output, overwrite, NativeFast);
```

A vector retains one actual basis and a complete loan snapshot. Its logical
layout is a column with `dimension` rows and one column; physical offset,
padding, leading dimension and transpose remain explicit. A covector uses a
selected dual space and the corresponding dual basis. A raw column with the
same dimension does not grant that role. Independent spaces/bases stay distinct.

`evaluate` requires `phi`'s basis to originate from `x`'s exact basis and its
space to have the actual dual origin. Its ideal target is `sum_i phi_i*x_i`,
with no newly inserted conjugation. Two ordinary vectors or a conjugate-space
vector used as a dual vector are rejected. Already explicit coordinate
interpretations are preserved through calls.

```vast
vector conjugated = conjugate(x, bvc, sigma);
hermitian(conjugated, y, scalar_output, h, overwrite, NativeFast);
release(conjugated);
```

`hermitian` consumes a vector in the selected `Conj<V>` and a vector in `V`,
with corresponding bases and an explicit matching declared form. It does not
insert `conjugate`. For identity Gram data, its ideal target on ordinary
arguments is `h(x,y) = sum_i sigma(x_i)*y_i`. A value already in `Conj<V>` is
also valid; constructing its coordinate view does not conjugate the payload.

For complex `[i]` and `[i]`, algebraic evaluation returns `-1` while the explicit
conjugation pairing returns `+1`. For `[1+2i]`, the results are `-3+4i` and `5`.
These finite native regressions distinguish the operations; they do not prove
floating-point bilinearity or exact field laws.

The direct pairing requires identity Gram data in the used basis, including
an all-one diagonal. Other nondegenerate forms remain valid declared data but
need an explicit supported Gram realization; this lowering rejects them.
General metric realization, transport and applicable ideal laws remain work.

### Resources, calls and output

The output is an explicit raw scalar loan of matching real/complex storage and
logical shape `1 x 1`, not an arbitrary one-dimensional mathematical object.
`overwrite` requires write authority and never reads old output; `accumulate`
requires initialized read/write output. Optional `alpha`/`beta` literals and
`coefficient(loan)` use GEMM's scalar, initialization and output-separation
rules. Accumulation realizes the scaled evaluation plus `beta*C_old`.

Each evaluation checks the original live vectors, borrows a transposed read
child for the left coordinates and an unchanged read child for the right,
checks/emits GEMM, then releases the children inside out. The certificate
rechecks the whole schedule, restored input snapshots and initialized scalar
output. Shared readable inputs are allowed; output and coefficient aliases
still need the actual byte-region checks.

Conjugation itself creates a read child. Its parent stays suspended until
release: `hermitian(conjugate_child, parent, ...)` cannot reuse that parent
handle directly. For `h(x,x)`, pass the same readable vector as two function
arguments. Actual binding creates compatible sibling read loans; conjugation
of one leaves the other usable. Separate read loans of the same immutable
allocation also work. No hidden copy repairs a conflict.

`ReadVector<basis>` refers to an earlier basis parameter. Like map parameters,
the wire carries explicit access/initialization contracts for vector borrowing
(`WriteVector`, `ReadWriteVector`, `initializes`). These preserve basis,
conjugation and allocation/layout but confer no operation or permission beyond
the actual child loan. Unused bodies have separate probes; every executable
call checks its real caller. Borrowed vectors cannot become owned results or
escape branch scope. Owned vector/tensor packaging and general vector operations
remain separate work; raw owned buffers retain existing return rules.

Evaluation/conjugation introduce no data allocation, copy or packing buffer.
The example reuses one output allocation. Its scalar results use the adapter's
[fused scalar loop](maps-and-gemm.md#numerical-adapter--scalar-outputs) rather
than BLAS. Full runtime remains part of the [Fast like C gate](../storage-ownership.md#713-performance-evidence-and-acceptance).

### Independent checking and evidence

Rust and Lean share strict unresolved protocol-8 forms: `vector`,
`conjugate_vector`, and `evaluate` with a nested `dual` or `hermitian` operation.
Headers use `kind: "vector"`, a basis name, access and initialization requirement.
Native flags, allocation IDs, checked tags and origin certificates are not
source authority. Old versions reject these payloads; older protocol-8 kernels
reject the new operations. Use a matching frontend/kernel revision.

`StorageEvaluation.checkVectorConjugate` validates actual origins, basis,
involution and borrow. `checkEvaluation` connects the exact dual or explicit
Hermitian contract to original live inputs, real child loans, `checkGemm`,
replayed schedule, restored snapshots and initialized output. The function
compiler independently replays that schedule and records exact emitted code.
The public checker audits every receipt against the same full
authority/Fn/dispatch check's accepted declaration environment.

The oracle's `vector_space`, `vector_input_reborrow`,
`actual_vector_conjugation`, `actual_evaluation`, `dual_evaluation_types`,
`hermitian_evaluation_form`, `evaluation_preserves_interpretation` and
`evaluation_returns_inputs_and_scalar` extract those actual-checker facts.
`public_vector_conjugation_origin` and `public_evaluation_origin` connect them
to the public request. These are structural/resource/lowering proofs, not
general ideal-module laws or native numerical refinement.

`EvaluationRegression` covers real/complex dimensions 0/1/3, ordinary and
physically transposed columns, provenance/flag mutations, initialization,
aliases, suspended parents, both branch states and native-plan audits. Public
tests cover nested repeated read inputs, malformed wire, old versions, invalid
unused helpers, artifact preservation and metadata-only execution without
OpenBLAS. Numerical CI executes all shape/orientation cases, mixed complex
components and explicit accumulation.

```sh
cargo run --locked -- check --manifest-path examples/packages/numerical/vector-evaluation/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/numerical/vector-evaluation/Vastitas.toml \
  --openblas-prefix /path/to/openblas-0.3.34 -o /tmp/vector-evaluation
/tmp/vector-evaluation
```

On Linux add `--native-cc cc`, as in [the adapter guide](maps-and-gemm.md#numerical-adapter).
The program checks both distinct complex results and prints `42`. Empty
evaluation uses the adapter's documented zero-inner convention; it supplies
no separate exact-field theorem.

[Explicit diagonal metrics](#diagonal-metrics) extend Hermitian evaluation to
non-orthonormal declared diagonal forms through caller scratch and a compound
preflight, with conditional ideal pairing/adjoint laws. Dense forms and basis
transport remain outside that increment.

[Bounded contraction trees](networks-and-packing.md#contraction-trees) now validate rank-two/three
occurrences, ports, edges and boundaries with explicit schedules and regrouping;
[packing caches](networks-and-packing.md#cached-packing) check retained scratch dependencies.
General-rank networks, broader generative numerical packages, dynamic interfaces
and equivalent-C acceptance remain open Stage 1 work.

<a id="diagonal-metrics"></a>

## Explicit diagonal metrics (protocol 8)

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

### Realization and resource contract

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

### Native costs and failure boundary

`adjoint_into` executes one O(mn) pass and writes mn scalar-width bytes.
`hermitian_diagonal` executes one O(n) weighting pass and one existing GEMM,
writing (n+1) scalar-width bytes, or just the zero scalar when n=0. The adapter
runs that 1×1 GEMM as its [fused scalar loop](maps-and-gemm.md#numerical-adapter--scalar-outputs)
over the scratch vector, without a BLAS driver call. Both reuse
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
The [prepared adapter/C experiment](https://github.com/MGYamada/Vastitas/blob/main/experiments/diagonal_metrics/README.md)
reports actual costs and performance gaps. It excludes public-source/FFI and
lifecycle costs and does not close the [Fast like C gate](../storage-ownership.md#713-performance-evidence-and-acceptance).

### Checking, proofs and examples

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
cargo run --locked -- check --manifest-path examples/packages/numerical/diagonal-metrics/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/numerical/diagonal-metrics/Vastitas.toml \
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
