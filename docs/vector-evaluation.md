# Bilinear vector evaluation and explicit Hermitian pairing

Package-only protocol 8 checks coordinate vectors, explicit vector conjugation,
algebraic dual evaluation and an orthonormal Hermitian pairing. The actual
source checker connects nominal bases and derived-space origins to live storage
loans, the exact GEMM schedule and native execution. This advances
[#67](https://github.com/MGYamada/Vastitas/issues/67) and the finite-network
foundation under [#69](https://github.com/MGYamada/Vastitas/issues/69); neither
issue is completed by this increment.

## Values and operations

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

## Resources, calls and output

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
The example reuses one output allocation. BLAS-internal workspace and full
runtime remain part of the [Fast like C gate](storage-ownership.md#713-performance-evidence-and-acceptance).

## Independent checking and evidence

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
cargo run --locked -- check --manifest-path examples/packages/vector-evaluation/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/vector-evaluation/Vastitas.toml \
  --openblas-prefix /path/to/openblas-0.3.34 -o /tmp/vector-evaluation
/tmp/vector-evaluation
```

On Linux add `--native-cc cc`, as in [the adapter guide](numerical-adapter.md).
The program checks both distinct complex results and prints `42`. Empty
evaluation uses the adapter's documented zero-inner convention; it supplies
no separate exact-field theorem.

[Explicit diagonal metrics](diagonal-metrics.md) extend Hermitian evaluation to
non-orthonormal declared diagonal forms through caller scratch and a compound
preflight, with conditional ideal pairing/adjoint laws. Dense forms and basis
transport remain outside that increment.

[Bounded contraction trees](contraction-trees.md) now validate rank-two/three
occurrences, ports, edges and boundaries with explicit schedules and regrouping;
[packing caches](cached-packing.md) check retained scratch dependencies.
General-rank networks, broader generative numerical packages, dynamic interfaces
and equivalent-C acceptance remain open Stage 1 work.
