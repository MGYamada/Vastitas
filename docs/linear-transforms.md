# Typed dual, conjugate and metric adjoint (protocol 8)

Resource functions now construct selected dual and conjugate spaces, corresponding
bases, explicit canonical scalar involutions, declared coordinate Hermitian forms,
and read-only transformed maps. These operations compose with actual dependent
function inputs, nested resource loans and checked GEMM. This is an implementation
of finite coordinate operations, not general tensor evaluation or a proof of
floating-point algebraic laws. [#67](https://github.com/MGYamada/Vastitas/issues/67)
and [#91](https://github.com/MGYamada/Vastitas/issues/91) remain open.

## Objects, involutions and bases

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

## Declared Hermitian forms

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

## Map operations and resources

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
equivalent-C timings remain part of the [Fast like C gate](storage-ownership.md#713-performance-evidence-and-acceptance).

## Dependent function contracts

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

## Wire and proof boundary

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

## Example and regression evidence

```sh
cargo run --locked -- check --manifest-path examples/packages/linear-transforms/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/linear-transforms/Vastitas.toml \
  --openblas-prefix /path/to/openblas-0.3.34 -o /tmp/linear-transforms
/tmp/linear-transforms
```

On Linux, add the explicit `--native-cc cc` numerical consumer option as in
[the adapter guide](numerical-adapter.md). The example uses three original
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

[Vector evaluation](vector-evaluation.md) now executes bilinear dual evaluation
and explicitly conjugated Hermitian pairing for declared orthonormal forms.
General metric realization/transport and corresponding ideal identities remain work, as do
generative numerical packages, dynamic scalar/shape interfaces, finite networks
and equivalent-C performance acceptance. This increment does not close Stage 1.
