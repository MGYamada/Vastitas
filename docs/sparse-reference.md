# Exact CSR pattern and SpGEMM reference

This is the small, standard-library-only Python entry point for
[#243](https://github.com/MGYamada/Vastitas/issues/243):

- [`scripts/sparse_reference.py`](../scripts/sparse_reference.py): validated CSR,
  exact COO aggregation, structural product bounds and plan dependencies.
- [`scripts/test_sparse_reference.py`](../scripts/test_sparse_reference.py):
  semantic and rejection regressions with independent dense/Boolean oracles.
- [`scripts/demo_sparse_reference.py`](../scripts/demo_sparse_reference.py):
  deterministic text observations, with distinct slot/nonzero/product counts.

These files do not implement production `std::sparse`, Graph lowering, an
Ownership Checker, a graph schema, native sparse kernels or Lean certificates.
The reference is not a compiler/runtime dependency. Its results are neither
speedup measurements nor evidence of GPU execution, and do not close #243.

```sh
python3 -m unittest discover -s scripts -p 'test_sparse_reference.py' -v
python3 scripts/demo_sparse_reference.py
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
```

Existing CI discovers `test_*.py`; no new workflow or dependency is needed.

## Representation and arithmetic contract

The coefficient model is exactly **Q**, implemented by `Fraction`. Raw inputs
accept only Python integers and `Fraction`, excluding `bool`, Float (including
NaN/infinity), complex values and caller-defined semirings. The mathematical
zero has annihilation and additive-identity laws. No Float reduction order,
threshold dropping, fast-math policy or floating-point error bound is inferred.

`Pattern` holds shape, row offsets, column indices, integer widths and a
descriptive label/revision. It is an immutable, nominal fixture snapshot:
the **same pattern object** is required for reuse. `CSR.with_values` retains it.
A separately constructed equal-looking pattern, even with the same label and
revision, is different. Labels and hashes cannot prove identity. A production
pattern registry, generative identity and revision discipline are still needed;
Python identity is process-local and not a serializable or security certificate.
Input sequences are copied to tuples, preventing accidental later list mutation.

Within a row, CSR indices must be **strictly increasing**; duplicates and
unsorted rows are rejected. COO construction aggregates duplicate coordinates
by exact addition in encounter order, then sorts coordinates lexicographically.
Every encountered position survives, including explicit zero and a duplicate
sum of zero. Thus a raw COO entry count, a canonical CSR slot count and a
numerical nonzero count can all differ. No automatic `eliminate_zeros` is used.

Validation checks shape, exactly `rows + 1` offsets, first offset zero, terminal
offset equal to the slot count, monotonicity, all offset/index ranges, canonical
rows and one value per slot. Repeated offsets encode empty rows. Zero-sized
shapes still undergo metadata validation and generate no products.

The explicit integer profile uses **unsigned** widths from 1 to 64 bits:

| Quantity | Required range |
| --- | --- |
| Rows, columns, indices | `0 .. 2^index_bits - 1`; actual indices must also be inside shape |
| Offsets, raw COO count, canonical/output slots, `rows + 1` | `0 .. 2^offset_bits - 1` |
| Multiplication contributions | `0 .. 2^count_bits - 1` |

Dimensions fitting the index width is a conservative reference convention;
it does not admit a dimension `2^index_bits`. Input profiles must match exactly;
there is no implicit narrowing or widening. Python integers compute sums before
range checks; overflow is rejected rather than wrapped. Small widths exercise
valid maximum counts and overflowing output/work counts without huge arrays.
32/64-bit column boundaries are also tested with only one stored entry.
These checks concern logical metadata, **not** signed BLAS limits, physical
byte sizes, alignment, pointer arithmetic or allocation success. `Fraction`
has variable-sized storage, so native value-buffer bytes remain unknown.

## Structural bound and the cancellation regression

For stored position sets `P_A` and `P_B`, the inspector computes

`P_C = {(i,j) | exists k, (i,k) in P_A and (k,j) in P_B}`.

It records every pair of input slots contributing to each output slot, in
increasing `k` order. It never reads values. Under this exact coefficient
model, absent positions are zero and zero annihilates multiplication, giving
`support(AB) subset P_C`. This is the mathematical argument implemented and
tested here, **not a newly machine-checked Lean theorem**.

`require_structural_bound` allows a candidate superset of `P_C`, and rejects
any missing candidate position even when its current result is zero. There is
deliberately no interface for caller-supplied cancellation certificates. In
particular, the empty pattern is rejected for `[1] * [1]`, and also for a
stored `[0] * [1]`. Checking only `candidate subset P_C` would be unsound.

The requested example has four slots in each input. Only B's values change:

| Result | Dense value | Output structural slots | Numerical nonzeros | Multiplication contributions |
| --- | --- | ---: | ---: | ---: |
| `AB` | `[[0,1],[-1,0]]` | 4 | 2 | 6 |
| `AB'` | `[[-1,1],[-2,-2]]` | 4 | 4 | 6 |

The two diagonal slots remain in the plan after initial cancellation. These
counts have different meanings: slots are exactly the relational bound's
size, numerical nonzeros are observations of one execution, and contributions
count input-slot products **including products by stored zero**. Contributions
are independently checked against `sum_k col_degree_A(k) * row_degree_B(k)`.
They count Q multiplications, not machine FLOPs or an execution-time estimate.
The executor adds each product to a zero-initialized rational accumulator;
index lookup/aggregation/allocation costs are not included in that count.

## Reuse and invalidation

| Change | Structure-only SpGEMM plan | First-pivot-guard demonstrator |
| --- | --- | --- |
| Values change, same patterns and binding | Reusable, including zero/nonzero transitions | Reusable only if the selected pivot row is still the same and nonzero |
| Cancellation changes numerical support | Reusable; output slots remain present | Pivot dependency is checked separately |
| Pattern, revision or nominal snapshot changes | Invalidated, even if mathematical values coincide | Invalidated |
| Fixture operation occurrence or method revision changes | Invalidated | Invalidated |
| Maximum-absolute pivot moves or all candidates become zero | Reusable | Invalidated; reinspection needed |
| Output slots or contribution schedule are altered | Rejected by the plan audit | Rejected by the same audit |

`Binding` models the dependency on an occurrence and method revision; its
labels are fixture data, not actual compiler identities. The only execution
profile is exact rational CSR SpGEMM in Python. Other operations, targets,
algorithms and numerical policies are not implemented by this plan API.

`PivotGuardPlan` observes only the first partial-pivot choice in one specified
column of the left operand: maximum absolute value, with the lowest row
winning ties. It does not implement LU, check subsequent Schur-complement
pivots or cache numerical factors. It illustrates a value-dependent condition
that must be revalidated. Every successful execution still recomputes the
full product using current values and the unchanged structural schedule.
Cached factors would require their own complete numerical dependencies.

For a transparent tamper regression, execution deliberately **recomputes the
symbolic audit** and compares the complete output layout and contribution
schedule. The same plan object is reused logically, but this is not an
optimized amortized inspector/executor. Python dataclass validation is not a
hostile-code security boundary. No externally authored plan may reach native
codegen on the strength of this audit.

The tests cover all 256 pairs of 2x2 Boolean patterns against an independent
relational oracle and dense multiplication, all 81 signed value assignments
for a fixed 1x2-by-2x1 pattern, and 100 seeded rectangular rational cases with
three value states each. Rejection cases cover malformed CSR/COO, explicit
zeros, duplicates, empty dimensions/rows, widths, stale nominal snapshots,
changed bindings, numerical guards and missing/reordered contributions.

## Information for the shared graph emit (#242)

[#242](https://github.com/MGYamada/Vastitas/issues/242) owns the canonical graph,
cost expression AST, diagnostics and JSON/DOT/SVG views. The table below is an
integration inventory, **not a sparse graph schema or a second emitter**.
The demo prints text only and cannot be imported as checked graph data.

| Information | Available reference observation | Required production origin/status |
| --- | --- | --- |
| Operation occurrence and method revision | `Binding` fixture labels | Exact returned Core, canonical declaration/method/profile and ordered port identities; unresolved here |
| Pattern identity/revision and layout | Immutable `Pattern`, canonical CSR arrays and widths | Actual validated pattern registry/storage provenance; fixture identity confers no authority |
| Structural slots and degrees | Exact slot counts, offset differences and index histograms | #242 advisory annotations attached to the same checked occurrence; not numerical support |
| Product support bound | Exact relational candidate positions | Checked input support bounds and actual coefficient/profile laws; mathematical bound, no Lean evidence here |
| Work | Exact scalar multiplication contribution count | Shared cost AST constant or degree-sum expression with units/convention; not timing or Float FLOPs |
| Numerical nonzeros | Exact value-snapshot observation | Explicit current-value dependency; never a structure-only omission permission |
| Plan dependencies | Input snapshots, binding, optional pivot guard | Core/graph occurrence, method/profile, layout/target/algorithm revisions and every evidence dependency |
| Missing/stale evidence and denied omissions | Local `S_*` exception codes/reasons | Reconcile with shared diagnostics catalog and statuses; these are reference codes, not a new canonical catalog |
| Output/workspace bytes, aliasing, initialization, lifetime | Unknown | Existing Storage/Ownership validation over actual allocations and accesses |
| Allocations, transfers, peak live memory, synchronization, inspect cost and speed | Unknown/unmeasured | Explicit cost model or runtime observations under #242; never fabricated from slot counts |
| Checked acceptance and export coverage | No production acceptance/export | Actual kernel outcome and honest partial/unsupported coverage; no synthetic `verified` status |

## Remaining production boundaries

Checked against main `2d6a86ce4c8a44bd883d879035aa9c924ed8fc71`:

- [`Graph`](graph-crossings.md) checks the internal crossing-word fragment.
  Public tensor/source lowering and its bridge to `Indexed.Core.Term` remain
  pending; this reference adds no sparse operation to either Core.
- [Protocol 8](resource-source.md) now connects the initial static package
  resource profile to the existing [Storage checker](storage-ir.md). That
  connection does not establish CSR support, initialized index/value buffers,
  sparse destination/scratch alias rights or this plan's physical validity.
- CSR lowering must use that existing ownership path for allocations, byte
  arithmetic, initialized reads, exclusive writes, lifetimes and actual
  returned schedule/codegen audits. It must not infer disjointness from
  different pattern IDs or create another borrow checker.
- Sparse pattern laws, selected method/profile realization, exact Core-to-plan
  correspondence, actual native refinement and supported Float policies need
  their own checked integration and proofs. Sector/block elimination, generic
  semirings, SpMV/SpMM, factorization and sparse storage formats beyond CSR/COO
  are outside this increment.
- CUDA streams/events, asynchronous owner/workspace retention and cancellation
  remain under `monad::cuda`/`monad::resource`; no GPU path is exercised here.
  Native CPU kernels and fair SuiteSparse/oneMKL/cuSPARSE performance comparisons
  remain separate future work.
