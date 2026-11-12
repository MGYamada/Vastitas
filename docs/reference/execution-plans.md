# Execution and planning reference models

This chapter describes five [reference models](../appendix/reference-models.md)
of execution and planning. They are finite: the reuse of GPU storage, sparse
patterns and their products, reduction plans, the split between `Float` and
`SafeFloat`, and the invalidation of dependent modules. Each is a Python
program with tests under `scripts/`, and each section states its hypotheses,
its verifier and its regression examples. None is a part of the compiler.

| Model | In the compiler |
| --- | --- |
| [CUDA storage reuse](#cuda-reuse-reference) | Model only. Implemented: storage on the host, with the checks of allocation, initialization, loans and release that [Storage and ownership](../storage-ownership.md) and [Resource programs](../storage/resource-programs.md) specify. The compiler generates no GPU code. Planned: [#266](https://github.com/MGYamada/Vastitas/issues/266), [#210](https://github.com/MGYamada/Vastitas/issues/210) |
| [CSR patterns and SpGEMM](#sparse-reference) | Model only. Implemented: dense [numerical maps](../linalg/maps-and-gemm.md) and their matrix products. Planned: [#243](https://github.com/MGYamada/Vastitas/issues/243) |
| [Reduction plans](#reduction-reference) | Model only. Implemented: the [contraction trees](../linalg/networks-and-packing.md#contraction-trees) that a program declares for a tensor network. The reassociation of a reduction under declared laws is a model only. Planned: [#303](https://github.com/MGYamada/Vastitas/issues/303) |
| [Float and SafeFloat](#float-reference) | Model only. Planned: [#318](https://github.com/MGYamada/Vastitas/issues/318), [#322](https://github.com/MGYamada/Vastitas/issues/322) |
| [Dependency invalidation](#incremental-reference) | Model only. Planned: [#339](https://github.com/MGYamada/Vastitas/issues/339) |

Each section keeps the record of the change that added its model. Its
statements about the compiler describe the repository at that change.

<a id="cuda-reuse-reference"></a>

## Finite CUDA reuse planning reference (#266)

This standard-library-only Python experiment computes maximal-use frontiers,
audits release/reuse order, and compares two explicit schedules for
[#266](https://github.com/MGYamada/Vastitas/issues/266). It **assumes the cleanup
contract of [#210](https://github.com/MGYamada/Vastitas/issues/210)**; it does not
reimplement its keeper, ticket, cancellation, event-recording, physical-free or
acknowledgement state machine. No CUDA calls, compiler changes, Lean proofs or
package-registration requirements are added.

The implementation baseline is main
`2d6a86ce4c8a44bd883d879035aa9c924ed8fc71`. That revision has the initial static
[protocol-8 resource composition](../storage/resource-programs.md) and the internal
[Graph crossing checker](../verification/core-models.md#graph-crossings). This Python model is connected to
neither. Its names are fixture identifiers, not accepted Core identifiers.

### Run

Python 3.10 or later; no third-party dependencies or GPU are needed.

```sh
python3 -m unittest discover -s scripts -p 'test_cuda_reuse_reference.py' -v
python3 scripts/demo_cuda_reuse_reference.py
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
```

- [Reference](https://github.com/MGYamada/Vastitas/blob/main/scripts/cuda_reuse_reference.py): immutable input records,
  frontier analysis, independent order audit, optional cost analysis and fallback.
- [Demo](https://github.com/MGYamada/Vastitas/blob/main/scripts/demo_cuda_reuse_reference.py): explicit hypothetical cleanup
  snapshots and JSON reports; prints to stdout and does not alter source files.
- [Tests](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_cuda_reuse_reference.py): negative coverage/identity/order
  cases and an independent permutation oracle. Existing Python test discovery
  finds them; no workflow or release gate is added.

### Input and authority boundary

`audit(expected_workload, candidate, cleanup_contract)` receives three separate
values. The candidate never supplies the expected workload or cleanup evidence
implicitly. A successful audit means **verified in this finite reference model**,
conditional on the independently supplied fixture inputs; it never authorizes
production lowering or reuse.

| Input | Content and responsibility |
| --- | --- |
| `Workload` | Complete operation/access inventory; nominal allocation identity **and generation**; owner, allocate/release nodes, stream epochs, concrete byte size, alignment, layout, pool class, closed lifetime, required dependencies and exact binding |
| `Candidate` | Exact subject, proposed additional order edges and allocation-to-slot assignment; no verified flags, claimed frontier or inferred completion |
| `CleanupContract` | Exact subject, sealed use ledger, full operation submission receipts and audited ordering receipts from the assumed #210 boundary |

Bindings contain synthetic Core/environment/adapter identities, runtime instance
and context epoch. Each submission and ordering receipt carries its own binding;
ordering receipts also carry both **full endpoint operations**, including access
generations. Copying an old receipt under a current snapshot header does not
make it current. Identical pointer-like names, shapes, operation names or
stream-local sequence numbers do not identify allocation lifetimes.

The operation inventory includes operands, outputs and workspaces equally. The
auditor reconstructs the complete use set from it and compares **every allocation**
with the sealed ledger. Missing/extra/duplicate tickets, missing allocations,
unknown workspace coverage, open/escaped lifetimes, stale generations and missing
receipts block the reference plan. An opaque operation with an incomplete memory
contract cannot be used to establish a last-use frontier.

The fixture's complete-coverage fields are explicit **preconditions**, not proofs
that arbitrary FFI code has no hidden accesses. A consumer omitted from both the
independent inventory and the cleanup ledger is not discoverable by this model.
Production must derive these records from actual accepted Core and independently
validated adapter contracts, including staging buffers, retained library state,
aliases, borrowed views and all workspace tickets. A caller setting a Boolean or
writing matching labels cannot satisfy that production obligation.

The #210 provider is assumed to have validated each `event_wait` receipt's exact
recording frontier, event generation, stream/context epochs and enqueued
wait chain. This reference does not repeat that verification, by design. It
checks endpoint/binding identity and requires definite enqueue outcomes for every
operation and ordering receipt. Partial, unknown, not-enqueued, cancellation,
stream-destruction and host-enqueue observations never establish reusable order.
`enqueued` is **not** `completed`: the relation describes device execution order.
Allocation nodes denote acquisition/start-of-lifetime positions; modeling a real
asynchronous acquisition protocol remains outside this experiment and #210's
initial completed-acquisition profile.

Python dataclasses are not a security boundary. Inputs use a typed in-process API;
there is no JSON decoder, production certificate importer, CUDA handle lookup or
protection against reflective mutation. Replacing all trusted fixture inputs
changes the modeled statement. Python execution and this algorithm are unproved.

### Frontier and independent audit

`Dag.frontier(Uses(b))` computes the maximal uses in the transitive dependency
relation. Incomparable final consumers remain separate. `propose_separate` adds
joins from every frontier element to release, without ordering independent
allocations. An unused allocation still needs allocation-before-release.
`propose_reuse` adds release-before-next-allocation edges for **one explicit chain**
and assigns it a shared slot. It performs no global optimization or contraction
tree rewrite.

The audit reconstructs the actual DAG from the separate #210 contract view,
requires an acyclic graph and exact coverage of the candidate's required/added
edges, and independently checks:

```text
for every allocation b and every use u in the reconstructed complete Uses(b):
    alloc(b) < u < release(b)
    alloc(b) < release(b)       # also required when Uses(b) is empty

for every pair b,c assigned to the same slot:
    release(b) < alloc(c) OR release(c) < alloc(b)
```

Thus even a candidate and receipt set that agree on an unsafe one-sided wait
are rejected. The auditor checks every use; it does not take the planner's
frontier as a proof. Exact edge-set matching also prevents an omitted realized
dependency from making the reported parallelism appear better. Extra harmless
edges require a matching candidate and fresh audit.

Slots are abstract, pairwise disjoint, whole-allocation regions. Within one slot,
layout, alignment and pool class must match exactly; capacity is the maximum
concrete size of its occupants. Unknown/symbolic sizes are unsupported and cannot
grant reuse. This conservative fragment does not check arbitrary byte offsets,
partial overlap, writes, initialization or loans. Those remain the mandatory
[#183 storage obligations](../storage-ownership.md), separately preserved by #210.
In particular, reuse does **not** inherit old contents as initialized data in a
fresh generation. There is no numeric reassociation or operation rewriting here.

### Reproduced experiments and cost interpretation

The independent five-node permutation test reproduces the original counts:
one-sided join has **4** valid orders, **2** releasing before `use_2`; joining both
uses leaves **2** orders, both safe in that model. An extended closed six-node
fixture additionally checks all 8 subsets of the two joins and reuse edge against
all `6!` permutations. Only the fully joined, ordered-reuse case is admitted.

For two independent 64-byte workspaces with hypothetical operation durations 3
and 5:

| Candidate | Peak live slot bytes | Hypothetical makespan | Work pair that the candidate orders |
| --- | ---: | ---: | --- |
| Separate allocations, preserve parallelism | 128 | 5 | None |
| Reuse one slot, A then B | 64 | 8 | `use_A` before `use_B` |

Neither candidate dominates the other on these two objectives. No policy silently
chooses the smaller-memory candidate. `estimate` computes peak live slot bytes
over **all dependency-respecting prefixes** (finite order ideals), not one chosen
topological order. Its optional enumeration is limited to 14 nodes. Makespan is
the weighted critical path assuming unlimited processors and supplied durations;
it excludes unmodeled synchronization, allocation and remapping costs. Unknown
durations produce `unknown`, and the enumeration limit never blocks an otherwise
valid order audit. Pool-reserved VRAM and overhead are explicitly `unknown`.

These numbers are neither CUDA scheduling predictions nor measured performance.
Ending an allocation lifetime does not imply returning cached pages to the driver.
The tests establish no real-GPU safety, speedup, global optimum or Lean theorem.

### Proposed handoff to common graph emit (#242)

`emit` generates the advisory `vastitas.cuda-reuse-reference.v1` payload. It is an
**illustrative extension** for [#242](https://github.com/MGYamada/Vastitas/issues/242),
not its implemented canonical graph schema or the `vastitas --emit graph` CLI.
It re-audits when producing facts; an old report or edited JSON cannot supply them.
Canonical ordering makes repeated and inventory-order-permuted inputs emit the
same JSON. The payload carries:

| Record | Proposed common-emit information |
| --- | --- |
| Expected subject | Exact fixture binding, operations/streams, allocations/generations/owners, workspace access roles, concrete size/alignment/layout/pool profile |
| Candidate | Added dependencies, slot assignments and exact subject; always separate from facts |
| Candidate costs | Max-of-stage-byte-sums expression AST (constant leaves in this fragment), estimated time, the work pairs that the candidate orders (`newly_ordered_work_pairs`), added edges, assumptions, unknown overhead/pool reservation |
| Verified reference facts | Complete uses, recomputed last-use frontiers, allocate/release positions, slot groups, exact order edges/kinds and receipt identities |
| Unresolved fields | Logical retire node (`null`, owned by #210), real Core/source provenance, adapter realization, actual pool bytes, symbolic dimensions, region/initialization/loan facts and runtime measurements |
| Diagnostics/integration | Stable reference codes; candidate analysis and contract-audit failures kept distinct; actual accepted Core, CUDA adapter and common emitter explicitly unconnected |

Cost `exact` means exact **within the declared finite model**, never a verified
production cost. A future symbolic extension must retain canonical polynomial
terms and maxima of liveness-stage sums instead of inventing numeric savings.
Production would project this information from actual audited Core, then recheck
the selected order/storage plan against that same Core, shape specialization,
numerical policy and supported adapter. Stream-ordered pools, CUDA Graph memory
nodes and unsupported capture/peer/IPC/managed-memory profiles must remain distinct.
Lowering correspondence and scoped MS integration are future obligations; a proof
about a second Python model cannot discharge them.

### Optional optimization and conservative fallback

`select(..., optimize=False)` defaults to the ownership-cleanup fallback. Missing
or rejected evidence also selects it: allocate separate storage, grant **no** early
release/reuse permission, and leave all outstanding/possibly submitted resources
and quarantine with the existing #210 keeper. The fallback does not execute an
unvalidated free, discard tickets, retry ambiguous free, assume completion, or
promise eventual reclamation on a stalled device.

An admitted reference plan still returns `production_reuse_permission: false`.
Mandatory ownership and async lifetime safety are independent of this optional
analysis. There is no package-registration gate, language-level optimization or
performance obligation, added Domain Checker, constitutional theorem, release
milestone, or added public acceptance route.

<a id="sparse-reference"></a>

## Exact CSR pattern and SpGEMM reference

This is the small, standard-library-only Python entry point for
[#243](https://github.com/MGYamada/Vastitas/issues/243):

- [`scripts/sparse_reference.py`](https://github.com/MGYamada/Vastitas/blob/main/scripts/sparse_reference.py): validated CSR,
  exact COO aggregation, structural product bounds and plan dependencies.
- [`scripts/test_sparse_reference.py`](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_sparse_reference.py):
  semantic and rejection regressions with independent dense/Boolean oracles.
- [`scripts/demo_sparse_reference.py`](https://github.com/MGYamada/Vastitas/blob/main/scripts/demo_sparse_reference.py):
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

Existing CI discovers `test_*.py`; no further workflow or dependency is needed.

### Representation and arithmetic contract

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

### Structural bound and the cancellation regression

For stored position sets `P_A` and `P_B`, the inspector computes

`P_C = {(i,j) | exists k, (i,k) in P_A and (k,j) in P_B}`.

It records every pair of input slots contributing to each output slot, in
increasing `k` order. It never reads values. Under this exact coefficient
model, absent positions are zero and zero annihilates multiplication, giving
`support(AB) subset P_C`. This is the mathematical argument implemented and
tested here, **not a machine-checked Lean theorem**.

`require_structural_bound` allows a candidate superset of `P_C`, and rejects
any missing candidate position even when its current result is zero. By design
there is no interface for caller-supplied cancellation certificates. In
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

### Reuse and invalidation

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

For a transparent tamper regression, execution **recomputes the
symbolic audit** by design and compares the complete output layout and contribution
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

### Information for the shared graph emit (#242)

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
| Missing/stale evidence and denied omissions | Local `S_*` exception codes/reasons | Reconcile with shared diagnostics catalog and statuses; these are reference codes, not a canonical catalog |
| Output/workspace bytes, aliasing, initialization, lifetime | Unknown | Existing Storage/Ownership validation over actual allocations and accesses |
| Allocations, transfers, peak live memory, synchronization, inspect cost and speed | Unknown/unmeasured | Explicit cost model or runtime observations under #242; never fabricated from slot counts |
| Checked acceptance and export coverage | No production acceptance/export | Actual kernel outcome and honest partial/unsupported coverage; no synthetic `verified` status |

### Remaining production boundaries

Checked against main `2d6a86ce4c8a44bd883d879035aa9c924ed8fc71`:

- [`Graph`](../verification/core-models.md#graph-crossings) checks the internal crossing-word fragment.
  Public tensor/source lowering and its bridge to `Indexed.Core.Term` remain
  pending; this reference adds no sparse operation to either Core.
- At that revision, [protocol 8](../storage/resource-programs.md) connects the initial static package
  resource profile to the existing [Storage checker](../storage/checked-storage.md#storage-ir). That
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

<a id="reduction-reference"></a>

## Finite reduction-plan reference

This independent Python reference for [#303](https://github.com/MGYamada/Vastitas/issues/303)
checks a candidate reduction against a **separately supplied target**. It does not
implement a Vastitas acceptance route, a production law provider, Lean proof
checking, native SIMD, real threads, a scheduler or a profiler.

`scripts/reduction_reference.py` owns the checker and arithmetic models;
`reduction_fixtures.py` constructs examples, `test_reduction_reference.py` supplies
regressions, and `demo_reduction_reference.py` prints the finite result ledger.
These scripts use only the Python standard library and are development tools,
not compiler/runtime dependencies. Existing CI discovers the tests.

### Independent target and candidate

The caller supplies a target with ordered input occurrence IDs, each input's
revision and exact value, a selected operation/revision, carrier, coefficient
model, numerical profile and contract. The candidate contains only its target
ID, selected binding, a binary tree and references to the closed law fixtures.
The checker never infers the requested target from the candidate. The caller must
control the target input; two filenames alone do not establish authority.

The checker separately compares:

1. Leaf identity and revision against the actual target occurrences.
2. Multiplicity: each target occurrence appears exactly once.
3. Ordered leaf sequence, independently of bracket shape.
4. Binary bracketing and, when pinned, the complete exact tree.
5. Operation, implementation revision, carrier and coefficient identity.
6. Each numerical-profile field and every submitted evidence reference.
7. Recomputed values against the independently selected reference computation.

Each binary node repeats and must match the selected binding. Leaves cannot
supply payloads. Equal values do not merge occurrences; equal matrix dimensions
do not identify a different carrier or coefficient model. Candidate-owned
contracts, result claims, callables, law tags, checked fields and proof payloads
are not admitted. Evaluation uses the same immutable parsed tree that was audited.
SHA-256 report identifiers record the target/candidate data, not proof authority;
reports cannot be fed back as certificates, and every call recomputes results.

### Law authority and transformation policy

The closed `_LAWS` table is an **explicit reference assumption**, not a Lean
certificate verifier. It contains scoped associativity fixtures for exact
rational 2x2 matrix multiplication and associativity/commutativity fixtures for
rational addition and multiplication. No binary64 associativity fixture exists.
The table cannot be extended by candidate JSON. Every submitted reference,
including unused evidence, must match both its independent catalog record and
the full selected binding. Candidate tags cannot upgrade a law. The matrix v2
fixture has v1's arithmetic but a different revision identity, on purpose.

For an exact reduction, reassociation preserves the leaf order unless the
independent target explicitly permits permutation and matching commutativity
evidence is present. Associativity alone never authorizes permutation. This
conservative reference requires associativity for every non-identical tree,
including permutations; it does not implement every possible local commutation
rule. Matching finite results alone cannot grant transformation permission.

### Contracts and arithmetic profiles

| Contract | Reference and admission | Meaning of success |
| --- | --- | --- |
| `exact` | Ordered seedless left fold; scoped exact laws for changed trees, plus explicit permission and commutativity for permutation | Exact equality for these inputs, under the closed reference law assumptions |
| `fixed_tree` | Target independently pins the full tree and profile; candidate must match both | Repeatable evaluation in this software model; left-fold equality is a separate observation |
| `left_fold_equivalent` | Retain leaf order and compare against the left fold | Equality for this finite input snapshot only; no law or permission for other inputs |
| `relaxed` | Retain explicit policy/error-contract IDs; validate structural fields | Always `unsupported` for a structurally valid candidate, because error/enclosure checking is unimplemented |

`left_fold_equivalent` is an additional finite diagnostic mode, not a fourth
general parallel contract. A fixed tree may succeed even when its left-fold
comparison overflows; that observation is `outside_profile` with no equality
claim. An unsupported relaxed contract never succeeds merely because sample
results happen to agree, and there is no implicit epsilon.

Exact values use `Fraction`; exact matrices are 2x2 over QQ. Scalar QQ addition,
multiplication and subtraction are also available, but subtraction has no law
fixture. Approximate coefficient coercion and machine integer overflow are absent.

The binary64 model accepts finite input bit patterns, computes the exact rational
sum, then rounds using integer arithmetic to nearest, ties to even. It retains
gradual subnormals and signed zero; NaN/infinity inputs and overflowing results
are rejected. FMA is forbidden. Profiles retain representation, precision,
rounding, FMA, subnormal, exceptional-value and signed-zero policies plus backend
identity. The backend here is the software reference, not OpenBLAS or hardware.
All 64 result bits are compared, including signed zero.

This is a **value-only finite numerical profile**, not the full observable-flags
or failure semantics proposed by [#318](https://github.com/MGYamada/Vastitas/issues/318).
It does not implement `monad::float` or claim its monad laws. Observable flags,
traps, NaN policies, branch effects and first-failure traces need their own
admitted semantics. Bind associativity never authorizes arithmetic reassociation.

Reference limits: 1–128 input occurrences, 255 tree nodes, depth 128, rational
input strings of at most 256 characters, and intermediate numerators/denominators
of at most 8192 bits. Exact arithmetic budget exhaustion is `unsupported`.
Empty reductions, seeds, unit laws, DAGs and user-defined operators need separate
contracts. The model never inserts an identity for empty inputs or partial chunks.

### Finite results and regressions

For `A=[[1,1],[0,1]]`, `B=[[1,0],[1,1]]`, `C=[[1,2],[0,1]]`:

- `(AB)C = A(BC) = [[2,5],[1,3]]`: ordered reassociation is admitted.
- `(BA)C = [[1,3],[1,4]]`: associativity-only permutation is rejected.
- Equal-valued identity-matrix samples still cannot supply commutativity evidence.

For binary64 `x=2^54`, `y=-2^54`, `z=1`, the left fold yields
`3ff0000000000000` (1), while the right tree yields `0000000000000000` (0).
The independently pinned right tree succeeds with a false left-fold-equivalence
observation; asking it to satisfy `left_fold_equivalent` yields `VALUE_MISMATCH`.

The 62 regression tests include:

- All 5 binary shapes and 24 permutations of four occurrences: only the five
  ordered matrix plans pass, while all 120 QQ-add plans pass with both laws and
  explicit permission.
- 4096 triples of 2x2 matrices with binary entries, and 5000 seeded binary64
  additions compared with the host Python result.
- Rounding ties, subnormal boundaries, cancellation, signed zero, overflow and
  strict JSON/CLI rejection and exit status handling.
- Missing/duplicate/stale/unknown leaves, equal-valued occurrence substitution,
  self-issued laws, operation/revision/carrier/coefficient/profile substitutions,
  invalid unused evidence, unsupported relaxed claims and resource limits.

These enumerations are finite observations, not general algebraic proofs or
soundness proofs of the Python checker. The host comparison is an additional
finite check; plan evaluation itself does not depend on host Float rounding.

```sh
python3 -m unittest discover -s scripts -p 'test_reduction_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/demo_reduction_reference.py
python3 scripts/demo_reduction_reference.py --write-fixtures /tmp/reduction-fixtures
python3 scripts/reduction_reference.py \
  /tmp/reduction-fixtures/matrix_ordered_reassociation.target.json \
  /tmp/reduction-fixtures/matrix_ordered_reassociation.candidate.json
```

The checker CLI exits with 0 for accepted, 1 for rejected, 2 for unsupported and
3 for malformed CLI input. It rejects duplicate JSON keys and NaN/Infinity.

### Actual implementation and remaining proof obligations

Reviewed main `46580b6bb217af421dc2bd5a82c0b89ace340a6f` includes public numerical
GEMM and [#309](https://github.com/MGYamada/Vastitas/pull/309)'s independent wire
mutation tests. Those tests retain valid surrounding metadata so rejection
reaches the intended semantic boundary. They do not implement reductions.

The [Graph checker](../verification/core-models.md#graph-crossings) audits finite crossing words, scoped law
authority and exact returned graphs; it has no reduction reassociation rule and
its production law provider/Indexed.Core bridge remain pending.
[StorageNumerical](../linalg/maps-and-gemm.md) connects nominal products and live loans
to the actual emitted resource GEMM. Its structural certificates do not prove
Float laws or accuracy. The [native adapter](../internals/numerical-backend.md#native-gemm-adapter)'s `NativeFast`
policy permits backend FMA/blocking/reduction order and cannot supply this
reference's pinned-tree guarantee.

Before admitting a production reduction transformation:

1. Prove the actual selected operation's algebraic laws, domain/closure and exact
   realization. Prove ordered reassociation from associativity and permutation
   from the required commutativity. Empty/seeded folds need explicit extra laws.
2. Reconstruct the target from the actual accepted source/environment/Core,
   independently of the proposal. Connect every input occurrence, selected
   method and revision-bound evidence to that same returned Core. Pure,
   pre-evaluated reference values do not justify reordering effectful expressions.
3. Prove soundness of the actual checker using its implementation definitions;
   the closed Python law table, candidate tags and report hashes are not authority.
4. Preserve exact tree/occurrences/operations/profiles through lowering and
   native execution. Keep source-to-Core and Core-to-native refinement distinct.
   Add source and forged/direct-IR regressions through that real entry point.
5. Prove the selected numerical implementation/refinement, including rounding,
   FMA, subnormals, signed zero and observable exceptional/effect behavior.
   General left-fold equivalence and validated relaxed error bounds require
   separate proofs; a single matching sample is insufficient.
6. Establish the remaining #303 access, ownership, noninterference, completion
   and scheduling obligations when actual parallel execution is introduced.

This reference completes none of those general Lean/Core/native obligations,
adds no Domain Checker or constitutional theorem, and does not close #303.

<a id="float-reference"></a>

## Float / SafeFloat executable reference

This is a bounded Python reference for [#318](https://github.com/MGYamada/Vastitas/issues/318),
following its current Slice A and the pure-reference/execution split in
[#322](https://github.com/MGYamada/Vastitas/issues/322). It does not complete either
issue or install public `std::float` / `monad::float` packages. The mathematical
contracts in [#310](https://github.com/MGYamada/Vastitas/issues/310) and
[#313](https://github.com/MGYamada/Vastitas/issues/313) are unchanged.

Run from the repository root with Python's standard library only:

```sh
python3 scripts/demo_float_reference.py
python3 -m unittest discover -s scripts -p 'test_*float_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The existing CI unittest discovery includes both test files; no compiler,
Lean, BLAS or third-party Python dependency is needed for these reference tests.

### Two layers, one primitive definition

| File | Responsibility |
| --- | --- |
| [float_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/float_reference.py) | Integer bit carrier, finite rational decoding, explicit rational conversion, add/sub/mul/raw division, and operation-local symbolic flags. Imports no execution layer. |
| [safe_float_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/safe_float_reference.py) | Dedicated `Float` / `SafeFloat`, immutable Unit configuration, `pure`, `bind`, canonical lift, checked division, lazy branching, and internal audit events. Reuses the same reference primitives. |
| [test_float_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_float_reference.py) | Representation and arithmetic checks independent of sequencing laws. |
| [test_safe_float_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_safe_float_reference.py) | Separate unit/associativity, flag monoid, morphism, equality, failure, and operational-trace tests. |

There is no general Reader/Writer/Except/State or transformer API. `Ok` and `Err`
are ordinary tagged reference Result values, not a production exception
runtime. Python callbacks/closures express test programs; they do not change
Vastitas's capture/ownership rules. The laws admit deterministic, effect-closed
callbacks only. Python does not establish this admissibility for arbitrary code;
Python exceptions propagate as model/programming errors, not `DivisionByZero`.

### Fixed binary64 profile

The pure profile is `binary64-rne-gradual-tiny-after-first-nan-v1`:

- Binary64 only, `roundTiesToEven`, no excess precision or FMA contraction.
- Gradual underflow, no DAZ input conversion and no FTZ output conversion.
- Underflow is flagged for an inexact result that is tiny **after rounding**.
  An exactly represented subnormal does not raise underflow. A value that rounds
  up to the smallest normal raises inexact, but not underflow in this profile.
- Arithmetic selects the first NaN operand, left before right, preserves its
  sign/payload and quiets it. Any signaling operand adds `INVALID`, even if a
  different NaN is selected. Invalid arithmetic without a NaN operand produces
  `0x7ff8000000000000`. This is a named deterministic choice, not a claim that all
  hardware or all IEEE implementations choose the same NaN.
- `F64(bits)` and monadic `pure` preserve every admitted bit, including signaling
  NaNs, without quieting, rounding, or emitting flags. Arithmetic/conversion are
  explicit operations. Finite decoding returns an exact `Fraction`; NaN and
  infinity have no RR/rational denotation.
- Conversion accepts explicit `Fraction` inputs, not arbitrary RR, Python
  floats, implicit casts or real-number proof objects. The pure conversion also
  permits an explicit negative sign for exact zero; rational zero alone is +0.

Rounding computes an exact rational significand, integer quotient/remainder,
and tie parity. The pure primitives use no host floating arithmetic or floating
environment APIs. `Flags` are five **symbolic bits** derived from those rules:
invalid, divide-by-zero, overflow, underflow, inexact. They are not measurements
of CPU/GPU flags. Arithmetic rules have executable and regression status only;
there is no claim of full IEEE conformance or a proved rounding implementation.

The execution profile appends `/left-to-right-short-circuit-v1`. `Config` is
immutable Unit: there are no dynamic choices within this profile. Directed
rounding, alternate NaN profiles, binary32, complex arithmetic, arrays, mutable
rounding state, flag inspection/clearing, traps, and native execution are outside
this increment. Unsupported primitive names/configurations are rejected.

### Denotation and equality

```text
Float<A>     = Unit -> (A, Flags)
SafeFloat<A> = Unit -> (Result<A, DivisionByZero>, Flags)
```

`run` returns exactly these pairs. Raw `bind` evaluates the first computation,
then its continuation with the same configuration, and unions their flags.
Safe `bind` stops on `Err`, retaining all accumulated flags. `pure` adds no flags.
`lift` wraps the raw value in `Ok`, preserving flags; lifting a raw Result yields
`Ok(Err(...))`, not a short-circuiting error. Raw `Float<Result<...>>` bind and
dedicated `SafeFloat` bind are therefore tested as distinct operations.

`same_observation` compares Result tags/error identities, accumulated flag masks,
and `representation_key` of successful values. The bounded equality carrier is
`F64`, bool, int, None, tuples and nested Results. F64 identity compares integer
bits; it is reflexive on NaNs and distinguishes signs/payloads/signaling bits.
It distinguishes +0 from -0, which raw `1/x` can distinguish. Native Python float
values are rejected by this comparator, rather than falling back to numeric
`==`. Equality of computations is pointwise equality at every admitted config;
there is only one config here. No general equality decision for callbacks exists.

The tests independently check left unit, right unit and associativity for both
monads, and both lift equations. They exhaust all continuations on a two-value
carrier and four masks `{empty, underflow, inexact, underflow|inexact}`: 32,768
raw and 248,832 safe associativity cases, including failure at each step. The
five-flag monoid is separately checked on all 32 masks (all 32³ triples). Lift
bind tests cover all 32² mask pairs with ten special-bit values. Additional law
tests use the actual arithmetic/checked primitives, including NaNs and ±0.
These are finite regressions, not universal Lean proofs. Bind associativity does
not permit reassociation of arithmetic: a separate negative test demonstrates
different binary64 results for the two additions around `2^53`, `1`, and `-2^53`.

### Division, ordering and failure

| Input | Raw reference division | Checked division |
| --- | --- | --- |
| finite nonzero / ±0 | Signed infinity, `DIVIDE_BY_ZERO` | `Err(DivisionByZero)`, no local IEEE flag |
| 0 / ±0 | Default quiet NaN, `INVALID` | Same typed error, no local IEEE flag |
| infinity / ±0 | Signed infinity, no flag | Same typed error, no local IEEE flag |
| NaN denominator | Selected quiet NaN, signaling policy applies | Guard passes; same raw result/flags |

Mathematical totalized division remains `a/0 = 0` in the selected exact Field;
this reference neither implements nor changes that mathematical model. It does
not extend #310's exact-Field guard to bare meadows. No field law is granted to
F64. `checked_div` guards the evaluated, operation-effective represented divisor.
With this fixed no-DAZ profile that is exactly the two signed-zero bit patterns.
A guard failure runs no raw division, including when the numerator is signaling
NaN. Success does not promise a finite result or exact mathematical nonzero.

`divide(left, right)` explicitly runs the left operand, then the right operand,
then the guard. Failure in the left operand skips the right operand and guard;
prior effects from both successful operands survive a later guard failure.
`choose` uses a represented Boolean and branch thunks, so an unselected branch
is neither constructed nor executed. No exact mathematical branch refinement is
inferred. Failed conditions skip both branches. Tests also retain failures in
`0 * checked_div(1, 0)`, self-division at zero, and nested checked division.

Boundary witnesses include:

- Exact `2^-1075 != 0` converts to +0, with underflow/inexact; checked division
  then fails and retains those flags. Exact nonzero evidence cannot remove this
  represented guard.
- Exact `1/10 + 1/5 - 3/10 = 0`, but the separately converted/evaluated denominator
  is `0x3c90000000000000` (`2^-54`); checked division succeeds. That success is
  not evidence for the ideal domain. No enclosure or ideal-domain certificate
  is fabricated.
- A representably nonzero approximation to `10^-200` passes a primal guard but
  its rounded square is zero. Guard evidence does not transfer to an AD divisor.
- `fl(49 * fl(1/49)) != 1` in the profile, although 49 passes the floating guard.
  The exact meadow unit equation is not the floating zero test.

### Internal trace is a separate check

`audit` returns an immutable internal trace from the **same evaluator** used by
`run`. Events contain site, operation and local flags; `pure`/`bind`/`lift` add no
events, and bind concatenates executed events in order. No second interpreter
or mutable side-channel trace drives the semantics. The trace is projected out
of the minimal observation and is not available to admitted continuations.

Two programs that first fail at sites A and B can both return
`(Err(DivisionByZero), emptyFlags)`. The regression explicitly establishes their
equal minimal observations and **different** internal traces. Consecutive checked
zero divisions record only the first executed guard. Associative bind bracketings
retain the same first failure and prior trace. Reordering underflow across a
failure changes retained flags and is detectable even without a trace.

Repeated raw zero division executes twice but sets just one sticky flag bit;
repeated underflow similarly leaves one bit while the trace has two occurrences.
Subtracting the earlier flags from the later ones cannot recover such repetitions. These diagnostic
trace checks are not extra failing-site identity in #310's public error or a
proof that a future optimized backend must preserve an unobserved site. A future
site-observing profile requires its own explicit trace-refinement theorem.

### Evidence and remaining obligations

| Layer | Status of this increment |
| --- | --- |
| Executable reference | Implemented and regression-tested Python primitive and sequencing layers; fixed binary64 real profile only. |
| Lean monad/lift proofs | **Not implemented.** Prove flag-union laws, both unit laws and associativity by failure cases, and both lift equations extensionally at representation equality. Establish equality congruence for admitted continuations and the trace projection separately. |
| Lean arithmetic proofs | **Not implemented.** Prove finite decoding/rounding and each operation's result/flag contract under the selected NaN, underflow and rounding policy; monad laws alone cannot prove these. |
| Production Source/Core connection | **Not implemented.** Preserve operation identities, computational presentation, model/profile/revision provenance, accepted Core, branch schedule and guard evidence. No parser/protocol/checker/stdlib admission change here. |
| Native refinement | **Not implemented or tested.** No CPU/GPU flags, fenv restoration, ABI, compiler optimization, BLAS/CUDA or native/reference conformance claim. |
| Mathematical accuracy/certification | **Not implemented.** Selected ideal RR/CC specifications, error/enclosure proofs and ideal nonzero evidence remain distinct obligations under #244/#313. |

Future native work must compare represented results, retained flags, typed
failures and branch/short-circuit observations against this selected reference,
declare environment isolation/restoration and DAZ/FTZ/FMA policies, and separately
prove refinement. Differential execution is useful evidence, not a substitute
for that proof. The same applies to any promised first-failure-site trace.

No acceptance checkbox in #318/#322, constitutional theorem, public Monad
instance, or mathematical contract is marked complete by this reference.

<a id="incremental-reference"></a>

## Dependency invalidation reference

This is executable preparation for [#339](https://github.com/MGYamada/Vastitas/issues/339),
not its production implementation or completion. It defines a small finite source
model, a conservative invalidation planner, untrusted cache candidates and
clean/incremental differential regressions. It changes no Rust or Lean acceptance
path and does not implement the [#152](https://github.com/MGYamada/Vastitas/issues/152)
Lean-native migration.

Run from the repository root, with Python 3.10+ and the standard library only:

```sh
python3 scripts/demo_incremental_reference.py
python3 -m unittest discover -s scripts -p 'test_incremental_reference.py' -v
```

The existing CI discovery command `python3 -m unittest discover -s scripts -p
'test_*.py'` includes the regressions. No further compiler dependency or workflow is
needed. The [implementation](https://github.com/MGYamada/Vastitas/blob/main/scripts/incremental_reference.py),
[tests](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_incremental_reference.py) and
[demo](https://github.com/MGYamada/Vastitas/blob/main/scripts/demo_incremental_reference.py) are independent of compiler APIs.

### Finite semantic model

Inputs are Python dataclass ASTs, not `.vast` source or a public wire protocol.
The caller constructs the finite, JSON-representable input profile. This is not
a hostile-source parser or a Python object security boundary.

- A package has a **nominal source identity**, separate display name/version,
  manifest revision and explicit package dependencies. All modules in the root
  packages' dependency closure are audited, including unused modules and methods.
  Disconnected packages are outside this build. Package identities are supplied
  fixture identities; the model does not authenticate files or resolve paths.
- Modules have a nominal `(package identity, logical path)` identity, imports,
  a scalar public interface, a literal body, interface uses, families, methods
  and calls. Literal typing distinguishes `Int` from `Bool`; a type mismatch is a
  real rejection of this tiny language, not an input `valid` flag. Interface uses
  check the current target's signature. Imports provide transitive visibility in
  this model; full Vastitas visibility/reexport rules are not implemented here.
- The synthetic dispatch profile has the nominal selectors `Any`, `Linear` and
  `Scalar`, and four feasible keys (`Linear`/`Scalar`, with/without `HasMetric`).
  The nominal/capability **product order**, not equality of observed key sets,
  determines specificity. These are fixtures from the design proposal, not
  production scalar selectors or metric witnesses.
- A family is identified by its exact declaring module and name. Owner methods
  are active; an assembly explicitly selects external contributions. Every body,
  including losing, unused and unapplied method bodies, is checked. Completion
  checks duplicate signatures and ambiguity over the **whole** finite key space,
  coverage over the declared domain and external methods' final winning footprints
  against grants from the exact owner to the exact contributing module.
- An assembly has explicit applied method identities, grants and a revision.
  The reference models the final authorized family, not the production exclusive
  loan/return/seal trace, reborrowing or permanent authority transfer. A grant alone
  does not apply a contribution. Current source reconstructs identities and grants;
  cache metadata cannot assert an owner or grant.

Package/import cycles, missing dependencies/imports, duplicate identities and
unsupported finite keys/signatures reject with deterministic diagnostics. This
small model rejects cycles rather than claiming support for recursive modules.

`Run.observation` contains build acceptance, sorted normalized diagnostics and
the ordered module structures: exact module identities, interfaces, typed literal
bodies, imports/uses, method bodies, all-key dispatch tables and selected call
targets/results. Rejection observations also retain these structures where the
input graph permits checking. Cache traces, timing and compiler version strings
are not semantic observations. This is a model observation, **not actual checked
Vastitas Core or native behavior**.

### Invalidation and reuse

| Change | Candidate invalidation |
| --- | --- |
| Unchanged current inputs | Try every existing candidate; recheck every one |
| Module literal body, public interface, uses or calls | Changed module and transitive importing consumers |
| Import change | Reverse dependency closure using the union of old and current import edges |
| Family/method addition, removal, signature or body change | Entire selected package/dependency/assembly closure |
| Owner grant, applied contribution or assembly revision | Entire selected closure |
| Compiler version, package identity, manifest or package dependency change | Entire selected closure |
| Module addition, removal or logical identity change | Entire selected closure |
| Missing/malformed cache snapshot | Entire selected closure |
| Missing entry or stale/corrupt/forged candidate, context or receipt | Recompute the affected candidate after current-input checking |

The broad fallback includes, by design, modules with no direct import of a
contributor: a selected assembly can alter a generic used by an unchanged consumer.
It also invalidates unrelated modules **inside** the selected closure when the
model cannot justify narrower reuse. Ordinary body/interface changes can retain
unrelated candidates. Transitive imported results in each context independently
guard against incomplete invalidation plans.

The snapshot is only a planning hint. A cache record contains a candidate, its
context and an `evidence` receipt with context/candidate hashes. The receipt is
explicitly `finite-recheck-required`; it is **not a proof, signature or verified
flag**. Matching source hashes, matching context hashes and recomputed receipt
hashes cannot authorize reuse by themselves.

Every invocation reconstructs the current package graph and entire family
environment. For every module, including warm hits, `_check_unit` rederives its
complete finite semantic result from current source, current family environment
and already rechecked imports, without receiving cache data. Only then may a
candidate whose full typed JSON structure matches that result and its current
context be reused. Otherwise the result is recomputed/replaced safely. Typed JSON
comparison prevents Python's `True == 1` or `False == 0` from accepting a forged
literal or acceptance field. Malformed outer cache data is discarded; no pickle
or other executable deserialization is used.

This intentionally conservative checker shares the finite semantic functions with
the clean reference. It tests cache transparency and invalidation against that
model; it is not an independently proved implementation of Vastitas semantics.
Explicit expected outcomes (targets, ambiguity, grant violations, body errors) and
an independent reachability computation supplement clean/incremental comparison.

`trace.reused` counts **candidate reuse after full rechecking**; `trace.checked`
lists every module rechecked. These counts do not measure skipped checker work or
establish a speedup. The cache is an in-memory, JSON-roundtrippable return value.
Builds do not mutate their supplied prior cache, and the records that a build adds retain rejection
as rejection. There are no persistent writes or published native outputs here.

### Regression coverage and expected demo

The demo follows cold/warm builds, a changed winner, an ambiguous family, its repair
and an unrelated body edit. For `f(Linear, {})` and `f(Any, {HasMetric})`, the
`Linear`+`HasMetric` key has two undominated methods; adding
`f(Linear, {HasMetric})` resolves that ambiguity. The consumer's source does not
change. All six demo steps compare complete observations with a clean build.

Tests also cover winner changes without ambiguity, method removal, selected-body
changes, interface/import rewiring, transitive and unused inputs, external
contributions outside a consumer's imports, grant revocation/narrowing/wrong
issuer/wrong grantee, assembly revisions, module deletion, distinct origins with
equal package names/versions, stale compiler versions and manifest/dependency
changes. Rejected builds can be repaired and reused across edit/revert histories.

Cache mutations include partial entries, malformed snapshots, foreign identities,
false rejection, forged success, altered targets, invalid evidence and **fully
rehashed** forgeries with current context/snapshot metadata. No cache success flag
can conceal a current rejection. There are also all-pairs histories for nine
program variants and all 64 forward-edge DAGs on four labeled modules, each with
four possible edit locations and two body edits (512 graph/edit comparisons).
The graph test independently computes reachability by transitive matrix closure
and asserts the exact invalidated/reused sets.

### Port boundary and remaining work

A Lean port can preserve the separation between immutable nominal inputs, current
environment reconstruction, conservative planning, candidate/receipt data,
current-context validation and observation/trace output. In particular, retain
the all-key family audit and all-body audit when introducing finer queries.

The following are **not implemented or demonstrated** by this reference:

- A persistent Lean-native `.vast` cache or compiler integration; parsing,
  actual scoped declarations/Core, generative endpoints and resource ownership.
- Lean-kernel rechecking of evidence, proof-object replay, or a theorem of cache
  transparency. Hash receipts cannot replace those obligations.
- Source file canonicalization, symlinks/hardlinks, production size limits,
  serialized-source validation, concurrent writers, interrupted/atomic writes,
  locking, cancellation or output collision protection.
- Native cache layers keyed by backend/target/ABI/options, executable parity,
  no-Rust production CI, or cold/warm/local-edit performance evidence.

The current [Stage 1b memoization](../stage1b.md) remains within a compilation;
[edit-assembly checking](../language/edit-authority.md) retains its existing whole-closure
validation. The dispatch design motivates the
finite fixtures without changing production semantics. #339 and #152 remain open
implementation and release obligations.
