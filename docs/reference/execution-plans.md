# Execution and planning reference models

These independent finite models exercise planning questions that the compiler does not implement: reuse of GPU storage, sparse patterns, reduction trees, incremental invalidation, and the split between `Float` and `SafeFloat`. Each has its own hypotheses, verifier and regression examples.

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
recording frontier, event generation, stream/context epochs and actually enqueued
wait chain. This reference deliberately does not repeat that verification. It
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
new generation. There is no numeric reassociation or operation rewriting here.

### Reproduced experiments and cost interpretation

The independent five-node permutation test reproduces the original counts:
one-sided join has **4** valid orders, **2** releasing before `use_2`; joining both
uses leaves **2** orders, both safe in that model. An extended closed six-node
fixture additionally checks all 8 subsets of the two joins and reuse edge against
all `6!` permutations. Only the fully joined, ordered-reuse case is admitted.

For two independent 64-byte workspaces with hypothetical operation durations 3
and 5:

| Candidate | Peak live slot bytes | Hypothetical makespan | Newly ordered work pair |
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
| Candidate costs | Max-of-stage-byte-sums expression AST (constant leaves in this fragment), estimated time, newly ordered work pairs, added edges, assumptions, unknown overhead/pool reservation |
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
performance obligation, new Domain Checker, constitutional theorem, release
milestone, or new public acceptance route.

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

Existing CI discovers `test_*.py`; no new workflow or dependency is needed.

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
| Missing/stale evidence and denied omissions | Local `S_*` exception codes/reasons | Reconcile with shared diagnostics catalog and statuses; these are reference codes, not a new canonical catalog |
| Output/workspace bytes, aliasing, initialization, lifetime | Unknown | Existing Storage/Ownership validation over actual allocations and accesses |
| Allocations, transfers, peak live memory, synchronization, inspect cost and speed | Unknown/unmeasured | Explicit cost model or runtime observations under #242; never fabricated from slot counts |
| Checked acceptance and export coverage | No production acceptance/export | Actual kernel outcome and honest partial/unsupported coverage; no synthetic `verified` status |

### Remaining production boundaries

Checked against main `2d6a86ce4c8a44bd883d879035aa9c924ed8fc71`:

- [`Graph`](../verification/core-models.md#graph-crossings) checks the internal crossing-word fragment.
  Public tensor/source lowering and its bridge to `Indexed.Core.Term` remain
  pending; this reference adds no sparse operation to either Core.
- [Protocol 8](../storage/resource-programs.md) now connects the initial static package
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
actually control the target input; two filenames alone do not establish authority.

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
fixture deliberately has v1's arithmetic but a different revision identity.

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
