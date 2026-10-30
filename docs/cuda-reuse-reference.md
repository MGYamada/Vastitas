# Finite CUDA reuse planning reference (#266)

This standard-library-only Python experiment computes maximal-use frontiers,
audits release/reuse order, and compares two explicit schedules for
[#266](https://github.com/MGYamada/Vastitas/issues/266). It **assumes the cleanup
contract of [#210](https://github.com/MGYamada/Vastitas/issues/210)**; it does not
reimplement its keeper, ticket, cancellation, event-recording, physical-free or
acknowledgement state machine. No CUDA calls, compiler changes, Lean proofs or
package-registration requirements are added.

The implementation baseline is main
`2d6a86ce4c8a44bd883d879035aa9c924ed8fc71`. That revision has the initial static
[protocol-8 resource composition](resource-source.md) and the internal
[Graph crossing checker](graph-crossings.md). This Python model is connected to
neither. Its names are fixture identifiers, not accepted Core identifiers.

## Run

Python 3.10 or later; no third-party dependencies or GPU are needed.

```sh
python3 -m unittest discover -s scripts -p 'test_cuda_reuse_reference.py' -v
python3 scripts/demo_cuda_reuse_reference.py
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
```

- [Reference](../scripts/cuda_reuse_reference.py): immutable input records,
  frontier analysis, independent order audit, optional cost analysis and fallback.
- [Demo](../scripts/demo_cuda_reuse_reference.py): explicit hypothetical cleanup
  snapshots and JSON reports; prints to stdout and does not alter source files.
- [Tests](../scripts/test_cuda_reuse_reference.py): negative coverage/identity/order
  cases and an independent permutation oracle. Existing Python test discovery
  finds them; no workflow or release gate is added.

## Input and authority boundary

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

## Frontier and independent audit

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
[#183 storage obligations](storage-ownership.md), separately preserved by #210.
In particular, reuse does **not** inherit old contents as initialized data in a
new generation. There is no numeric reassociation or operation rewriting here.

## Reproduced experiments and cost interpretation

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

## Proposed handoff to common graph emit (#242)

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

## Optional optimization and conservative fallback

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
