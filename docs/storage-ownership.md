# Storage, ownership and residual retention — revised Chapter 7

Status: accepted design direction, 2026-10-29; public implementation and performance
evidence remain pending under [#183](https://github.com/MGYamada/Vastitas/issues/183)
and the [Stage 1 completion gate](stage1-completion.md).
This is the current design contract replacing the storage discussion in
[historical Chapter 7](design/tensor-resources-units.md#7-ownership-and-tensor-network-ports).
The archived v0.3 text and its source hashes remain unchanged.
The notation below describes required IR behavior, not available surface syntax.

The [dense layout/preflight reference](storage-layout-preflight.md) supplies an
executable integer model, regression cases and proposed Lean obligations for
the first dense/transpose fragment. It is not production resource acceptance,
completed Lean soundness, native check elimination or performance evidence.

The [finite CUDA reuse planning reference](cuda-reuse-reference.md) explores
last-use frontiers and memory/parallelism tradeoffs under #210's existing async
cleanup contract. Its optional Python analysis is not connected to accepted Core
or a CUDA adapter and does not establish GPU safety or performance.

The [internal resource IR](storage-ir.md) now supplies independently checked
logical transitions, canonical layouts, initialization and branch joins, with
actual-checker byte-region and active-loan theorems. Its component schema is not
public protocol 8. Its optional native runtime and
[internal resource functions](storage-functions.md) exercise allocation, calls,
destination reuse and failure cleanup. [Protocol 8](resource-source.md) now connects the initial static resource profile
to package source and pure return blocks. Dynamic shapes/value flow, numerical
consumers and performance comparisons remain pending.

## 7.1 Fast like C: the primary design goal

**Fast like C is Vastitas's highest-priority performance and architecture goal.**
Mathematical abstraction must admit native code with the storage access, allocation
behavior and kernel calls of a competent C implementation of the same computation.
Performance is a design constraint from the representation boundary onward, not
an optimization project postponed until after the public interfaces are fixed.

Correctness, declared mathematical meaning and explicit numerical policy constrain
the comparison. A faster program that drops an ownership check, changes arbitrary
precision integers into machine integers, or silently changes floating-point
semantics does not meet the goal. When a safe design is too expensive, change its
representation or API and measure again; do not certify a different computation.

Every numerical operation must expose a cost contract: reads, writes, allocation,
copy/packing, retained bytes, synchronization and data-dependent validation.
Static identity, type, dispatch and authority evidence should disappear from the
hot loop once its obligations have been discharged. Required dynamic dimensions,
bounds and lifetime information remain until their last justified use.

The goal does not assert current C-level performance. Stage 1 must record actual
C comparisons and unresolved gaps; AD-specific comparisons follow with AD.
Compiler latency and generated-program runtime are separate measurements.

## 7.2 Four distinct identities and rights

| Layer | Identity and right | Does not imply |
| --- | --- | --- |
| Mathematical object/value | Nominal object, base, basis, scalar and logical version | A particular layout or writable memory |
| Physical allocation | Fresh allocation identity, extent, allocator and live lifetime | Equality of mathematical endpoints |
| Storage access | Region, initialized cells and read/write loan | Function-edit authority or graph wiring rights |
| Network occurrence | Fresh occurrence and linear port identities | A fresh allocation or disjoint tensor factors |

Function-edit ownership remains the independent protocol-6 discipline in
[edit authority](edit-authority.md). Borrowing a function does not borrow its data.
Creating two occurrences of one immutable tensor creates new ports, not copies.
The runtime may share immutable descriptors; copying a descriptor does not grant
mutable authority. A numerical logical value may reuse storage only after all
dependencies on its previous contents have ended or been explicitly retained.

## 7.3 Allocation and layout records

An owned allocation records a fresh identity, live generation, element
representation, byte capacity, required alignment, allocator/deallocator pair,
device/address space and initialization map. Reused addresses receive a fresh
identity; pointer equality is not sufficient allocation provenance.

A view retains that allocation identity and a checked layout descriptor:
byte offset, rank, extents, byte strides, element width, access mode and region.
For indices `0 <= i[k] < extent[k]`, the accessed byte interval begins at
`offset + sum(i[k] * stride[k])` and has the element representation's width.
The checker reasons with mathematical integers; machine lowering must establish
that every size, multiplication, addition and pointer conversion is representable.

The initial resource profile admits finite rank, positive-width scalar elements
and nonnegative strides. Negative strides, packed bits and foreign device memory
require separately specified extensions; they must be rejected if unsupported.
Read-only broadcast with zero strides may be represented explicitly. A writable
view must be injective over nonempty logical indices, with nonoverlapping element
byte intervals. A zero stride on an axis of extent greater than one fails this.

The accessible intervals must lie within capacity and satisfy element alignment.
If any extent is zero, the view has no accessible element; no element pointer
may be dereferenced. Validate its metadata without evaluating `extent - 1` in an
unsigned machine type or manufacturing an out-of-bounds pointer for an empty view.
Capacity, padding and initialized logical cells are distinct; padding is not read.

An initial dense matrix uses column-major storage with explicit leading dimension.
For a nonempty `m x n` matrix, `ld >= max(1,m)` and capacity covers its last
element, including column padding. LP64 narrowing is checked before BLAS entry.
Complex storage and alignment are fixed by the adapter ABI, not inferred from
the source spelling `Complex<F64>` or an unchecked host struct cast.

## 7.4 Regions, overlap and alias evidence

A region describes actual accessible byte intervals in one allocation.
Different live allocations are disjoint. Within one allocation, independently
checked layout/partition evidence may establish disjoint regions. Equal shapes,
different variable names, tensor factors and distinct mathematical bases do not.

The initial finite checker accepts contiguous intervals and explicit partitions
whose extents, offsets and coverage it can reconstruct. Strided access may use a
conservative enclosing interval; if that interval overlaps another access, reject
the conflicting loans unless a supported stronger partition proves disjointness.
Do not enumerate every tensor element to resolve aliasing in a hot-path check.

Unknown overlap is treated as overlap for mutable access. No implicit defensive
copy repairs it. The caller can request a copy/packing operation, supply a valid
partition, or choose a schedule with nonoverlapping loan lifetimes.
Read/read overlap is permitted. Write/read and write/write overlap are forbidden
for simultaneously active incompatible accesses, including aliases through views.

Backend alias attributes such as C `restrict` require a translation argument for
their entire access scope. Pairwise checks at one instruction do not authorize
stronger alias promises for a surrounding function. If the argument is absent,
omit the attribute; never obtain speed through an invalid native alias contract.

## 7.5 Affine ownership and explicit transitions

The resource environment tracks each owned handle, live loan and region state.
The following operations must be represented and independently checked:

| Operation | Required state | Result |
| --- | --- | --- |
| Allocate | Checked size/alignment and successful allocation | One live owner; uninitialized region |
| Move | Live owner; no outstanding loan under the initial profile | New owner binding; old binding unusable |
| Read loan | Live storage; requested cells initialized; no overlapping writer | Shared read access for a bounded scope |
| Write loan | Live owner; no overlapping active access | Exclusive access, with explicit write-only or read/write mode |
| Return loan | Matching live loan and all children returned | Access ends; initialization/changes propagate to owner |
| Drop | Live owner and no loans or retained dependencies | Exactly one release by the matching allocator |

An exclusive parent may be split or reborrowed only with an explicit child region
inside the parent and checked sibling compatibility. Suspend the parent's access
while a child is active; return children inside out. Shared children do not permit
their exclusive parent to write. This is storage authority, separate from edit
delegation; the two mechanisms must not share tokens merely because names match.

Loans cannot escape through function results, packages, retained descriptors or
other data unless the result's explicit lifetime contract and caller audit permit
it. The initial profile rejects such escape rather than inventing a lifetime.
An owned result transfers its owner explicitly. Last use may shorten a loan only
when the checked resource schedule records that shortening.

## 7.6 Initialization, branches and failure

Initialization is tracked by region, not one optimistic flag on an allocation.
A write-only loan may cover uninitialized storage; any read requires initialized
cells. A partial write initializes only its checked write set. Moving an owner
preserves that state. Reading padding or an unwritten part of a view is invalid.

At a branch join, ownership and outstanding loans must agree after explicit
normalization: a handle moved in one branch is not silently live after the join.
The guaranteed initialized region is the intersection of the branch guarantees.
Different fresh branch results need an explicit owner result binding; no equality
of allocation IDs or nominal mathematical identities is inferred from equal sizes.
Every admitted exit path must release or return its resources exactly once.

Before the first external write, validate shapes, nominal endpoints, layouts,
aliasing, initialization, arithmetic narrowing and backend support, and complete
any required scratch allocation. A failure in this preflight preserves output.
This is not a transaction guarantee for a native crash, cancellation during a
kernel, hardware failure or a backend that violates its contract.

A fallible operation that has started writing must expose its partial state or
invalidate the affected output; it cannot return an initialized success value.
Operations requiring all-or-nothing publication use explicit staging storage and
commit, with that extra storage and copy charged to their cost contract.

## 7.7 Views, transpose, conjugation and packing

A view changes metadata and access rights while retaining allocation provenance.
A transpose permutes extents/strides and mathematical axes; it normally allocates
no buffer. An adjoint additionally conjugates complex elements. A logical
conjugated read view is not a writable raw pointer with identical semantics.

The lowerer may use a supported BLAS transpose/conjugate-transpose flag after
checking its descriptor contract. An unsupported layout needs an explicit pack
step with axis order, destination layout, byte count and lifetime in the plan.
High-rank contraction records both axis grouping and permutation before GEMM.
A reshape is a view only when the byte mapping and mathematical index contract
justify it; otherwise its materialization is explicit.

No high-level operation silently introduces copy-on-write, reference-count traffic
per element, layout conversion or a temporary proportional to the input size.
A declared allocating operation is allowed, but allocation must be visible in the
checked plan. Multiple references to immutable data do not demand element copies.
Do not erase view provenance merely because the native operation accepts pointers.

## 7.8 Destination passing, scratch and local mutation

Support caller-provided destinations and reusable scratch with explicit ownership.
A numerical kernel's normal fast path should perform no heap allocation after
successful preflight when its caller supplied compatible output and workspace.
Stack allocation, scalar replacement and fusion are representation choices only
when lifetime, initialization, alias and semantic obligations remain valid.

Scratch has size/alignment requirements and an explicit lifetime ending before
reuse. Pooling must retain allocator provenance and establish that all loans and
residual dependencies ended. Uninitialized scratch is not a source operand.
Loop-invariant layout/alias checks should be hoisted to the enclosing checked
operation, not repeated for every scalar element.

Local mutation may realize a pure logical operation when no observer or future
residual requires the old value. A storage-safety theorem alone does not prove
this refinement. Keep explicit resource transitions distinct from the existing
pure Core; prove the connection to logical evaluation for each supported lowering.
The initial schedule is deterministic; optimization search is not a prerequisite.

## 7.9 The first GEMM contract

Stage 1 uses `F64` and `Complex<F64>`, column-major LP64, synchronous CPU and
explicit `NativeFast`, with pinned OpenBLAS 0.3.34 behind a thin C adapter.
The common preflight validates scalar representation, endpoints/bases, dimensions,
transpose/adjoint flags, leading dimensions, capacities and loan compatibility.
Output cannot overlap either input. Read-only inputs may share storage only if
the exact adapter/backend contract permits it. No implicit alias-repair copy exists.

`overwrite` is logically `C := A * B` and must never read old `C`; it accepts
uninitialized output. `accumulate` is `C := C + A * B` and requires initialized
output. Their checked IR read/write sets differ even if one backend call shape
uses an equivalent coefficient. Trust and test the native adapter's write-only
behavior; a mathematical zero multiplier alone does not establish it.

For empty output (`m = 0` or `n = 0`), perform no element access. For nonempty
output and `k = 0`, overwrite must initialize output to zero and accumulate
must preserve it, while still enforcing accumulate's initialization contract.
Specify these cases in the adapter instead of relying on undocumented no-op
behavior. Test dimension/stride overflow before any narrowing or output write.

Check nonfinite/rounding behavior against the declared `NativeFast` policy;
resource validity does not certify a real-number identity or bitwise portability.
Numerical CI uses one backend thread. Non-numerical programs and the ordinary
compiler remain usable without linking or installing OpenBLAS.

## 7.10 Reverse residual retention and mutation

Residual retention is a forward-compatible design obligation; AD is outside
Stage 1. Here a residual means saved data for later pullback execution, not a
solver's numerical error estimate. Exclusive writing rights alone cannot prove
that overwriting a primal is safe for a future backward computation.

A residual records required logical value versions, allocation identities and
regions, rule/function revisions, basepoints and numerical/evidence dependencies.
Views retain the same dependencies. A saved pointer without a live dependency
does not retain a value. Validity is checked before use, not inferred from a name.

Each required value must have one explicit retention strategy:

| Strategy | Permission and cost |
| --- | --- |
| Retain | Keep an immutable loan/dependency alive; overlapping mutation and release are forbidden |
| Snapshot | Copy to separately owned storage before mutation; record bytes and lifetime |
| Recompute | Retain sufficient inputs and a checked replay plan, including rule/policy dependencies; charge recomputation |

Recomputation must reproduce the value contract required by the selected pullback.
Effects, randomness, changed parameters, unstable numerical factorizations or a
different execution policy do not become replayable merely because the function
has a pure-looking signature. If the necessary replay equivalence is unavailable,
retain or snapshot explicitly. Checkpointing is a later planner implementing this
contract, not an excuse to omit dependencies now.

A one-shot residual is consumed once. A reusable pullback requires a separate
reusable residual contract with stable shared inputs and explicit workspace on
each call. Freezing dependencies may preserve a first derivative while breaking
higher derivatives; higher-order AD must retain differentiable primal/residual
dependencies as required by [ADR 0001](adr/0001-mathematics-first-stdlib.md).

For example, backward execution for `y = x * x` needs the appropriate old `x`.
Overwriting its uniquely owned buffer with `y` is alias-safe but does not preserve
that dependency. The plan must retain old `x`, snapshot it, or justify replay;
the checker must reject a stale residual even if the new value has the same type.
Invariant-bearing geometric/numerical descriptors follow the same dependency rule.

## 7.11 Tensor ports and execution scheduling

Every occurrence creates fresh ports; every finalized port is connected once or
returned at the boundary under its structural contract. Two occurrences may read
one immutable tensor. Those wiring checks are independent of allocation loans.
Acting on `V` and `W` in one dense `V ⊗ W` buffer may touch all the same entries.
Factor rights and mathematical commutation do not establish disjoint writes.

The initial finite network lowers through a deterministic contraction order and
explicit intermediate/output/scratch lifetimes. Each contraction must pass the
same storage audit as a direct call. No implicit copy, metric or conjugation may
be introduced to repair wiring or memory conflicts. Asynchronous execution and
device transfers remain later profiles with explicit completion/lifetime contracts.

## 7.12 Independent checking and proof boundary

Public protocol 8 must carry enough untrusted layout, region, transition and
dependency information for Lean to reconstruct the resource schedule independently.
Rust annotations, serialized proof flags, claimed alias facts and alleged
initialization are not evidence. Reject unsupported fields in older protocols.

Check the actual returned IR at acceptance and again before native generation.
If optimization changes allocation, fusion, packing, alias scope or retention,
reconstruct and check the resulting plan. Proofs must refer to that same plan
and native lowering contract, not a separately hand-constructed resource model.

Required proof obligations are preservation of live ownership, loan compatibility,
initialized reads, region bounds, scope and dependency validity across admitted
transitions and joins. Runtime checks establish facts that depend on runtime sizes;
their evidence cannot be assumed earlier than the successful branch.
Native ABI, allocator, BLAS, floating-point and hardware behavior remain explicit
trusted boundaries. None of these resource proofs alone proves C-level speed,
whole-program mathematical meaning or higher-order differentiation correctness.

## 7.13 Performance evidence and acceptance

Use a competent C baseline with the same algorithm, scalar representation,
layout, backend/version, thread count, numerical policy and input/output contract.
Exact integer comparisons use an equivalent arbitrary-precision implementation.
A naive triple loop is not the baseline for a Vastitas call to optimized BLAS.
Measure both prepared-kernel execution and the full operation including allocation,
preflight and packing; do not remove those costs from only one side.

| Workload | Required evidence |
| --- | --- |
| Elementwise/strided access and transpose views | Runtime, bandwidth, validation count, allocation/copy count |
| Real/complex GEMM; transpose versus adjoint | Runtime by size, identical backend, adapter overhead, correctness |
| Repeated destination/scratch reuse | Zero unexpected per-call allocation, stable peak live bytes |
| Finite contractions and explicit packing | Total runtime, intermediate bytes, packing bytes/time, deterministic schedule |
| Small calls | Batched measurements, absolute overhead and distribution; not just unstable ratios |
| Retain/snapshot/recompute (with AD) | Forward/backward runtime, peak retained bytes, copy bytes and replay count |

Record source/IR/native revisions, generated code, C source, compiler flags, CPU,
OS, allocator, backend, thread configuration, sizes, input generation, warmup and
raw samples. Alternate measurement order; report distributions and uncertainty.
Check results and observable outputs so dead-code elimination cannot erase work.
Include cache-resident and memory-bound sizes and zero-size/stride edge cases.

The initial engineering target for representative bulk workloads taking at least
1 ms per sample is at most 10% median slowdown against equivalent C on a controlled
host. This is a provisional acceptance budget, not a claim of measured results or
a universal theorem. Publish the paired samples and uncertainty; a noisy result
crossing the budget is inconclusive and requires measurement, not a pass.
For tiny calls, set and record an absolute overhead budget before accepting them.

Unexpected allocation, hidden copies or asymptotically greater data movement fail
the cost contract even if one timing sample is favorable. Correctness CI on both
OSes is mandatory; noisy hosted timing alone is not a performance gate.
Do not silently widen budgets to accommodate a regression. Resolve the cause or
record an explicitly reviewed change of target. Unmeasured or materially slower
paths remain performance gaps and block the corresponding completion claim.

## 7.14 Delivery and regression obligations

1. Finalize allocation/layout/region IR and explicit cost contracts before public
   storage APIs. Implement protocol-8 Rust and Lean changes in the same increment.
2. Reject move-after-use, loan escape, stale generations, overlapping views,
   noninjective writes, uninitialized reads and incompatible branch resources.
3. Check native bounds/alignment/narrowing, failure-before-write, partial-write
   states and scratch release. Include forged raw and checked IR regressions.
4. Implement destination-passing GEMM and finite network schedules; execute actual
   source `check`/`build` outputs and compare equivalent C baselines.
5. Connect actual-checker resource theorems and the final code-generation audit;
   record every remaining native/semantic assumption in `verification.md`.
6. Keep residual metadata extensible, but introduce AD retention/replay and its
   proofs with the later AD work. Do not mark AD implemented by writing this chapter.

The completion record must distinguish implemented checks, regression evidence,
formal theorems, trusted native behavior and measured performance. This chapter
defines the required work; it is not evidence that any unchecked item has passed.
