# Checked reuse of packed tensor values

Protocol 8 supports a bounded logical-value dependency for the explicit rank-three
packing profile. A named cache records an actual accepted packing into caller-owned
scratch. Its consumer checks that both the source and scratch still represent the
captured allocation versions before performing the ordinary checked contraction.

```vast
cache saved = pack3(t, destination);
release(input_t);
release(packing);
borrow packed_read = read(scratch, layout(8, 4, 3, 5, false));
tensor packed = view3(packed_read, bu, bvd, bw, axes(0, 2, 1), 2);
contract3_cached(saved, packed, b, c, NativeFast);
contract3_cached(saved, packed, b, c, NativeFast);
```

The [complete real/complex example](../examples/packages/cached-tensor-packing/src/main.vast)
uses padded layouts, one explicit packing per scalar representation and two
contractions. Scratch and output remain caller-owned. A cache is a lexical compiler
witness; it is not a resource parameter/result, owned package, snapshot allocation,
read loan, AD residual or runtime cache object.

## Dependency and access contracts

The checker records two stamps after the actual `pack3`: source and scratch
allocation identities, logical versions, scalar representations and physical
layouts. Both stamps use the post-pack state. In particular, disjoint source and
scratch regions may belong to one allocation, whose version advances during packing.
The nominal cache also records the accepted ordered axis bases and grouping.
No source or wire input supplies allocation identities, versions, proof flags or
a trusted packing relation.

`contract3_cached` requires that both allocations are still live with the recorded
versions. The actual packed operand must retain the recorded scratch allocation,
layout, ordered nominal bases and grouping. Its current loan may have a new name
and ancestry after explicit release/reborrow or owner transfer. It must be active,
readable and initialized. The ordinary right operand, output, dual-axis contract,
initialization and alias checks still apply.

The source stamp grants no access and creates no hidden source read loan. The
source can be moved, and a cached contraction can write its allocation using
independent packed scratch when the ordinary GEMM separation checks permit it.
That write invalidates subsequent cache use. Source/scratch drops also invalidate
reuse. The checker never extends an allocation lifetime for a cache.

Every actual fill, store, copy, pack or GEMM advances the written allocation's
logical version and invalidates dependencies mentioning it. This is conservative
for writes into disjoint regions, writes of the same bits and empty operations.
The initial profile tracks whole allocations, not per-region version histories.

Branch joins conservatively invalidate all incoming cache dependencies, even if
neither branch writes them. Caches can be used inside both arms or created locally
inside an arm; local handles are explicitly forgotten before the join. A cache
cannot escape a function or branch. Function calls replay their actual primitive
schedule, so writes through borrowed or owned arguments invalidate the caller's
cache too. Lexical cleanup also forgets invalidated handles.

To refresh a cache, explicitly perform another packing with fresh local names.
There is no automatic repacking, alias-repair copy, hidden allocation or planner.

## Snapshot use and retention

Ordinary `pack3` and `contract3` retain their existing snapshot behavior. Changing
the original source does not change coordinates already copied into scratch.
Ordinary contraction of that old snapshot remains valid; cached contraction
additionally requires its relation to the current original source.

A real read loan already retains a region against overlapping writes, owner moves
and drops for its checked scope. A versioned dependency instead detects that a
previous relation became stale after access ended. It preserves no old bytes and
cannot replace a retention loan. Retain/snapshot/recompute residual strategies,
escaping lifetime contracts and AD execution remain later work; see
[Chapter 7.10](storage-ownership.md#710-reverse-residual-retention-and-mutation).

## Actual schedule and generation boundary

The internal resource schedule includes three metadata operations:

| Operation | Independent requirement | Effect |
| --- | --- | --- |
| `captureDependency` | Fresh symbol; actual live initialized source/scratch loans | Reconstruct both stamps from the current state |
| `requireDependency` | Named live dependency with matching current stamps | Validate use without granting memory access |
| `forgetDependency` | Matching lexical dependency handle, including an invalidated one | End compiler metadata scope |

The audited dependency table rejects duplicate identities, owner/loan collisions,
invalid live stamps and unclosed lexical handles. Writes/drop leave invalidated
entries for explicit cleanup; they cannot be reactivated by reusing a name. A
raw capture asserts no nominal axes or packing equivalence. Only the public
operation's accepted packing certificate can supply a cached contraction.

The source checker records exact pack/capture and require/GEMM schedules, both-arm
receipts, separate all-body probes and declaration origins. Code generation reruns
the complete source checker and the original primitive schedule, including all
dependency operations, before erasing them. Their native lowering is empty.

Regressions cover stale source/scratch versions, disjoint updates, call effects,
move/reborrow, branch invalidation and cleanup, refreshed packing, real/complex
results, malformed wire inputs and forged native plans. The checked-native fixture
executes one packing and two products with three allocations: real counters are
24 peak data bytes, 32 written bytes and 8 copied bytes; complex counters double
those byte counts. All data is freed. The sole copy is the explicit packing.
These arena counters exclude Lean/allocator overhead and BLAS-private memory.
They establish bounded cost evidence, not equivalent-C performance acceptance.

`VastitasOracle.StorageDependencies` derives an earlier capture and an accepted
entry-preserving action suffix from the exact accepted raw schedule prefix. It
proves freshness, no resurrection after invalidation/forgetting, and write/join
invalidation. Checked-cache and consumer-receipt corollaries take an explicit
accepted intervening replay; a right-arm corollary includes the actual left run
and exact allocator reseed. They do not assume branch-local `priorCode` starts
from an empty state. Automatic replay-prefix extraction from arbitrary nested
source receipts remains a source-correspondence obligation.

`VastitasOracle.StorageCachedPacking` connects actual accepted packing/capture,
current allocation versions, nominal packed operands, emitted schedules, public
declaration origins and empty native metadata lowering to those same checker
receipts. The oracle boundary is logical resource history and structural checking. Native byte copying, BLAS arithmetic, full source/native correspondence
and ideal floating-point field laws remain separate trusted/tested or unproved
boundaries. This increment does not complete general scratch pooling, retained
numerical evidence, dynamic shapes, AD or the wider Stage 1 storage issue.
