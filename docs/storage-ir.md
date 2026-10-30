# Internal storage resource IR

This is an internal foundation for [#183](https://github.com/MGYamada/Vastitas/issues/183),
implementing part of the [Chapter 7 contract](storage-ownership.md). It is not
public protocol 8, `.vast` storage syntax, or native buffer execution. Those
connections, numerical consumers and measured C performance remain in the
[Stage 1 completion gate](stage1-completion.md).

## Input and acceptance

`src/storage.rs` defines an untrusted component schema. The independent decoder
in `VastitasKernel.StorageProtocol` rejects unknown fields, unsupported operations
and integer narrowing: symbols fit unsigned 32 bits, sizes and literal payloads
fit unsigned 64 bits. The checker derives allocation identities and state; callers
cannot supply an allocation identity, initialization flag or checked certificate.
The shared `tests/fixtures/storage.json` exercises every action, both scalar
representations, all access modes, nested borrowing and both branch arms through
Rust serialization and Lean decoding/checking. This is a component fixture, not
an actual-source lowering fixture.

`Storage.checkPlan` starts from an empty environment, checks both branch arms
even for a literal condition, and requires every owner and loan to be closed at
exit. Its certificate records the exact input, `run` result, final audit and
closed-resource equations. `Wire.CheckedInput` additionally records the decoder
and checker equations. Neither certificate is a public wire input. Protocols
2–7 do not execute this component; protocol 2 explicitly rejects the reserved
top-level `resources` field while retaining unrelated legacy hint compatibility.
Protocol 8 remains unsupported.

There is a 4096-node global plan budget as well as a 4096 traversal-depth bound.
Both arms consume the node budget. Every allocation's initialization metadata
has a 4096-node audit budget, checked before traversing its full history.
Repeated writes of an already initialized region reuse its guarantee; identical
branch guarantees share their history, and an empty guarantee annihilates a
branch intersection. These are metadata bounds, not limits on buffer elements.

## Resources and operations

| Operation | Checked transition |
| --- | --- |
| `allocate` | Fresh logical allocation and owner, byte-size bound, initially unwritten storage |
| `move` | No live loans; preserve identity, initialization and version; revoke old owner |
| `drop` | Live owner without loans; remove the logical allocation |
| `borrow` | Derive allocation from owner or parent loan; check layout, read initialization and pairwise compatibility |
| Reborrow | Child bytes contained in parent; neither read nor write permissions may increase; suspend parent access |
| `release` | Live loan with no children; return loans inside out |
| `transpose` | Swap logical axes, preserving physical allocation and byte footprint; reject suspended parent changes |
| `fill`, `store` | Writable active loan, exact scalar representation; record the whole view or the one addressed cell |
| `expect` | Readable active loan, valid index and initialized cell; the expected payload is reserved for a future runtime assertion |
| `copy` | Active readable source and writable destination with equal scalar representation and logical shape; initialized source |
| Branch join | Same owners, allocations and loan structure; intersect initialization guarantees and merge logical versions |

Symbols cannot be reused or shadowed, including after move or release. Fresh
allocations in different branches get different identities and must be dropped
within the branch under this initial closed-plan profile. Explicit owned results,
function lifetime contracts and caller-owned buffers are still pending.

Write-only access never reads, and cannot gain read authority by creating a
child loan. An initialized region can instead be reborrowed through an owner
after returning its write-only loan. Read/read sharing is allowed. Active access
with a writer requires distinct allocations or proven disjoint envelopes.
Ancestors may overlap their children only because their access is suspended;
siblings still undergo compatibility checks. Mathematical tensor factors confer
no allocation or alias rights.

Logical versions advance on writes; a branch join creates a version after both
branches. This is preparation for dependency tracking, not an implementation of
residual retention, stale-dependency rejection, snapshots or AD.

## Layout and initialization

The admitted layout is a column-major physical rectangle with an explicit
logical transpose. Offset and capacity are bytes; leading dimension is elements.
`f64` uses 8 bytes and `complex_f64` uses 16 bytes, with 8-byte relative alignment.
Scalar literals are raw IEEE payloads, not a new public floating-point type or a
claim about floating-point arithmetic. The future native adapter must establish
its matching representation, base alignment and allocator contract separately.

Rows, columns and leading dimension fit nonnegative LP64 dimensions. Leading
dimension is at least `max(1, rows)`, including empty layouts. Capacities and
computed byte offsets fit the signed 64-bit offset bound. Empty layouts validate
metadata but have no element access and may have an unaligned offset. Arithmetic
uses mathematical `Nat` before checking narrowing.

Containment of a contiguous view uses its interval. Containment of a padded
rectangle additionally checks the row/column shift and compatible column grid;
it never treats padding as initialized. A write records its actual rectangle,
and a scalar store records only its single cell. Branch initialization is the
intersection of both exits. The entailment procedure is conservative: separate
partial writes are not combined into a whole-region guarantee without additional
partition evidence. Interleaved views with overlapping envelopes are rejected
when either writes, even if a stronger partition proof could separate them.
Arbitrary strides, read-only broadcast, general partitions and packing remain
pending.

## Proofs and regression evidence

The oracle imports the actual kernel definitions:

| Module | Proved boundary |
| --- | --- |
| `VastitasOracle.StorageLayout` | Every admitted logical cell is in bounds and relatively aligned; distinct cells occupy disjoint byte intervals; transpose preserves the footprint; native stride/offset intermediates fit the checked range |
| `VastitasOracle.StorageRegions` | Containment entails inclusion of actual bytes; disjoint envelopes imply disjoint actual bytes; initialization entailment covers requested bytes; normalized writes/joins preserve the logical initialized-byte meaning |
| `VastitasOracle.StorageSafety` | An audited pair of distinct active loans with a writer cannot share a byte; audited read permissions entail logical initialization; successful action checks audit their input/output; decoder certificates retain the exact checked plan |

`StorageRegression` compares bounds, injectivity, containment and separation with
an independent enumeration of bytes for small real/complex, padded, shifted,
transposed and empty layouts. It also checks moves, access modes, nested loans,
branch joins, initialization, forged states, metadata budgets and a billion-by-
billion layout without expanding its elements. `VastitasStorageTest.Regression`
checks the Rust fixture and malformed component inputs.

These theorems do not prove that actual native memory has been allocated or
written, native pointer addition is valid, cleanup occurs on failure, copies or
numerical results are correct, or a complete source program has resource safety.
`expect` acceptance does not prove that memory equals its supplied payload.
The internal state audit validates initialization metadata; only a plan checked
from the empty state reconstructs its history. Arbitrary externally supplied
audited states are not trusted execution histories.

Public/source integration must preserve all existing function, dispatch,
authority and all-body checks, then send the exact checked resource schedule to
an independent pre-codegen audit. Native liveness and failure-before-write,
destination/scratch reuse, cost records, dependency retention and equivalent-C
measurements remain required. Pure indexed Core theorems do not imply these
mutable-resource guarantees, and this increment does not close #183.
