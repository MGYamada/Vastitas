# Internal affine resource functions

This is the function component of [storage ownership](storage-ir.md), advancing
[#183](https://github.com/MGYamada/Vastitas/issues/183). Its raw component schema is not `.vast` syntax or a replacement for package/Fn/dispatch/edit
checks. [Protocol 8 resource source](resource-source.md) composes this component
with the complete package checker. Dynamic value flow remains required by the
[Stage 1 gate](stage1-completion.md).

## Contracts and calls

`src/storage.rs::functions` and `StorageFunctionProtocol` share an untrusted
component schema. A program has finite definitions and a closed entry. Function
IDs and local symbols are 32-bit component identifiers; they confer no package
visibility or edit authority. Unknown fields, unsupported parameter kinds and
integer narrowing are independently rejected.

| Contract | Actual-call behavior |
| --- | --- |
| Owned parameter | Check scalar, capacity and required initialized regions; move into a fresh callee binding and revoke the caller binding. |
| Borrowed parameter | Check scalar and logical shape; create a child of the actual caller loan with the declared rights, preserving its real offset, padding, transpose and allocation. |
| Numerical space/basis parameter | Preserve the exact caller identity; check explicit static profile/dimension and preceding parameter dependencies. |
| Numerical map parameter | Check both caller bases and the original live snapshot, create an actual child loan, and audit that its map retains both endpoints and the exact borrow transition. |
| Initialized borrowed output | On successful return, require the whole original argument footprint initialized. A single-cell store does not initialize a larger output. |
| Owned result | Check scalar, capacity and initialized regions; reject duplicates and outstanding loans; move into a fresh caller binding in declared result order. |

Borrowed parameters return inside out at the call boundary. A callee-local
transpose does not change the caller's view or lifetime. Two read arguments may
share a region; a writer still needs actual separation. Parameter names confer
no alias evidence. This initial contract rejects borrowed results and local loan
escape. Every owned input/local allocation must be dropped or explicitly returned.

Contracts specify minimum initialization requirements, not trusted summaries.
Each actual call rechecks the body against its caller's real state and derives
writes from the operations. Argument/result transfer adds no buffer allocation
or alias-repair copy. Callers can lend reusable destinations and scratch; any
additional workspace allocation must appear explicitly in the body.

## All-body checking and exact expansion

Every function receives a separate synthetic probe, including unused definitions
and both branch arms. Owned probes start with declared initialization; borrowed
probes use a contiguous view with declared rights. These detect invalid bodies,
captures, recursion and missing output initialization. They do **not** prove
acceptance for every layout/alias configuration: a hardcoded subview may fit the
probe yet fail for a shifted/padded caller. Actual calls must pass again. Probe
buffers and zero payloads never enter the executable schedule.

Local symbols are renamed freshly per activation. Expanded calls use the same
`Storage.Statement` operations, including explicit moves, loans and returns.
Branch-local bindings cannot escape; both arms receive distinct fresh allocation
and symbol identities. Definition order is irrelevant. Disconnected recursive
cycles and invalid unused bodies are rejected.

Each call records its exact newly appended schedule, preserves the preceding
operations, and independently replays that slice from the actual caller state.
The receipt checks the same resulting state, restored caller loans, distinct
live/unborrowed owned results, their initialization contracts and absence of
unreturned local owners. The final entry schedule is checked again from empty
state and must close every resource. Existing native-plan auditing then precedes
generation. No function probe, loan interpreter or per-element ownership/refcount
operation enters the generated program.

Limits are 4096 definitions, 64 parameters/results each, 64 initialized regions
per owned type and 4096 source statements across all definitions. Each probe and
the executable have separate 4096-unit expansion-work budgets, counting calls,
source statements and emitted actions, plus a depth bound. This bounds even
exponential acyclic call expansion. The resulting primitive schedule retains the
storage checker's bounds. These are compiler limits, not buffer-size limits.

## Evidence and remaining boundaries

`VastitasOracle.StorageFunctions` imports the actual component. It extracts exact
call-slice replay and caller-loan restoration, distinct owned results with declared
scalar/capacity and initialized bytes, and exclusion of local owner escape. Every
original body has a checked probe retaining its source ID. Decoder, executable
expansion and final closed-plan equations refer to the same input; generation
requires that certificate. These facts do not prove arbitrary parametric function
contracts, full source correspondence or native refinement.

`tests/fixtures/storage-functions.json` crosses Rust serialization, independent
Lean acceptance and native generation. It covers moved/returned owners, nested
calls, shifted/padded views, callee-local transpose, shared read aliases, repeated
destination reuse, unused functions and both branch arms. Its success executable
records three allocations/frees, zero live bytes, 128 peak bytes, 128 written bytes
and 64 copied bytes. Two copies reuse one destination; probes add no allocation.
Assertion/allocation failures also close all buffers. `FunctionRegression` covers
tampering, actual alias conflicts, probe/caller layout disagreement, incomplete
initialization, escape, capture, recursion and expansion limits.

Calls currently expand synchronously with static shapes and capacities. Public
dependent numerical inputs compose through [protocol 8](numerical-values.md#dependent-numerical-inputs);
the older resource-only internal wire schema remains unchanged. Numerical
input receipts supplement the existing exact call replay and loan-return checks.
Initialized owned-map inputs/results additionally preserve input-dependent bases,
allocation identity and the actual coordinate layout. Their transfer emits only
the existing checked move; temporary loans cannot escape. Result contracts are
checked in the post-body state, and actual-layout loans permit padded/subregion
results to be used inside a generic helper without guessing its physical layout.
See [owned numerical results](numerical-values.md#owned-numerical-results).
General tensor types, general pure-Core/resource interoperation, runtime
dimensions/conditions, general owned-result branch joins and escaping-loan
lifetime contracts are not supplied by this component. General dynamic source
composition, general generative numerical result packages, general scratch/dependency handling and equivalent-C
measurements remain in Stage 1. Independent compilation caching and broader
lifetime extensions retain their separate scope.

Function bodies are not transactions. Initialization postconditions describe
successful return; native failure after earlier writes does not roll those writes
back, and publishes no initialized success value. Mathematical meaning, physical
writes and native failure behavior remain distinct from logical resource proofs.

[Owned-map packages](owned-map-packages.md) now add the bounded
`OwnedMapTo<source_basis,target_dimension>` profile: one hidden primal target and
direct basis, initialized affine storage, fresh consuming unpack and explicit
repack. The source basis remains an actual caller dependency. Pack/open/transfer
preserve the exact allocation/layout and emit no additional native instructions.
Dynamic dimensions, general resource packages/closures, borrowed results and
full source/native refinement remain pending.


The [bounded packing cache](cached-packing.md) adds lexical dependency witnesses
for actual rank-three packing and repeated contraction. Capture/require/forget
remain in the exact replayed call schedule; local witnesses are forgotten before
function and branch exits. Mutations through real dependent calls invalidate the
caller witness, and returned owners do not carry a cache lifetime contract.
