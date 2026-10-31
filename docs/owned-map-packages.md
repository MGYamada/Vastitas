# Generative owned-map packages

Protocol 8 supports `OwnedMapTo<source_basis, target_dimension>`, an affine
package containing one initialized owned map, one hidden primal target space and
its direct basis. The source basis is an explicit dependency on an earlier
parameter. Dimensions remain static. This bounded profile does not implement
runtime dimensions, arbitrary existential resource tuples or borrowed results.

The [real and complex example](../examples/packages/generative-owned-map/)
returns locally generated targets, passes packages through nested calls, opens
and repacks them, and uses their exact padded allocation through dependent
owned-map and read-map parameters. It builds and runs without OpenBLAS because
its checked schedule contains no GEMM.

```vast
resource fn create(u: Space<profiles::RealSmooth, 2>, bu: Basis<u>)
    returns (boxed: OwnedMapTo<bu, 3>) -> Unit {
    space w = linear(profiles::RealSmooth, 3);
    basis bw = basis(w);
    allocate buffer: F64[10];
    borrow initialize = write(buffer, layout(8, 3, 2, 4, false));
    fill(initialize, f64_bits(0));
    release(initialize);
    map result = owned(buffer, layout(8, 3, 2, 4, false), bu, bw);
    map boxed = pack(result);
    value { () }
}
// In a caller with u and bu:
call create(u, bu) -> (boxed);
unpack boxed as (w, bw, result);
borrow coordinates = read(result);
release(coordinates);
drop(result);
```

`pack` consumes an initialized `OwnedMap`. Its target must be primal and its basis
direct; hiding a dual/conjugate origin, derived basis or metric dependency needs a
richer closure contract and is rejected. The independent check retains the exact
source basis, implementation, geometric base, real/complex coefficient profile,
allocation, offset, stride, transpose and initialization. Equal dimensions do not
establish these identities. Padding outside the view need not be initialized.
Outstanding loans prevent packing, moving, passing or returning the owner.

An opaque package permits only metadata-preserving ownership moves, matching
`OwnedMapTo` arguments/results, consuming unpack and drop. Raw borrowing, raw
`Owned` arguments/results and reconstruction as another owned map are rejected
while it is opaque. These restrictions are checked in the actual resource
compiler, including direct internal function input; frontend binding kinds do
not supply authority. An opaque value's binding name must equal its owner.

`unpack boxed as (w, bw, result);` consumes `boxed` and introduces fresh abstract
space and basis brands plus a fresh owner name. It keeps the source basis and
all physical storage metadata. Two independent same-dimensional packages remain
distinct. Repacking and opening again introduces new abstract identities; an old
opened basis cannot type the newly opened map. No conversion, conjugation,
metric, coordinate copy or equality evidence is inserted.

Opened names belong to the current function or branch scope. Ordinary owned-map
results still refer only to basis parameters; a hidden local target cannot escape
through that result contract. Repack explicitly to return a hidden target. A
function must return or drop every local owner and restore all caller loans.
General result joins between branches and escaping borrowed lifetimes remain
outside this profile. Both branches and every unused resource body are checked;
synthetic argument probes never supply executable payloads.

## Wire and independent certificates

Parameters use `kind:"owned_map_to"` with `name`, `source`, `dimension`, `span`.
Results use `type:{kind:"owned_map_to",source,dimension}`. The source dependency
must name an earlier basis parameter. `pack_map` has `name` and `owner`;
`unpack_map` has `package`, `space`, `basis`, `owner`. All appear inside the usual
numerical operation envelope. Rust and Lean independently decode these forms;
unknown fields, supplied allocation IDs, success flags and old wire envelopes
are rejected. The fields contain unresolved source names, not checked brands.

`StorageOwnedPackages.checkPackage` reconstructs and audits the closed target,
actual live/initialized map, fresh opening and exact `Storage.checkAction` move.
`StorageFunctions` retains the accepted operation and emitted-move receipt, plus
actual post-body result receipts. Returned payloads are tagged as raw, map or
package. Real calls validate their original caller's dependencies; package
results carry their closed target across the ordinary lexical-state reset.
The public source checker audits every package operation/result receipt against
the same declaration environment accepted by the full authority checker.

`VastitasOracle.StorageOwnedPackages` proves actual acceptance and emission,
source/allocation/layout preservation, initialization, opening freshness and
witness bindings, closed target restrictions and actual dependent result
contracts. Public origin theorems refer to the exact protocol-8 returned checker
result. These are structural/resource guarantees, not float field laws, full
source operational equivalence or native heap refinement.

## Execution cost and validation

Pack, unpack and transfer emit only existing resource moves. Native lowering
erases moves, so there is no runtime package allocation, coordinate copy or
extra GEMM. The example emits exactly two data allocations (one per scalar
profile), and no copies; no-mathlib/no-OpenBLAS native tests execute padded,
transposed and zero-dimensional variants. This is cost evidence, not a claim of
C parity or completion of the historical Stage 1 gate.

`OwnedPackageRegression` covers actual dependent calls and results, both branch
receipt sets, initialization, outstanding loans, raw erasure, stale allocation,
forged hidden provenance, reused witnesses and opaque name/owner mismatch.
`tests/generative_packages.rs` checks source and strict raw-wire rejection and
executes generated real/complex programs. The optional numerical suite feeds
opened maps into actual real/complex GEMM with unchanged allocation counts and
no copies. The existing resource replay, forged native-plan, cleanup and
sanitizer checks remain applicable.
