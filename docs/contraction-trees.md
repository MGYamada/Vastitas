# Bounded finite contraction trees

Protocol 8 accepts explicit contraction trees with 2–64 occurrences, `n-1`
internal edges and a rank-two or rank-three ordered boundary. Each occurrence
and intermediate has rank two or three, and at most one original occurrence
has rank three. This supports finite matrix chains and three-legged trees with
matrix chains along the legs. It does not accept arbitrary rank, cycles,
self-traces, disconnected outer products, structural copy nodes, metric
insertion, or contraction-order search.

Each occurrence refers to an actual tensor view with ordered nominal bases.
Each port is an occurrence name and axis index. Occurrences may share an
immutable tensor or allocation; their distinct ports confer no storage
separation. Every port occurs exactly once in an edge or the ordered boundary.
An edge explicitly names its dual and primal endpoints; those bases must have
the actual corresponding parent and dual-space origin. Equal dimensions,
conjugate spaces and unrelated bases cannot supply that evidence.

## Source and explicit execution plan

The complete padded real/complex example is
[`examples/packages/contraction-tree`](../examples/packages/contraction-tree/Vastitas.toml).
It computes, in the written order,

```
M[u,w,a] = sum_v T[u,v,w] * A[v,a]
C[u,a,b] = sum_w M[u,w,a] * B[w,b]
```

The logical axes of `T`, `A`, `B` and `C` are respectively
`[bu,bvd,bwd]`, `[bv,bad]`, `[bw,bbd]` and `[bu,bad,bbd]`.
The graph header is:

```vast
contract_tree(c, NativeFast) {
    occurrence t = t;
    occurrence a = right_a;
    occurrence b = right_b;
    edge ev = (t[1], a[0]);
    edge ew = (t[2], b[0]);
    boundary(t[0], a[1], b[1]);
    plan {
        // Explicit borrows, tensor views, regroup/rebind and named joins.
    }
}
```

The plan contains at most 1024 events. `join result = (edge,left,right,output)`
consumes two distinct active components and the named connecting edge. It emits
one checked overwrite GEMM with alpha one, absent beta and `NativeFast`.
The selected axis is the GEMM inner coordinate. Free left axes retain their
order as the row group; free right axes retain their order as the column group.
The output has exactly the ordered free-left followed by free-right bases.
Primal-on-left contractions keep the written operand order. Conjugation,
transposition and reassociation are never inferred.

`regroup(component,destination)` explicitly copies that component to a
caller-supplied writable tensor view with the **same ordered logical axes**.
Its physical permutation/grouping may differ. The operation does not allocate.
Rank-three views use all six axis permutations and either split. Rank-two
views default to `[0 | 1]`; an explicit alternative is
`view2(loan, first_basis, second_basis, axes(1,0), 1)`.
Every rectangular descriptor includes its actual byte offset and leading
dimension. The first listed axis is fastest within each row or column group.

A regroup or contraction leaves its component attached to the exact written
producer allocation, version, layout and view. To use a write-only result as
an input, the plan must release that write loan, borrow a read loan, construct
the corresponding tensor view and call `rebind(component,read_view)`.
Rebinding checks the same producer allocation/version, ordered axes, grouping
and layout. An unrelated initialized buffer of equal shape cannot substitute.
The example reuses its one scratch allocation after releasing the first packed
read loan. No alias-repair copy, hidden temporary or permission upgrade occurs.

Plan preparation permits only explicit borrow/release and view construction.
Allocations, initialization of original inputs and final drops belong to the
surrounding resource program. Plan-local loans must be released; the exact
caller loan list is restored. Plan-local names do not escape. Calls and both
ordinary branch arms retain all tree receipts, while all-body probes remain
separate from executable expansions. Tensor-valued parameters and results are
not introduced; existing dependent space/basis and rectangular-loan parameters
can construct local views.

## Independent graph and producer checks

Rust serializes unresolved graph names, ports, ordered boundaries and the
explicit plan. Lean independently resolves local bindings, actual bases and
loans against the public declaration environment. The strict additive protocol-8
`tree` statement has `graph`, `output`, `policy`, `plan` and `span` fields.
The graph has `occurrences` (`name`,`value`), `edges` (`name`,`dual`,`primal`)
and `boundary`; a port has `occurrence` and `axis`.
Plan `kind` values are `action`, `view`, `regroup`, `rebind` and `join`.
Only borrow/release actions are admitted. Unknown fields, trusted-proof fields,
allocation IDs and fabricated native flags are rejected.

Local counts and single-use ports are insufficient for connectivity: a
boundary component beside a disconnected cycle can satisfy them. The checker
therefore reconstructs active components and a binary producer tree. Every
join connects disjoint leaf sets through its actual declared edge. At every
step it checks the occurrence partition, remaining port frontier, consumed
edges and exact original port-to-basis mapping. Completion requires one
producer tree containing every occurrence and edge exactly once, the precise
ordered boundary and the caller's exact initialized output view. No component
or cycle can be silently discarded. Declaration order does not choose execution
order; the submitted named plan does.

The checker retains each actual `CheckedRegroup` or `CheckedSingle` result,
its accepted event, before/after resource state and exact action suffix.
Each suffix and the whole tree schedule are independently replayed by the
resource checker, then checked again during ordinary resource expansion and
native code generation. Both branch arms preserve all receipts and public
origin audits.

## Physical regrouping and costs

The existing optimized `pack3` handles `[0 | 1,2]` to `[0,2 | 1]` unchanged.
Other explicit regroupings use `Storage.Action.regroup3` and the native bounded
permutation loop. Its descriptor contains three physical extents and two
encoded grouping permutations. For rank two, a trailing physical extent one
and trailing index zero embed the same rectangle; this adds no logical axis,
space or basis. The oracle proves that embedding preserves the actual rank-two
coordinates.

For logical dimensions `d` and a group `p`, flattening is first-axis-fastest:
`index[p0] + d[p0] * (index[p1] + ...)`. Row and column groups determine the
actual rectangle coordinate. Its byte address is
`offset + scalar_width * (row + leading * column)`.
The native code independently checks both permutations, all dimensions and
products, complete rectangles, scalar agreement, nonempty envelope separation
and accounting overflow before pointers or writes. Raw 8/16-byte cells are
copied without conjugation; source bytes and destination padding are preserved.
Empty volume still validates all metadata and performs no pointer formation,
copy or counter increment. Overlapping nonempty envelopes, including identity
mapping in place, are rejected. Disjoint regions of one allocation are allowed.

Each explicit regroup reads and writes `product(dimensions)*scalar_width`
bytes and increments copied and written counters by that volume. Each GEMM
writes its actual output rectangle. For the example dimensions `(u,v,w,a,b)`,
packing copies `(u*v*w + u*w*a)*scalar_width` bytes, and GEMMs write
`(u*w*a + u*a*b)*scalar_width` bytes. Both terms for the reused scratch remain
visible; its capacity is the maximum required physical envelope, including
padding. Each scalar profile has six caller allocations, two packs and two
GEMMs. Metadata and proofs erase from generated code. Arena counters exclude
Lean allocation, allocator overhead, RSS and BLAS internal workspace.

The separate [matched C experiment](../experiments/contraction_trees/README.md)
uses the actual emitted schedule and equivalent explicit C packing and GEMMs.
Measurements and sanitizer runs are evidence about those cases, not a native
refinement proof or a claim of C parity. Controlled-host performance acceptance
remains subject to the [performance gate](storage-ownership.md#713-performance-evidence-and-acceptance).

## Proofs, tests and remaining scope

`VastitasOracle.TensorContraction` imports actual checked views and proves
mixed-radix coordinate bounds/injectivity, initialized destination bytes,
rank-two physical embedding, actual selected-axis coordinates, exact GEMM
operands/inner extent and a finite coordinate-reference equality preserving
summation and multiplication order. `VastitasOracle.TensorTree` proves actual
single-use ports, corresponding dual origins, the reconstructed connected
producer tree's full node/edge coverage, exact ordered boundary bases,
submitted event order, actual numerical/resource transitions and public
checker origins. No field laws, custom axioms, categorical equalities or
floating reassociations are used.

Regression coverage includes more than two edges, rank-two chains, repeated
immutable occurrences, every selected-axis/operand orientation of a rank-three
and rank-two pair, padded real/complex execution, zero extents, scratch reuse,
both branches, unused bodies, stale/foreign producers, invalid ports,
disconnected cycles, opaque packages and forged wire/native metadata. Native
C tests independently cover all 144 rank-three grouping pairs, raw special
bits, padding, same-allocation separation, invalid codes, overflow and failure
preservation.

General ranks, multiple rank-three nodes, arbitrary intermediate ranks,
trace/copy nodes, metrics and Hermitian contractions, automatic planning,
common-subexpression reuse and tensor-category rewrites remain outside this
profile. The separate cached-pack increment supplies explicit version/dependency
reuse receipts; it does not authorize implicit reuse inside this plan. Full
source/native correspondence, C/FFI/BLAS refinement, floating laws and the
historical Stage 1 performance gate remain open.
