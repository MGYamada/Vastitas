# Tensor networks, packing and contraction trees

Start with two-map wiring, then follow the ordered axes and caller-owned storage through packing, contraction trees and cache invalidation.

<a id="finite-networks"></a>

## Executable finite two-map networks

Protocol 8 supports a deliberately finite profile of [#69](https://github.com/MGYamada/Vastitas/issues/69):
two rank-two map occurrences, one bilinear evaluation edge, one input boundary,
one output boundary and one caller-provided overwrite destination. It is connected
to the independent Lean checker and the existing typed GEMM/storage/native path.
This finite profile is part of the completed [Stage 1 delivery](../stage1-completion.md). Broader network constructions remain with #69.

### Public source

For already constructed maps `left : V → W`, `right : U → V` and
`destination : U → W`, with the same middle basis:

```vast
contract(destination, NativeFast) {
    occurrence a = left;
    occurrence b = right;
    edge(a.input, b.output);
    input(b.input);
    output(a.output);
}
```

`a.input` is the algebraic-dual factor of the source of `left`; `a.output`
is its target factor. Thus the edge means `V∨ ⊗ V → K`, with the dual port
written first. Boundaries retain the uncontracted input of `b` and output of
`a`. The destination must have exactly those source/target objects **and bases**.
In coordinates the requested result is `C[i,k] = Σ_j A[i,j]*B[j,k]`.
Multiplication is bilinear; contraction inserts no conjugation, metric, adjoint,
dual-space identification or basis transport.

Occurrence identifiers are local to this contraction. A repeated immutable map
value may appear under two different occurrence names, for example `a = same`
and `b = same` for an endomorphism squared. Their ports are different even though
they read the same allocation. They do not grant separate mutable-buffer
ownership. Output separation and all loan/access/initialization checks still
come from the existing resource checker. A port must occur exactly once across
the edge and boundaries. Duplicated occurrence names, duplicate port use,
unconnected/unknown ports and reversed boundary roles are rejected.

Explicitly transformed operands use the existing checked
[dual/conjugate/adjoint path](transforms-and-metrics.md#linear-transforms), including its exact nominal
origins, basis evidence and active child loans. A graph cannot supply raw native
flags or convert a conjugate space into an algebraic dual. Merely equal dimensions
do not identify spaces, and distinct bases of one space are not silently identified.

The [complete package](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/finite_network/Vastitas.toml) computes
the rectangular real and complex products from the public GEMM example and checks
every output coordinate. The complex product has entries `1+2i, 3i; 2, 2`;
an inserted conjugation changes it.

```sh
cargo run --locked -- check --manifest-path examples/packages/finite_network/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/finite_network/Vastitas.toml \
  --openblas-prefix /path/to/openblas-0.3.34 -o /tmp/finite-network
/tmp/finite-network
```

On Linux add `--native-cc cc`, as for the existing numerical adapter. The program
prints `42` after its coordinate checks. Source checking needs no OpenBLAS.
The optional native runtime is linked only for executed GEMM; unused network
bodies remain independently checked on the ordinary no-BLAS path.

### Graph and independent acceptance

Rust serializes an unresolved resource statement with `kind: "network"`, `graph`,
`output`, `policy: "native_fast"` and `span`. The graph has:

| Field | Entries |
| --- | --- |
| `occurrences` | Two `{name, value}` objects; `value` is a local map name |
| `edges` | One `{dual, primal}` edge |
| `inputs` | One explicit input boundary port |
| `outputs` | One explicit output boundary port |

Each port is `{occurrence, role}`, where `role` is `input` or `output`. Types,
allocations, inferred conversions, certificates and schedules are not accepted
from the frontend. The decoder bounds these lists before traversing them and
rejects unknown fields at every level. Older protocols reject network statements;
older protocol-8 kernels fail closed on the unknown tag.

`ResourceSource.lowerStatements` independently resolves map names in the actual
function scope. `Storage.Functions.networkOperation` resolves the current call's
activation and passes the actual numerical environment, values and resource state
to `TensorNetwork.check`. It validates occurrence identity, exact port coverage,
edge variance, nominal edge type and ordered boundaries. It then calls the
existing `Storage.Numerical.checkProduct` for the actual three maps. Storage and
GEMM checking are shared with direct products, including stale views, initialization,
output aliases and exact scalar/layout checks. All-body probes remain separate from executable expansion. Both branch arms
are checked, and each arm's receipts are retained exactly once together with
receipts before and after the branch, including nested branches. A branch receipt
records its local schedule segment; it does not claim that both arms execute.

The sole edge determines the left and right operands. Declaration order does not
select a different schedule. Lowering emits exactly one overwrite GEMM with
default alpha one, beta zero and explicit `NativeFast`. There is no order search,
packing, intermediate allocation or copy inserted by the graph layer.
`NetworkReceipt` retains the exact accepted graph, pre-state, mathematical product,
emitted operation and actual accepted storage transition. The public checker audits
that every executable network receipt uses its same accepted declaration environment.

### Proof and validation boundaries

`VastitasOracle.TensorNetwork` imports the actual implementation and proves:

| Theorem | Guarantee |
| --- | --- |
| `ports_used_once` | Every declared occurrence port has exactly one use |
| `admitted_bilinear_edge` | Both edge ends have the same exact basis with dual/vector roles |
| `edge_product_basis` | The graph edge basis equals the actual GEMM inner basis |
| `output_boundary` | Ordered boundaries and destination bases agree |
| `no_implicit_conjugation` | Lowering preserves only the checked operand conjugation flags |
| `same_input_plan` | The same accepted input produces the same GEMM request |
| `actual_lowering` | Actual graph acceptance, emitted GEMM and storage acceptance agree |
| `public_network_origin` | Public acceptance ties the receipt to the exact declaration environment |

These are graph acceptance, nominal typing and exact lowering facts. They do not
prove floating-point arithmetic, a general tensor-category denotation theorem,
full source operational equivalence or native heap/toolchain refinement. They
reuse the existing product/storage proofs rather than reimplementing those models.

`NetworkRegression` checks actual internal expansion and mutated graphs/values/native
instructions. `tests/numerical_source.rs` checks public source, strict raw-wire
rejection, unused bodies, branches, declaration-order independence, alias rejection
and immutable reuse. Its optional native test executes real/complex rectangular
products, `(2+3i)^2 = -5+12i` through two occurrences of one map, and nested dependent
calls. Both numerical CI jobs run the optional source tests. The direct pair emits
six data allocations and two GEMMs, without copies; the reuse pair emits four data
allocations and two GEMMs. These are structural costs, not C-parity measurements.

### Remaining scope

This profile has exactly two rank-two maps and one contraction, uses a caller-owned
destination, and fixes overwrite with unit alpha. Network accumulation and scalar
coefficients, arbitrary rank or multiple edges, scalar covector/vector evaluation,
explicit Hermitian pairing nodes, trace/copy/diagonal/hyperedge nodes, general metric
realization, rewrites and contraction-order optimization are not implemented here.
The existing crossing-word `Graph` checker and its categorical obligations remain
separate. The broader #69 checklist stays open.

The delivery includes bounded runtime shapes, explicit scratch and packing dependencies. Stage 2 or later owns equivalent-C runtime and outstanding total-memory measurements. [Integrated evidence](../stage1-completion.md)

The separate [rank-three contraction and packing profile](#tensor-packing)
now supplies one fixed higher-rank coordinate contraction with explicit scratch.
It does not extend this two-map graph schema or implement general graph rewriting.

<a id="tensor-packing"></a>

## Finite rank-three contraction and explicit packing

Protocol 8 now has a closed real/complex coordinate-tensor increment:

```text
C[i,j,l] = sum_k T[i,k,j] * B[k,l]
```

The two inputs have ranks three and two; the output has rank three. The
contracted axes are exactly `T[1]` and `B[0]`, and the ordered output boundary is
`[T[0], T[2], B[1]]`. This is a fixed-axis operation, not general `einsum`, a graph
optimizer, or a tensor-category implementation. General networks, structural
nodes and rewrite laws remain open in #69. The separate
[bounded contraction-tree profile](#contraction-trees) adds explicit multi-edge
plans and selected-axis regrouping while retaining these fixed operations.

### Actual axis types and representation

A tensor view retains an ordered list of actual local bases, an exact live
resource-loan snapshot, a physical axis permutation, and a split between the
row and column groups of an existing rectangular layout. All axes use the same
accepted numerical implementation, scalar base, coefficient kind and geometric
setting. Rank is two or three; each extent fits the LP64 dimension bound.
The accepted declaration environment and complete basis/space origins are
rechecked. No grouped nominal object or basis is manufactured from a product
of dimensions.

For the example, the axis bases are `[bu, bvd, bw]` and `[bv, bxd]`.
`bvd` must be the corresponding basis of the actual algebraic dual of `bv`'s
space: its parent is `bv` and its space origin is that exact space's dual.
A different basis of the same space, an unrelated equal-sized space, or a
conjugate space cannot replace it. The destination axes must be exactly
`[bu, bw, bxd]` in that order. Axes may reuse a basis; their positions remain
distinct. Axis labels grant no storage ownership or disjointness evidence.

`view2` defaults to physical groups `[0 | 1]`; the tree increment also accepts an
explicit rank-two grouping. `view3` specifies a complete permutation
and its row-group length. The first axis within each group is fastest:

| Axes / groups | Rectangular coordinate |
| --- | --- |
| `T`, `[0 | 1,2]` | `(i, k + dim(V)*j)` |
| Packed `T`, `[0,2 | 1]` | `(i + dim(U)*j, k)` |
| `B`, `[0 | 1]` | `(k, l)` |
| `C`, `[0,1 | 2]` | `(i + dim(U)*j, l)` |

The underlying `Storage.Layout` remains a nontransposed column-major rectangle,
including its byte offset and leading dimension. Group products must equal its
actual row/column counts. Padding is outside the coordinate domain. These
metadata describe storage order without changing mathematical axis order or
assuming a structural symmetry law.

### Public source

The complete real/complex padded example is
[`examples/packages/tensor-packing`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/tensor-packing/Vastitas.toml).
Its key steps are:

```vast
// input_t is an initialized read loan, with rows=u and columns=v*w.
tensor t = view3(input_t, bu, bvd, bw, axes(0, 1, 2), 1);
tensor b = view2(input_b, bv, bxd);

// The caller allocates scratch and supplies its write loan.
borrow packing = write(scratch, layout(8, 4, 3, 5, false));
tensor destination = view3(packing, bu, bvd, bw, axes(0, 2, 1), 2);
pack3(t, destination);
release(packing);

// Initialization does not upgrade a write-only loan to readable access.
borrow packed_read = read(scratch, layout(8, 4, 3, 5, false));
tensor packed = view3(packed_read, bu, bvd, bw, axes(0, 2, 1), 2);
tensor c = view3(output, bu, bw, bxd, axes(0, 1, 2), 2);
contract3(packed, b, c, NativeFast);
```

`pack3` preserves the exact ordered axes and supports precisely
`[0 | 1,2]` to `[0,2 | 1]`. It copies to an existing writable destination;
it neither allocates nor conjugates. Both inputs and output of `contract3` must
already have the prescribed grouping. No implicit packing, output permutation,
metric, conjugation, alias-repair copy, or permission escalation is inserted.
A caller whose input is already grouped can construct the corresponding view
and omit packing explicitly.

The first contraction profile uses overwrite, alpha one, absent beta and explicit
`NativeFast`. It emits one ordinary resource GEMM with `M=u*w`, `K=v`, `N=x`.
The existing resource checker validates input initialization, access, scalar
representation and actual output-byte separation. Neither tensor factors nor
separate source names can authorize overlapping writes.

Tensor descriptors are local metadata. Existing dependent space/basis and
borrowed rectangular parameters allow helpers to construct local tensor views,
pack or contract, and return initialized caller destinations. Tensor-valued
parameters/results and generative tensor packages are not added here.
An existing `OwnedMapTo<bx, 3>` result can supply the rank-two operand: unpacking
introduces its actual target `v` and basis `bv`; deriving `bvd` from that opening
then supplies the corresponding contracted axis of the rank-three operand.
Combined tests execute this path in both branch directions and reject replacing
`bv` with a same-sized basis from a different opening.

### Independent checking and native execution

The strict protocol-8 `tensor` statement carries an unresolved operation:

- `view`: `name`, `loan`, ordered `axes`, and `grouping` with `order` and `split`.
- `pack`: `source` and `target` tensor names.
- `contract3`: `left`, `right`, `output`, and `native_fast` policy.

The decoder bounds axes and permutations before traversing them and rejects
unknown fields. It accepts no allocation IDs, resolved bases, flags, proof
objects or fabricated schedules. Older envelopes reject these statements.
`TensorNumerical` reconstructs the actual values in the same declaration
environment used by the full authority checker. `StorageFunctions` retains
constructor, packing and contraction receipts with exact accepted states and
emitted code. Both branch arms retain all receipts exactly once; local tensor
bindings are restored at branch and call exits, separately from all-body probes.

Raw `Storage.Action.pack3` records source/destination loans and the three extents.
It checks the two precise rectangles, initialized input and byte separation,
and initializes only the destination rectangle. `StorageCodegen` reconstructs
allocation IDs and both layouts from that original schedule; modified packing
dimensions, layouts or instructions fail regeneration.

The native C operation preflights all descriptors, products, representations,
aliases and accounting limits before writing. It uses bounded stack metadata
and nested loops that copy contiguous first-axis blocks. No data or scratch
allocation occurs inside packing. Nonempty overlapping envelopes are rejected,
even for identical mappings; disjoint regions of one allocation are allowed.
Empty cases still validate all metadata and form no element pointers. Source
bytes and destination padding are preserved. The optional storage runtime
remains independent of BLAS; contraction selects the existing numerical runtime.

### Proof and cost boundaries

`VastitasOracle.TensorNumerical` imports the actual checker and proves mixed-radix
index injectivity, the accepted packing coordinates and their actual rectangular
bounds, initialized destination bytes, actual nominal axes/dual origins, actual
GEMM loans, inner extent and coordinate grouping, exact emitted transitions and public declaration origins.
Its finite coordinate-reference theorem uses the same summation order and
requires no field laws. These are not C/FFI memory refinement, floating-point
arithmetic, general tensor-category laws or source/native operational equivalence.

For extents `u,v,w,x` and scalar width `s`, the explicit pack reads and writes
`u*v*w*s` bytes. It increments the existing copied and written counters by that
amount. The caller's scratch capacity, including any padding, remains live until
explicit release/drop. GEMM writes `u*w*x*s` output bytes. There is one packing
operation and one GEMM per contraction in the example; grouping metadata adds
no data allocation. The two example calls contain eight explicit data allocations,
two packs and two GEMMs. These are structural costs, not C-parity measurements.
Arena counters do not cover Lean allocation, allocator overhead, process RSS or
OpenBLAS internal workspace. Compare the complete generated path and a competent
C implementation using the same packing and pinned sequential BLAS, including
full lifecycle and reused scratch/destination scopes. Packing time/bytes, peak
live memory, raw paired samples and uncertainty remain required before any
performance claim; see [the performance gate](../storage-ownership.md#performance-evidence-and-acceptance).

The optional [tensor packing experiment](https://github.com/MGYamada/Vastitas/blob/main/experiments/tensor_packing/README.md)
checks the canonical public executable, instruments its actual emitted resource
instructions, and compares them with a matched explicit C pack plus direct CBLAS.
It includes lifecycle, reused-buffer, packing-adapter and BLAS diagnostic scopes,
exact arena counters, every-coordinate and padding checks, and raw paired samples.
Instrumented reuse hoists setup/cleanup around repeated emitted pack/GEMM calls;
it does not add source-level dynamic iteration. Local validation or exploratory
timing alone does not close the controlled-host performance gate.

Regression coverage includes public real/complex coordinate expectations, padding,
each zero extent, nested dependent calls, both branch directions, forged raw and
native metadata, wrong bases/dual origins, stale loans and explicit permission
transitions. Source checking and unused-body auditing need no OpenBLAS; numerical
CI executes the optional public tensor tests on both operating systems.

The optional [checked packing cache](#cached-packing) binds an actual packing
to source/scratch versions and rejects stale use in `contract3_cached`. Ordinary
`pack3` and `contract3` continue to permit independently stored snapshots.

<a id="contraction-trees"></a>

## Bounded finite contraction trees

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

### Source and explicit execution plan

The complete padded real/complex example is
[`examples/packages/contraction-tree`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/contraction-tree/Vastitas.toml).
It computes, in the written order,

```text
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

The plan contains at most 1024 events. Each event also consumes the global
4096-statement resource source budget, including events in both branch arms.
The source envelope checks this before lowering the plan and reports
`E_RESOURCE_LIMIT` if the total is exceeded. `join result = (edge,left,right,output)`
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

### Independent graph and producer checks

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

### Physical regrouping and costs

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
When the source's first axis occupies 16–64 bytes, has more than one element
and has unit scalar stride in both prepared views, the native loop copies that
entire axis with one `memcpy` per pair of remaining coordinates. The other
groupings use exact 8/16-byte cell copies. Block widths from 16 through 64 bytes select fixed-size
copies outside the loops, allowing the C compiler to inline them; larger blocks
retain the cell loop. This decision uses actual physical strides after all
preflight checks; equal dimensions or nominal factor identities do not justify
coalescing, aliasing or skipping checks. No block includes padding and no
temporary storage is added. Both paths preserve every payload bit, including
signed zeros and signaling NaNs.
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

The separate [matched C experiment](https://github.com/MGYamada/Vastitas/blob/main/experiments/contraction_trees/README.md)
uses the actual emitted schedule and equivalent explicit C packing and GEMMs.
Measurements and sanitizer runs are evidence about those cases, not a native
refinement proof or a claim of C parity. Controlled-host performance acceptance
remains subject to the [performance gate](../storage-ownership.md#performance-evidence-and-acceptance).
The [short-block adapter comparison](https://github.com/MGYamada/Vastitas/blob/main/experiments/contraction_trees/results/2026-11-01-macos-regroup-blocks/RESULTS.md)
retains both rejected variable-copy experiments and the final clean native
comparison. It motivates the bounded 16–64-byte path without claiming a
whole-program speedup or replacing the existing generated/C measurements.
The [subsequent full Linux public-program record](https://github.com/MGYamada/Vastitas/blob/main/experiments/contraction_trees/results/2026-11-01-linux-regroup-blocks/RESULTS.md)
measures clean main `7486d2c` after this optimization. All twelve public programs
and native/output/cost checks passed. It reports adapter, FFI-inclusive reuse and
lifecycle scopes separately, retains tiny overhead and fallback slow observations,
and does not establish a causal old/new speedup or controlled-host acceptance.

### Proofs, tests and remaining scope

`VastitasOracle.TensorContraction` imports actual checked views and proves
mixed-radix coordinate bounds/injectivity, initialized destination bytes,
rank-two physical embedding, actual selected-axis coordinates, exact GEMM
operands/inner extent and a finite coordinate-reference equality preserving
summation and multiplication order. `VastitasOracle.TensorTree` proves actual
single-use ports, corresponding dual origins, the reconstructed connected
producer tree's full node/edge coverage, exact ordered boundary bases,
submitted event order, actual numerical/resource transitions and public
checker origins. `regroup_invalidates_dependencies` connects the actual
destination-write certificate to invalidation of every mentioned cache entry. No field laws, custom axioms, categorical equalities or
floating reassociations are used.

Regression coverage includes more than two edges, rank-two chains, repeated
immutable occurrences, every selected-axis/operand orientation of a rank-three
and rank-two pair, padded real/complex execution, zero extents, scratch reuse,
both branches, 64-node acceptance and 65-node rejection, unrelated cache
survival and generic-regroup cache invalidation, unused bodies, stale/foreign producers, invalid ports,
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

<a id="cached-packing"></a>

## Checked reuse of packed tensor values

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

The [complete real/complex example](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/cached-tensor-packing/src/main.vast)
uses padded layouts, one explicit packing per scalar representation and two
contractions. Scratch and output remain caller-owned. A cache is a lexical compiler
witness; it is not a resource parameter/result, owned package, snapshot allocation,
read loan, AD residual or runtime cache object.

### Dependency and access contracts

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

### Snapshot use and retention

Ordinary `pack3` and `contract3` retain their existing snapshot behavior. Changing
the original source does not change coordinates already copied into scratch.
Ordinary contraction of that old snapshot remains valid; cached contraction
additionally requires its relation to the current original source.

A real read loan already retains a region against overlapping writes, owner moves
and drops for its checked scope. A versioned dependency instead detects that a
previous relation became stale after access ended. It preserves no old bytes and
cannot replace a retention loan. Retain/snapshot/recompute residual strategies,
escaping lifetime contracts and AD execution remain later work; see
[Chapter 7.10](../storage-ownership.md#residual-retention).

### Actual schedule and generation boundary

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
