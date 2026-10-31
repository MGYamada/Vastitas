# Finite rank-three contraction and explicit packing

Protocol 8 now has a closed real/complex coordinate-tensor increment:

```
C[i,j,l] = sum_k T[i,k,j] * B[k,l]
```

The two inputs have ranks three and two; the output has rank three. The
contracted axes are exactly `T[1]` and `B[0]`, and the ordered output boundary is
`[T[0], T[2], B[1]]`. This is a fixed-axis operation, not general `einsum`, a graph
optimizer, or a tensor-category implementation. General networks, structural
nodes and rewrite laws remain open in #69. The separate
[bounded contraction-tree profile](contraction-trees.md) adds explicit multi-edge
plans and selected-axis regrouping while retaining these fixed operations.

## Actual axis types and representation

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

## Public source

The complete real/complex padded example is
[`examples/packages/tensor-packing`](../examples/packages/tensor-packing/Vastitas.toml).
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

## Independent checking and native execution

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

## Proof and cost boundaries

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
performance claim; see [the performance gate](storage-ownership.md#713-performance-evidence-and-acceptance).

The optional [tensor packing experiment](../experiments/tensor_packing/README.md)
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
