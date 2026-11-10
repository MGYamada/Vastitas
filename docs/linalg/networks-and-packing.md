# Networks, packing and contraction trees

This chapter gives the statements that contract [numerical maps](maps-and-gemm.md)
and **tensors** along the edges of a graph: a network of two maps, tensors
with two or three axes, their packing and contraction, contraction trees with
an explicit plan, and caches of a packing. Nothing is implicit. An edge joins
a basis with the same basis or with its derived dual basis, and equal
dimensions prove nothing. No statement of this chapter conjugates, uses a
metric or allocates, and only `pack3`, `cache` and `regroup` copy cells.

> **Syntax**
>
> ```text
> TensorStatement -> TensorView `;`
>     | `pack3` `(` IDENTIFIER `,` IDENTIFIER `)` `;`
>     | `contract3` `(` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `,` `NativeFast` `)` `;`
>     | `cache` IDENTIFIER `=` `pack3` `(` IDENTIFIER `,` IDENTIFIER `)` `;`
>     | `contract3_cached` `(` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `,`
>       IDENTIFIER `,` `NativeFast` `)` `;`
> ```

The naming rules and the codes for a binding that is not in scope are those of
[Numerical maps](maps-and-gemm.md). No parameter type takes a tensor, a
network or a cache: a function receives loans and bases and declares its own
tensors.

## Two-map networks

> **Syntax**
>
> ```text
> NetworkContraction -> `contract` `(` IDENTIFIER `,` `NativeFast` `)`
>     `{` ( NetworkDeclaration `;` )* `}`
> NetworkDeclaration -> `occurrence` IDENTIFIER `=` IDENTIFIER
>     | `edge` `(` NetworkPort `,` NetworkPort `)`
>     | `input` `(` NetworkPort `)`
>     | `output` `(` NetworkPort `)`
> NetworkPort -> IDENTIFIER `.` ( `input` | `output` )
> ```

A `contract` block writes the composition of two maps as a **network**. Each
**occurrence** is a node that stands for one use of a map. It has two
**ports**: `.input` stands for the dual of the source space of the map, and
`.output` for its target space. The `edge` contracts the input port of one
occurrence with the output port of the other. `input` and `output` name the
two remaining ports, the **boundary**, which are the source and the target of
the result. With `edge(a.input, b.output)` the destination receives the map of
`a` after the map of `b`. The statement is the `overwrite` product of
[Matrix products](maps-and-gemm.md#matrix-products) for the same three maps,
without a coefficient. The order of the declarations has no effect.

Rules:

- The block must hold two `occurrence` declarations, one `edge`, one `input`
  and one `output` (`E_NETWORK`).
- The two occurrences must have different names (`E_NETWORK`). They may name
  one map. An occurrence name is local to the block: it may equal the name of
  a binding, and it must not be a reserved name (`E_RESERVED`).
- An occurrence must name a map (`E_NETWORK`). It may name a
  [transformed map](transforms-and-metrics.md#transformed-maps).
- Each of the four ports must be used once, by the edge or by the boundary
  (`E_NETWORK`).
- The first port of the edge must be an input port and the second an output
  port, of different occurrences (`E_NETWORK`).
- `input` must name the input port of the occurrence whose output port is in
  the edge, and `output` the output port of the other occurrence
  (`E_NETWORK`).
- The source basis of the map at the input port of the edge must be the
  target basis of the map at its output port (`E_NETWORK`). Another basis of
  that space, a basis of another space of the same dimension and a derived
  basis do not fit.
- The destination must be a map from the source basis of the map at the
  output port of the edge to the target basis of the map at its input port
  (`E_NUMERICAL_TYPE`).
- The rules of [Matrix products](maps-and-gemm.md#matrix-products) on access,
  transposition and overlap hold for the destination and the two maps.

```vast
{{#include ../../examples/packages/finite_network/src/real/mod.vast:30:39}}
```

## Tensors

> **Syntax**
>
> ```text
> TensorView -> `tensor` IDENTIFIER `=`
>     ( `view2` `(` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER ( `,` AxisGrouping )? `)`
>     | `view3` `(` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `,`
>       AxisGrouping `)` )
> AxisGrouping -> `axes` `(` ( INTEGER_LITERAL ( `,` INTEGER_LITERAL )* `,`? )? `)`
>     `,` INTEGER_LITERAL
> ```

`tensor t = view3(l, b0, b1, b2, axes(p0, p1, p2), s);` presents the loan `l`
as a **tensor** with three ordered axes, where the basis `bk` indexes axis
`k`. The bases and their order are the type of the tensor. The **grouping**
`axes(p0, p1, p2), s` says how the matrix of the loan stores the cells: the
first `s` axes of the list index its rows and the others its columns, and
within a group the first axis of the list runs fastest. With the dimensions
`d0`, `d1`, `d2` and the grouping `axes(0, 2, 1), 2`, the cell `(i0, i1, i2)`
is in row `i0 + d0·i2` and column `i1`. `view2` declares a tensor with two
axes. Without a grouping it has `axes(0, 1), 1`: axis 0 along the rows and
axis 1 along the columns. A tensor declares no loan and copies no cell.

Rules:

- The first operand must be a live static loan and the others bases
  (`E_TENSOR`).
- `axes(…)` must list each axis number of the tensor once, from 0, and the
  number after it must be at least 1 and less than the number of axes
  (`E_TENSOR`).
- The spaces of all axes must have one linear implementation, and the cells
  of the loan must have its element type (`E_TENSOR`).
- The view of the loan must not be transposed. Its rows must be the product
  of the dimensions of the axes before the split, and its columns the product
  of the others (`E_TENSOR`).
- The dimension of the space of every axis must be at most 2³¹ − 1
  (`E_TENSOR`).
- One basis may index several axes, several tensors may present one loan,
  and a tensor may present a `write` loan.
- A tensor is not a loan and not a map. `release`, `transpose`, `fill`,
  `store`, `expect` and `copy` that name one are errors (`E_RESOURCE_LOAN`).
  So are `drop` and `move` (`E_RESOURCE_MOVE`), a `borrow` from one
  (`E_RESOURCE_TYPE`) and a tensor as an operand of `gemm`
  (`E_NUMERICAL_TYPE`).
- A statement may use a tensor only while its loan is live, has no live child
  and has the layout that it had at the `tensor` statement (`E_TENSOR`).

## Packing and contraction

`pack3(s, t);` copies a tensor with three axes from the grouping
`axes(0, 1, 2), 1` to the grouping `axes(0, 2, 1), 2` in the view of `t`. It
copies each cell bit for bit. `contract3(l, r, out, NativeFast);` contracts
the middle axis of a tensor with three axes with the first axis of a tensor
with two: the cell `(i, j, m)` of `out` is the sum over `k` of
`l[i, k, j] · r[k, m]`. It is one `overwrite` product of the matrices that the
groupings of the rules describe.

Rules:

- The operands of `pack3` must be tensors with three axes and the same bases
  in the same order. The source must have the grouping `axes(0, 1, 2), 1` and
  the target `axes(0, 2, 1), 2` (`E_TENSOR`).
- The loan of the source of `pack3` must permit reading and the loan of the
  target writing (`E_RESOURCE_ACCESS`). Their views must not overlap
  (`E_RESOURCE_ALIAS`).
- In `contract3(l, r, out, NativeFast)`, `l` must have the bases `[a, d, b]`,
  `r` the bases `[v, c]` and `out` the bases `[a, b, c]`. `d` must be the
  derived basis of `v` in the dual of its space (`E_TENSOR`).
- `l` must have the grouping `axes(0, 2, 1), 2`, `r` the grouping
  `axes(0, 1), 1` and `out` the grouping `axes(0, 1, 2), 2` (`E_TENSOR`). A
  tensor that is stored in the grouping of `l` needs no `pack3`.
- The loans of `l` and `r` must permit reading and the loan of `out` writing
  (`E_RESOURCE_ACCESS`). The view of `out` must not overlap the view of `l`
  or of `r` (`E_RESOURCE_GEMM`).
- `pack3` initializes the view of its target, and `contract3` the view of its
  output.

This fragment of
[`examples/packages/tensor-packing`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/tensor-packing)
packs a tensor and contracts it with a matrix:

```vast
{{#include ../../examples/packages/tensor-packing/src/real/mod.vast:33:45}}
```

## Contraction trees

> **Syntax**
>
> ```text
> TreeContraction -> `contract_tree` `(` IDENTIFIER `,` `NativeFast` `)`
>     `{` ( TreeDeclaration `;` )* `plan` `{` PlanStep* `}` `}`
> TreeDeclaration -> `occurrence` IDENTIFIER `=` IDENTIFIER
>     | `edge` IDENTIFIER `=` `(` TreePort `,` TreePort `)`
>     | `boundary` `(` ( TreePort ( `,` TreePort )* `,`? )? `)`
> TreePort -> IDENTIFIER `[` INTEGER_LITERAL `]`
> PlanStep -> BorrowStatement
>     | `release` `(` IDENTIFIER `)` `;`
>     | TensorView `;`
>     | `regroup` `(` IDENTIFIER `,` IDENTIFIER `)` `;`
>     | `rebind` `(` IDENTIFIER `,` IDENTIFIER `)` `;`
>     | `join` IDENTIFIER `=`
>       `(` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `)` `;`
> ```

The graph of a `contract_tree` has one node for each `occurrence`, which
names a tensor. The port `o[k]` is axis `k` of the occurrence `o`. An `edge`
contracts a port whose basis is a derived dual basis with a port whose basis
is the basis that it derives from. `boundary` lists the ports that stay free,
in the order of the axes of the result. The `plan` gives the whole evaluation.
A **component** is a set of occurrences that the plan has contracted, with
the tensor that holds their product. At the start every occurrence is a
component with the tensor that it names.

| Step | Meaning |
| --- | --- |
| `regroup(c, t);` | Copy the tensor of the component `c` to the tensor `t`, which has the same axes in another grouping. `t` is then the tensor of `c` |
| `rebind(c, t);` | Make `t`, another tensor over the same cells, the tensor of `c` |
| `join c = (e, l, r, t);` | Contract the components `l` and `r` along the edge `e` into the tensor `t`, and name the result `c`. It is one `overwrite` product |

The plan fixes the order of the contractions, every copy and every buffer.
The compiler searches for no order and inserts no copy.

Rules:

- The graph must have from 2 to 64 occurrences, one edge fewer than
  occurrences, and 2 or 3 boundary ports. It has at most 128 declarations
  before `plan`, and a plan has at most 1024 steps (`E_TENSOR_TREE`).
- Every plan step counts against the limit on the statements of a program,
  which [Appendix D](../appendix/limits.md#other-documented-bounds) gives
  (`E_RESOURCE_LIMIT`).
- The output and every occurrence must name a tensor that the function
  declared before the statement (`E_TENSOR_TREE`). The loan of the tensor of
  an occurrence must permit reading, and its cells must be initialized
  (`E_TENSOR_TREE`).
- Occurrence names must differ from one another, and edge names from one
  another (`E_TENSOR_TREE`). They are local to the statement and may equal
  names of bindings.
- Every port, one for each axis of every occurrence, must be used once, by an
  edge or by the boundary (`E_TENSOR_TREE`). An axis number that the
  occurrence does not have is an error (`E_TENSOR_TREE`).
- The basis at the first port of an edge must be the derived basis of the
  basis at its second port in the dual of its space. The two ports must
  belong to different occurrences (`E_TENSOR_TREE`).
- A plan step must have one of the forms of `PlanStep`. Another statement
  there, and a `borrow` without a layout, are errors (`E_TENSOR_TREE`).
- A loan or a tensor of the plan must have a name that is not in use
  (`E_DUPLICATE`). It is not visible after the statement.
- The plan must release every loan that it borrows, and no loan of the
  function (`E_TENSOR_TREE`).
- In `regroup(c, t)`, `t` must be a tensor with the bases of `c` in the same
  order (`E_TENSOR`). Its loan must permit writing (`E_RESOURCE_ACCESS`), and
  its view must not overlap the view of `c` (`E_RESOURCE_ALIAS`).
- In `rebind(c, t)`, `t` must be a tensor over a loan that permits reading,
  with the allocation, the layout, the bases and the grouping of the tensor
  of `c` (`E_TENSOR_TREE`). No statement may have written that allocation
  since `c` got its tensor.
- After a `regroup` or a `join`, the tensor of the component is the target.
  A later `regroup` or `join` reads it, so its loan must be live
  (`E_TENSOR_TREE`) and must permit reading (`E_RESOURCE_ACCESS`).
- For a target on a `write` loan, the plan releases that loan, borrows a
  `read` loan of the same view, declares a tensor on it and names it in
  `rebind`. A target on a `read_write` loan needs none of this.
- In `join c = (e, l, r, t)`, `e` must be an edge that no earlier `join` used,
  between a port of the component `l` and a port of another component `r`
  (`E_TENSOR_TREE`). The name `c` must differ from every component name
  (`E_TENSOR_TREE`).
- The tensor of `l` must store its other axes, in order, along the rows and
  the joined axis along the columns. The tensor of `r` must store the joined
  axis along the rows and its other axes, in order, along the columns
  (`E_TENSOR`).
- `t` must have the bases of the other axes of `l` followed by those of `r`,
  with the axes of `l` along the rows (`E_TENSOR`). Its loan must permit
  writing (`E_RESOURCE_ACCESS`).
- At the end of the plan there must be one component. Its ports must be the
  boundary ports in their order. Its tensor must be the output of the
  statement, or a tensor of the plan with the same loan, bases and grouping
  (`E_TENSOR_TREE`).
- `contract_tree` initializes the view of its output.

This tree of
[`examples/packages/contraction-tree`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/contraction-tree)
contracts a tensor with three axes with two matrices:

```vast
{{#include ../../examples/packages/contraction-tree/src/real/mod.vast:33:64}}
```

## Caches

`cache c = pack3(s, t);` packs like `pack3` and binds the **cache** `c`: a
record, at compile time, that the cells of `t` hold the packing of the cells
of `s`. `contract3_cached(c, l, r, out, NativeFast);` is
`contract3(l, r, out, NativeFast)` with two more conditions: `c` is valid, and
`l` presents the cells that `c` recorded. A cache keeps no loan and no
allocation alive, holds no cells and has no effect when the program runs.

Rules:

- `cache c = pack3(s, t)` follows the rules of `pack3`, and `c` must be a
  name that is not in use (`E_DUPLICATE`).
- The first operand of `contract3_cached` must be a cache
  (`E_TENSOR_CACHE`).
- A cache is valid until a statement writes the allocation of `s` or of
  `t`, until one of the two allocations is dropped, and until the end of a
  branch. A write to another part of the allocation counts, and so do a
  `fill` of a view without cells and a write inside a called function.
- `contract3_cached` must name a valid cache (`E_TENSOR`).
- The operand `l` must be a tensor on the allocation of `t`, with the layout
  and the bases of `t` (`E_TENSOR`). It may present another loan than the
  loan of the `cache` statement.
- The other rules of `contract3` hold for `contract3_cached`.
- A cache is not an owner, a loan or an argument of a call. A cache that an
  arm of a branch declares is not visible after the branch
  (`E_RESOURCE_NAME`).
- `contract3` needs no cache. It accepts a packed tensor after a write to the
  source of the packing.

```vast
{{#include ../../examples/packages/cached-tensor-packing/src/real/mod.vast:33:47}}
```

[Numerical backend](../internals/numerical-backend.md#networks-packing-and-contraction-trees)
describes the checking, the native execution and the evidence of these
statements.

## Moved sections

These anchors keep older links working.

- <a id="finite-networks"></a><a id="executable-finite-two-map-networks"></a><a id="public-source"></a>Executable finite two-map networks: [Two-map networks](#two-map-networks).
- <a id="graph-and-independent-acceptance"></a>Graph and independent acceptance: [Numerical backend](../internals/numerical-backend.md#two-map-networks-graph-and-independent-acceptance).
- <a id="proof-and-validation-boundaries"></a>Proof and validation boundaries: [Numerical backend](../internals/numerical-backend.md#two-map-networks-proof-and-validation-boundaries).
- <a id="remaining-scope"></a>Remaining scope: [Numerical backend](../internals/numerical-backend.md#history).
- <a id="tensor-packing"></a><a id="finite-rank-three-contraction-and-explicit-packing"></a><a id="actual-axis-types-and-representation"></a><a id="public-source-1"></a>Rank-three contraction and packing: [Tensors](#tensors) and [Packing and contraction](#packing-and-contraction).
- <a id="independent-checking-and-native-execution"></a>Independent checking and native execution: [Numerical backend](../internals/numerical-backend.md#tensor-packing-independent-checking-and-native-execution).
- <a id="proof-and-cost-boundaries"></a>Proof and cost boundaries: [Numerical backend](../internals/numerical-backend.md#tensor-packing-proof-and-cost-boundaries).
- <a id="bounded-finite-contraction-trees"></a><a id="source-and-explicit-execution-plan"></a>Bounded finite contraction trees: [Contraction trees](#contraction-trees).
- <a id="independent-graph-and-producer-checks"></a>Independent graph and producer checks: [Numerical backend](../internals/numerical-backend.md#contraction-trees-independent-graph-and-producer-checks).
- <a id="physical-regrouping-and-costs"></a>Physical regrouping and costs: [Numerical backend](../internals/numerical-backend.md#contraction-trees-physical-regrouping-and-costs).
- <a id="proofs-tests-and-remaining-scope"></a>Proofs, tests and remaining scope: [Numerical backend](../internals/numerical-backend.md#contraction-trees-proofs-tests-and-remaining-scope).
- <a id="cached-packing"></a><a id="checked-reuse-of-packed-tensor-values"></a><a id="dependency-and-access-contracts"></a>Checked reuse of packed tensor values: [Caches](#caches).
- <a id="snapshot-use-and-retention"></a>Snapshot use and retention: [Numerical backend](../internals/numerical-backend.md#cached-packing-snapshot-use-and-retention).
- <a id="actual-schedule-and-generation-boundary"></a>Actual schedule and generation boundary: [Numerical backend](../internals/numerical-backend.md#cached-packing-schedule-and-generation-boundary).
