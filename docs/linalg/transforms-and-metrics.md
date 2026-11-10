# Transforms, evaluation and metrics

This chapter gives the statements that relate a space to its dual and to its
conjugate: derived spaces and bases, involutions, **metrics**, the dual, the
conjugate and the adjoint of a [numerical map](maps-and-gemm.md), **vectors**,
and the pairings of vectors. Nothing is implicit. A conjugation happens only
where a program writes `conjugate`, `adjoint` or `adjoint_into`, and a
Hermitian form enters only where a program names a metric. A pairing is
accepted only between a basis and a basis derived from it, and equal
dimensions prove nothing.

> **Syntax**
>
> ```text
> TransformStatement -> InvolutionStatement | MetricStatement | VectorStatement
>     | AdjointIntoStatement | EvaluateStatement | HermitianStatement
>     | HermitianDiagonalStatement
> ```

The naming rules and the codes for a binding that is not in scope or of
another kind are those of [Numerical maps](maps-and-gemm.md). In this chapter
`V` and `W` are spaces, `bv` and `bw` are bases of them, and `σ` is the scalar
involution: the identity for a real linear implementation and complex
conjugation for a complex one.

## Dual and conjugate spaces

> **Syntax**
>
> ```text
> DerivedSpaceExpression -> `dual` `(` IDENTIFIER `)`
>     | `conjugate` `(` IDENTIFIER `,` IDENTIFIER `)`
> DerivedBasisExpression -> `derived` `(` IDENTIFIER `,` IDENTIFIER `)`
> InvolutionStatement -> `involution` IDENTIFIER `=` `canonical` `(` IDENTIFIER `)` `;`
> ```

`involution sigma = canonical(v);` declares the **involution** of the linear
implementation of the space `v`. `space vd = dual(v);` declares the dual space
of `v`, and `space vc = conjugate(v, sigma);` its conjugate space by `sigma`.
Each **derived space** has the implementation, the dimension and the element
type of `v`. `basis bvd = derived(bv, vd);` declares the **derived basis** of
the basis `bv` in the derived space `vd`: the dual basis in a dual space, and
the conjugate basis in a conjugate space.

Rules:

- The argument of `canonical`, the argument of `dual` and the first argument
  of `conjugate` must be spaces (`E_NUMERICAL_TYPE`).
- The involution of `conjugate(v, sigma)` must be an involution of the
  implementation of `v` (`E_NUMERICAL_TYPE`). An involution that another
  space of the same implementation declared fits.
- A derived space is a different space from every other space. The dual of a
  dual and the conjugate of a conjugate are not the original space, and two
  `dual(v)` statements declare two spaces.
- In `derived(b, s)`, `b` must be a basis, and `s` must be a space declared as
  the dual or as a conjugate of the space of `b` (`E_NUMERICAL_TYPE`).
- Two `derived(b, s)` statements declare two different bases. Each of them
  fits where a rule needs the derived basis of `b` in `s`.
- `basis(s)` of a derived space `s` declares a basis that is derived from no
  basis. Where a rule needs a derived basis, it is an error
  (`E_NUMERICAL_TYPE`, or `E_NUMERICAL_METRIC` in `hermitian_diagonal`).
- Two `involution` statements over spaces of one implementation declare one
  involution under two bindings. The rules of this chapter say where a
  statement needs the same binding and where any binding of the involution
  fits.

```vast
{{#include ../../examples/packages/linear-transforms/src/main.vast:6:20}}
```

## Metrics

> **Syntax**
>
> ```text
> MetricStatement -> `metric` IDENTIFIER `=`
>     ( `orthonormal` `(` IDENTIFIER `,` IDENTIFIER `)`
>     | `scaled_identity` `(` IDENTIFIER `,` IDENTIFIER `,` GramEntry `)`
>     | `diagonal` `(` IDENTIFIER `,` IDENTIFIER `,` `[` GramEntries? `]` `)` ) `;`
> GramEntries -> GramEntry ( `,` GramEntry )* `,`?
> GramEntry -> `-`? INTEGER_LITERAL
> ```

A **metric** declares a Hermitian form `h` on the space of a basis by its
Gram matrix `G` in that basis: `h(x, y)` is the sum of `σ(xᵢ) gᵢ yᵢ`. The form
is conjugate-linear in `x` and linear in `y`. `orthonormal(b, sigma)` declares
`G = I`, `scaled_identity(b, sigma, c)` declares `G = c·I`, and
`diagonal(b, sigma, [g₁, …, gₙ])` declares the diagonal matrix of its entries.
An entry may be negative, so the form need not be positive. A metric is
declared data: the compiler never derives one from the cells of a buffer.

Rules:

- The first argument of a metric must be a basis and the second an involution
  of the implementation of the space of that basis (`E_NUMERICAL_TYPE`). The
  basis may be a derived basis.
- The entry of `scaled_identity` and every entry of `diagonal` must not be
  zero, unless the space has dimension 0 (`E_NUMERICAL_TYPE`).
- `diagonal` must list as many entries as the space has dimensions
  (`E_NUMERICAL_TYPE`).
- `diagonal` lists at most 4096 entries. The compiler reports a longer list
  at the root manifest (`E_PROTOCOL`).
- A metric has **identity Gram data** when it is `orthonormal`, a
  `scaled_identity` with the entry 1 or a `diagonal` whose entries are all 1.
  `adjoint` and `hermitian` need such a metric.
- `adjoint_into` and `hermitian_diagonal` accept every metric whose entries
  have an absolute value of at most 2⁵³.
- Over a space of dimension 0, every metric has identity Gram data, and no
  bound holds for the entry of a `scaled_identity`.

## Transformed maps

> **Syntax**
>
> ```text
> TransformedMapExpression -> `dual` `(` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `)`
>     | `conjugate` `(` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `)`
>     | `adjoint` `(` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `)`
> ```

A **transformed map** reads the cells of a map `a` as the matrix of another
map. Let `a` be a map from `V` in `bv` to `W` in `bw`, with the matrix `A`:

| Statement | Map | From, to | Matrix |
| --- | --- | --- | --- |
| `map d = dual(a, bwd, bvd);` | The dual map of `a` | The dual of `W` in `bwd` to the dual of `V` in `bvd` | The transpose of `A` |
| `map c = conjugate(a, bvc, bwc, sigma);` | The conjugate map of `a` | The conjugate of `V` in `bvc` to the conjugate of `W` in `bwc` | `σ` of every entry of `A` |
| `map h = adjoint(a, hv, hw);` | The adjoint of `a` for the metrics `hv` and `hw` | `W` in `bw` to `V` in `bv` | The conjugate transpose of `A` |

No statement of the table copies a cell. A transformed map is a `read` child
of the loan of `a`, and `gemm` reads its cells transposed or conjugated as
the table says.

Rules:

- The first argument must be a map (`E_NUMERICAL_TYPE`) whose loan permits
  reading (`E_RESOURCE_ACCESS`).
- In `dual(a, bs, bt)`, `bs` must be the derived basis of the target basis of
  `a` in the dual of its target space, and `bt` the derived basis of the
  source basis of `a` in the dual of its source space (`E_NUMERICAL_TYPE`).
- In `conjugate(a, bs, bt, sigma)`, `bs` must be the derived basis of the
  source basis of `a` in the conjugate of its source space by `sigma`, and
  `bt` the same for the target (`E_NUMERICAL_TYPE`). `sigma` must be the
  binding that declared those conjugate spaces.
- In `adjoint(a, hs, ht)`, `hs` must be a metric on the source basis of `a`
  and `ht` a metric on its target basis, both with identity Gram data
  (`E_NUMERICAL_TYPE`). The two metrics may name different bindings of the
  involution.
- While a transformed map is live, the loan of `a` is suspended. The map `a`
  and every other map on that loan give no access (`E_NUMERICAL_TYPE`).
- `release(m)` ends a transformed map `m`. It must come before the release of
  the loan of `a` (`E_RESOURCE_LOAN`) and before the end of the body
  (`E_RESOURCE_ESCAPE`). Nested transformed maps end from the inside out.
- A transformed map is read-only. As the output of `gemm`, a `dual` map is an
  error (`E_RESOURCE_ACCESS`), and a `conjugate` or `adjoint` map is an error
  (`E_NUMERICAL_TYPE`).
- A transformed map is not a loan. `transpose`, `fill`, `store`, `expect` and
  `copy` that name one are errors (`E_RESOURCE_LOAN`). So are `drop` and
  `move` (`E_RESOURCE_MOVE`) and a `borrow` from one (`E_RESOURCE_TYPE`).
- A transformed map that an arm of a branch declares must be released in that
  arm (`E_RESOURCE_JOIN`).

This function of
[`examples/packages/linear-transforms`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/linear-transforms)
multiplies with the dual of a map:

```vast
{{#include ../../examples/packages/linear-transforms/src/main.vast:69:77}}
```

## Adjoints for diagonal metrics

> **Syntax**
>
> ```text
> AdjointIntoStatement -> `adjoint_into` `(` IDENTIFIER `,` IDENTIFIER `,`
>     IDENTIFIER `,` IDENTIFIER `,` `NativeFast` `)` `;`
> ```

`adjoint_into(a, out, hv, hw, NativeFast);` writes to `out` the matrix of the
adjoint of `a` for the metrics `hv` on the source basis and `hw` on the target
basis. The adjoint `A†` satisfies `hw(A x, y) = hv(x, A† y)`. Its entry in row
`i` and column `j` is `σ(A[j, i]) · gwⱼ / gvᵢ`, for the Gram entries `gv` and
`gw` of the two metrics. The statement writes each cell of `out` once and
uses no other storage.

Rules:

- The first two operands must be maps and the next two metrics
  (`E_NUMERICAL_METRIC`).
- `hv` must be a metric on the source basis of `a` and `hw` a metric on its
  target basis. `out` must be a map from the target basis of `a` to its source
  basis, and it must not be a `conjugate` or `adjoint` map
  (`E_NUMERICAL_METRIC`).
- Every entry of both metrics must have an absolute value of at most 2⁵³
  (`E_NUMERICAL_METRIC`). A call that passes a metric to a function with an
  `adjoint_into` checks the same.
- The loan of `a` must permit reading, and the loan of `out` writing
  (`E_RESOURCE_ACCESS`).
- The view of `out` must not be transposed (`E_RESOURCE_DIAGONAL`). The view
  of `a` may be.
- The views of `a` and `out` must not overlap (`E_RESOURCE_ALIAS`).
- `adjoint_into` initializes the view of `out`.

```vast
{{#include ../../examples/packages/diagonal-metrics/src/real/mod.vast:17:21}}
```

## Vectors

> **Syntax**
>
> ```text
> VectorStatement -> `vector` IDENTIFIER `=`
>     ( `view` `(` IDENTIFIER `,` IDENTIFIER `)`
>     | `conjugate` `(` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `)` ) `;`
> ```

`vector x = view(l, b);` presents the loan `l` as the column of coordinates of
a **vector** of the space of `b`, in the basis `b`. A covector is a vector in
a derived basis of the dual space. `vector xc = conjugate(x, bc, sigma);`
declares the conjugate vector of `x`: a `read` child of the loan of `x` over
the same cells, which a pairing reads conjugated.

Rules:

- In `view(l, b)`, `l` must be a live static loan and `b` a basis
  (`E_NUMERICAL_TYPE`).
- The view of the loan must have as many rows as the space of `b` has
  dimensions, one column, and the element type of that space
  (`E_NUMERICAL_TYPE`).
- Several vectors may present one loan, in different bases. A vector does not
  suspend its loan.
- In `conjugate(x, bc, sigma)`, `x` must be a vector, and `bc` must be the
  derived basis of the basis of `x` in the conjugate of its space by `sigma`
  (`E_NUMERICAL_TYPE`). `sigma` must be the binding that declared that
  conjugate space.
- The loan of `x` must permit reading (`E_RESOURCE_ACCESS`). While the
  conjugate vector is live, the loan of `x` is suspended: `x` and every other
  vector on that loan give no access (`E_NUMERICAL_TYPE`, or
  `E_NUMERICAL_METRIC` in `hermitian_diagonal`).
- `release(xc)` ends a conjugate vector. It must come before the release of
  the loan of its vector (`E_RESOURCE_LOAN`), before the end of the body
  (`E_RESOURCE_ESCAPE`) and, for a conjugate vector of an arm, in that arm
  (`E_RESOURCE_JOIN`). `release(x)` of a vector that `view` declared ends its
  loan.
- A statement may use a vector only while its loan is live and has the layout
  that it had at the `vector` statement (`E_NUMERICAL_TYPE`).
- A vector is not a loan and not a map. `transpose`, `fill`, `store`,
  `expect` and `copy` that name one are errors (`E_RESOURCE_LOAN`). So are
  `drop` and `move` (`E_RESOURCE_MOVE`), a `borrow` from one
  (`E_RESOURCE_TYPE`) and a vector as an operand of `gemm`
  (`E_NUMERICAL_TYPE`).
- No statement writes through a vector. A program writes the cells of a
  vector through its loan.

## Pairings

> **Syntax**
>
> ```text
> EvaluateStatement -> `evaluate` `(` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `,`
>     GemmMode `,` `NativeFast` GemmCoefficient* `)` `;`
> HermitianStatement -> `hermitian` `(` IDENTIFIER `,` IDENTIFIER `,` IDENTIFIER `,`
>     IDENTIFIER `,` GemmMode `,` `NativeFast` GemmCoefficient* `)` `;`
> HermitianDiagonalStatement -> `hermitian_diagonal` `(` IDENTIFIER `,` IDENTIFIER `,`
>     IDENTIFIER `,` IDENTIFIER `,` `scratch` `(` IDENTIFIER `,` Layout `)` `,`
>     `overwrite` `,` `NativeFast` `)` `;`
> ```

A pairing writes one cell.

| Statement | Value |
| --- | --- |
| `evaluate(phi, x, out, mode, NativeFast);` | The sum of `phiᵢ xᵢ`, for a covector `phi` and a vector `x`. It is bilinear and conjugates nothing |
| `hermitian(xc, y, out, h, mode, NativeFast);` | The sum of `xcᵢ yᵢ`, for a vector `xc` of the conjugate space and a metric `h` with identity Gram data. With `xc` the conjugate vector of `x`, it is `h(x, y)` |
| `hermitian_diagonal(xc, y, out, g, scratch(o, layout(…)), overwrite, NativeFast);` | The sum of `xcᵢ gᵢ yᵢ`, for a metric `g` with the Gram entries `gᵢ` |

With `overwrite` the cell of `out` becomes `alpha` times the value. With
`accumulate` it becomes `beta` times the old cell plus `alpha` times the
value. [Matrix products](maps-and-gemm.md#matrix-products) gives `GemmMode`,
`GemmCoefficient` and the rules of coefficients, which hold here.
`hermitian_diagonal` first writes the products `gᵢ yᵢ` to the scratch view of
the owner `o`, and then pairs `xc` with that view.

Rules:

- The first two operands must be vectors (`E_NUMERICAL_TYPE`, or
  `E_NUMERICAL_METRIC` for `hermitian_diagonal`), and their loans must permit
  reading (`E_RESOURCE_ACCESS`).
- In `evaluate(phi, x, …)`, the basis of `phi` must be the derived basis of
  the basis of `x` in the dual of its space (`E_NUMERICAL_TYPE`). A conjugate
  basis is not a dual basis, even over a real implementation.
- In `hermitian(xc, y, out, h, …)`, `h` must be a metric with identity Gram
  data on the basis of `y`. The basis of `xc` must be the derived basis of
  the basis of `y` in the conjugate of its space, declared with the
  involution binding of `h` (`E_NUMERICAL_TYPE`).
- `xc` may be a conjugate vector or a `view` in that conjugate basis. The
  cells of a `view` are read as stored.
- In `hermitian_diagonal`, the metric and the bases must satisfy the rule of
  `hermitian` without the condition on identity Gram data, and every entry of
  the metric must have an absolute value of at most 2⁵³
  (`E_NUMERICAL_METRIC`). A call that passes a metric to a function with a
  `hermitian_diagonal` checks the same.
- `out` must be a live loan (`E_RESOURCE_LOAN`) that permits writing
  (`E_RESOURCE_ACCESS`).
- The view of `out` must have one row and one column, the element type of
  the vectors and no transposition (`E_RESOURCE_GEMM`).
- With `accumulate`, `out` must be a `read_write` loan (`E_RESOURCE_GEMM`).
- `out` must not be the loan of an operand (`E_RESOURCE_LOAN`) or a child of
  it (`E_NUMERICAL_TYPE`).
- `hermitian_diagonal` reports four of these errors of `out` under other
  codes: an owner, another element type and a transposed view as
  `E_RESOURCE_DIAGONAL`, the loan of an operand as `E_RESOURCE_ALIAS`, and a
  child of one as `E_NUMERICAL_METRIC`.
- `scratch(o, layout(…))` must name an owner (`E_RESOURCE_DIAGONAL`) without
  a live loan (`E_RESOURCE_LOAN`). An owned map fits, and an owned-map
  package does not (`E_NUMERICAL_PACKAGE`).
- The layout of the scratch must lie in the allocation
  (`E_RESOURCE_LAYOUT`). It must have as many rows as the space has
  dimensions, one column, no transposition and the element type of the
  vectors (`E_RESOURCE_DIAGONAL`).
- `hermitian_diagonal` takes `overwrite` only and no coefficient
  (`E_PARSE`).
- A pairing initializes the cell of `out`, and `hermitian_diagonal` also the
  scratch view. The scratch need not be initialized before.

While a conjugate vector is live, its vector gives no access. To compute
`h(x, x)`, a program passes one vector to two `ReadVector` parameters, as the
caller of `hermitian_value` below does, or declares vectors on two `read`
loans of the same cells.

These functions of
[`examples/packages/vector-evaluation`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/vector-evaluation)
evaluate a covector on a vector and pair a vector with a conjugate vector:

```vast
{{#include ../../examples/packages/vector-evaluation/src/main.vast:36:57}}
```

## Parameter types

> **Syntax**
>
> ```text
> TransformParameterType -> `DualSpace` `<` IDENTIFIER `>`
>     | `ConjugateSpace` `<` IDENTIFIER `,` IDENTIFIER `>`
>     | `DerivedBasis` `<` IDENTIFIER `,` IDENTIFIER `>`
>     | `Involution` `<` IDENTIFIER `>`
>     | `Metric` `<` IDENTIFIER `,` IDENTIFIER `>`
>     | `OrthonormalMetric` `<` IDENTIFIER `,` IDENTIFIER `>`
>     | ( `ReadVector` | `WriteVector` | `ReadWriteVector` )
>       `<` IDENTIFIER `>` `initializes`?
> ```

| Type | The argument must be |
| --- | --- |
| `DualSpace<v>` | A space declared as `dual` of the argument for `v` |
| `ConjugateSpace<v, s>` | A space declared as `conjugate` of the argument for `v`, with the involution binding that is the argument for `s` |
| `DerivedBasis<b, s>` | The basis declared as `derived` from the argument for `b` in the argument for `s` |
| `Involution<v>` | An involution of the implementation of the argument for `v`; any binding of it |
| `Metric<b, s>` | A metric on the argument for `b` whose involution is the involution of the argument for `s` |
| `OrthonormalMetric<b, s>` | Such a metric with identity Gram data |
| `ReadVector<b>`, `WriteVector<b>`, `ReadWriteVector<b>` | A vector in the argument for `b` whose loan permits the access |

Rules:

- A parameter type must name earlier parameters of the kind that the table
  gives. A name that is no earlier parameter is an error (`E_RESOURCE_NAME`),
  and an earlier parameter of another kind is an error (`E_NUMERICAL_TYPE`).
- An argument that is not what the table gives is an error
  (`E_NUMERICAL_TYPE`). A vector whose loan lacks the access is an error
  (`E_RESOURCE_ACCESS`).
- A body knows only what its parameter types state. A space of the type
  `Space` is not a dual space, a basis of the type `Basis` is not a derived
  basis, and a metric of the type `Metric` has no identity Gram data
  (`E_NUMERICAL_TYPE`).
- The argument for `s` in `Metric<b, s>` and `OrthonormalMetric<b, s>` may
  be any binding of the involution of the metric. A metric keeps the binding
  of its own `metric` statement, and a call checks the body again with the
  bindings of the caller. A `hermitian` or `hermitian_diagonal` of the body
  whose metric and conjugate space then name different bindings is an error
  (`E_NUMERICAL_TYPE` or `E_NUMERICAL_METRIC`).
- One vector passed to two parameters of one call must go to `ReadVector`
  parameters both (`E_RESOURCE_ALIAS`).
- In the body, a vector parameter is a vector, not a loan. A body must not
  release it (`E_RESOURCE_LOAN`).
- A `WriteVector` parameter with `initializes` promises that the body
  initializes every cell (`E_RESOURCE_INIT`). No statement writes through a
  vector, so a body can keep the promise only for a space of dimension 0.
- The types of this chapter are parameter types only. None is the type of an
  owned result.

[Numerical backend](../internals/numerical-backend.md#transforms-vectors-and-metrics)
describes the checking, the native execution and the evidence of these
statements.

## Moved sections

These anchors keep older links working.

- <a id="linear-transforms"></a><a id="typed-dual-conjugate-and-metric-adjoint-protocol-8"></a><a id="objects-involutions-and-bases"></a>Typed dual, conjugate and metric adjoint: [Dual and conjugate spaces](#dual-and-conjugate-spaces).
- <a id="declared-hermitian-forms"></a>Declared Hermitian forms: [Metrics](#metrics).
- <a id="map-operations-and-resources"></a>Map operations and resources: [Transformed maps](#transformed-maps).
- <a id="dependent-function-contracts"></a>Dependent function contracts: [Parameter types](#parameter-types).
- <a id="linear-transforms--wire-and-proof-boundary"></a><a id="wire-and-proof-boundary"></a>Wire and proof boundary: [Numerical backend](../internals/numerical-backend.md#wire-and-proof-boundary-of-transforms).
- <a id="example-and-regression-evidence"></a>Example and regression evidence: [Numerical backend](../internals/numerical-backend.md#example-and-regression-evidence-of-transforms).
- <a id="vector-evaluation"></a><a id="bilinear-vector-evaluation-and-explicit-hermitian-pairing"></a><a id="values-and-operations"></a>Vector evaluation: [Vectors](#vectors) and [Pairings](#pairings).
- <a id="resources-calls-and-output"></a>Resources, calls and output: [Vectors](#vectors), [Pairings](#pairings) and [Parameter types](#parameter-types).
- <a id="independent-checking-and-evidence"></a>Independent checking and evidence: [Numerical backend](../internals/numerical-backend.md#vector-evaluation).
- <a id="diagonal-metrics"></a><a id="explicit-diagonal-metrics-protocol-8"></a>Explicit diagonal metrics: [Adjoints for diagonal metrics](#adjoints-for-diagonal-metrics) and [Pairings](#pairings).
- <a id="realization-and-resource-contract"></a>Realization and resource contract: [Metrics](#metrics), [Pairings](#pairings) and [Numerical backend](../internals/numerical-backend.md#diagonal-metrics).
- <a id="native-costs-and-failure-boundary"></a>Native costs and failure boundary: [Numerical backend](../internals/numerical-backend.md#native-costs-and-failure-boundary-of-diagonal-metrics).
- <a id="checking-proofs-and-examples"></a>Checking, proofs and examples: [Numerical backend](../internals/numerical-backend.md#checking-proofs-and-examples-of-diagonal-metrics).
