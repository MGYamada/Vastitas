# Frames

This chapter defines the frames of smooth affine objects, the arrays of
vectors, covectors and linear maps in frames, and the primitive bindings that
encode, decode, change frames and contract arrays. A **frame** of a smooth
affine object `X` of dimension n is an ordered list of n vector fields on
`X`, the frame vectors, whose values at each point of `X` form a basis of the
tangent fiber at that point. The components of the frame vectors are
polynomials in the coordinates of `X` with rational coefficients.
[Smooth affine declarations](smooth-declarations.md) defines smooth affine
objects, smooth maps, tangent and cotangent fibers and the
[failure value](smooth-declarations.md#fiber-primitives) ⊥. The general rules
of `indexed` declarations are in
[Indexed declarations](../indexed-source.md).
[Notation](notation.md) explains the Syntax blocks, and the
[glossary](../appendix/glossary.md) defines the terms.

The examples quote the tested package
[`examples/packages/frames/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/frames),
whose executable prints `42`. Each rejected program is a package on the
profile of the standard library. It appears with the diagnostic that the
compiler prints for it.

The declarations of this chapter are the forms of `FrameProfileDeclaration`:

> **Syntax**
>
> ```text
> FrameProfileDeclaration -> FrameFamily | FrameDeclaration
> ```

Each declaration of this chapter is an [item](items.md):
`FrameProfileDeclaration` is one form of
[`IndexedDeclaration`](../indexed-source.md). So is `PrimitiveDeclaration`,
whose bindings in this chapter are the forms of `FrameBinding`. `pub` before a
declaration makes it visible outside its module.

## Frame matrices

Let `b` be a frame of an object `X` of dimension n. At a point p of `X`,
$P_b(p)$ is the n × n matrix whose column j is frame vector j at p, given in
the coordinates of `X`. $P_b(p)$ is invertible at every point, and $Q_b(p)$ is
its inverse. The **coordinate frame** of `X` is the frame whose frame vector
j is the unit vector of coordinate j, so its matrix is the identity matrix
$I$ at every point. The
components of a [tangent or cotangent fiber](smooth-declarations.md#fiber-primitives)
are its components in the coordinate frame, or in the coordinate coframe for
a covector.

A vector v at p has the components $a = Q_b(p)\,v$ in the frame `b`, so that
$v = P_b(p)\,a$. A covector α at p has the components
$\beta = P_b(p)^\top \alpha$ in the coframe dual to `b`, so that
$\alpha = Q_b(p)^\top \beta$. The pairing of the two arrays is the pairing of
the fibers: $\beta \cdot a = \alpha \cdot v$.

## The frame profile

> **Syntax**
>
> ```text
> FrameFamily -> `indexed` `family` IDENTIFIER `(` Parameters? `)`
>     `=` FrameFamilyForm `;`
> FrameFamilyForm -> `frame` `constraints` `(` Constraints? `)`
>     | FrameArrayRepresentation ( `constraints` `(` Constraints? `)` )?
> FrameArrayRepresentation -> `frame_vector` | `frame_covector` | `frame_map`
> ```

[Families](../indexed-source.md#families) gives the productions
`Parameters` and `Constraints`, including the parameter `frame(F)`.

The representation of a family says which values its indexed types have. The
table names the families of the example below. In the table, `b` and `c` are
frames, of the objects `X` and `Y`.

| Representation | Indexed type | Values |
| --- | --- | --- |
| `frame` | `Frame<X>` | None. An [`indexed frame`](#frame-declarations) declaration names the type |
| `frame_vector` | `Coords<b>` | The arrays of the vectors at the points of `X` in the frame `b`, and the failure value |
| `frame_covector` | `CoCoords<b>` | The arrays of the covectors at the points of `X` in the coframe dual to `b`, and the failure value |
| `frame_map` | `FrameMap<b, c>` | The arrays of the linear maps from a tangent fiber of `X` to a tangent fiber of `Y` in the frames `b` and `c`, and the failure value |

A **frame array** in the frame `b` is a value of a type `C<b>` of a family
`C` with the `frame_vector` or `frame_covector` representation. It is a
point p of the object of `b` and n rational components: the components
$Q_b(p)\,v$ of a vector v at p, or the components $P_b(p)^\top \alpha$ of a
covector α at p. A frame array may also be the failure value ⊥, which lies
over no point. A family with the `frame_vector` representation holds the
arrays of vectors, and one with the `frame_covector` representation the
arrays of covectors.

A **map array** from the frame `b` to the frame `c` is a value of a type
`M<b, c>` of a family `M` with the `frame_map` representation. It is a source
point p of `X`, a target point q of `Y` and an m × n matrix A of rational
numbers, where n and m are the dimensions of `X` and `Y`. It stands for the
linear map L from the tangent fiber at p to the tangent fiber at q with
$L(P_b(p)\,a) = P_c(q)\,(A\,a)$. Row i of A belongs to frame vector i of `c`,
and column j to frame vector j of `b`. A map array may also be ⊥.

A parameter `frame(F)` takes a frame declared at the family `F`. The frames
of an array are part of its type, so they are static. Its points are values,
which the program computes at run time.

Rules:

- A family with the `frame` representation must have exactly one parameter,
  of the form `object(K)`, and exactly the constraint `canonical(0)`.
  Otherwise it is an error (`E_TYPE`).
- Every implementation in the domain of `K` must have the `smooth_affine`
  representation. Otherwise it is an error (`E_TYPE`).
- A family with the `frame_vector` or `frame_covector` representation must
  have exactly one parameter, of the form `frame(F)`, and no constraints. A
  family with the `frame_map` representation must have exactly two
  parameters, both of the form `frame(…)`, and no constraints. Otherwise it is
  an error (`E_TYPE`). These three families may omit the clause
  `constraints(…)`.
- The path `F` of a parameter `frame(F)` must name a family with the `frame`
  representation. Otherwise it is an error (`E_TYPE`).
- The argument of a parameter `frame(F)` must be a path that names a frame
  declared at `F`. Otherwise the type is an error (`E_TYPE`). Two frames are
  different arguments, even when they have the same columns, so `Coords<b>`
  and `Coords<b2>` are different types for two such frames.

`std::geometry::frame` declares the families `Frame`, `Coords`, `CoCoords`
and `FrameMap` over the classification `CInfAffine` of
`std::geometry::smooth::affine`. It declares no frame and no frame primitive.
A program declares its frames and the primitives that name them, as it
declares its metrics and the `flat` and `sharp` primitives that name a metric.

Example, from
[`profile.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/frames/src/profile.vast):

```vast
{{#include ../../examples/packages/frames/src/profile.vast:frame-families}}
```

## Frame declarations

> **Syntax**
>
> ```text
> FrameDeclaration -> `indexed` `frame` IDENTIFIER `:` Path
>     `<` Path ( `,` Path )* `>` `=` FrameDefinition `;`
> FrameDefinition -> `coordinates` | FrameColumns ( `inverse` `=` FrameColumns )?
> FrameColumns -> `columns` `(` ( FrameColumn ( `,` FrameColumn )* `,`? )? `)`
> FrameColumn -> `(` ( Polynomial ( `,` Polynomial )* `,`? )? `)`
> ```

[Polynomial expressions](smooth-declarations.md#polynomial-expressions)
gives the production `Polynomial`.

`indexed frame b: F<X> = columns(c₁, …, cₙ);` declares the frame `b` of the
object `X` at the frame family `F`. Each parenthesized group cⱼ is frame
vector j: entry i of cⱼ is its component i, a polynomial expression in the
coordinates of `X`. The groups are the columns of $P_b$.
`indexed frame e: F<X> = coordinates;` declares the coordinate frame of `X`.

A frame is constant when every entry of its columns expands to a constant.
The kernel computes the inverse $Q_b$ of a constant frame. A frame that is not
constant declares the columns of $Q_b$ after `inverse =`, and the kernel
checks that $P_b\,Q_b = Q_b\,P_b = I$ holds as an identity of polynomials. So
the frame vectors of an accepted frame form a basis at every point of `X`.
The determinant of an accepted frame is a nonzero constant, because the
polynomial $\det P_b$ has the polynomial inverse $\det Q_b$. A frame whose
determinant depends on the point, such as the columns `(x, 0)` and `(0, 1)`
or the diagonal matrix diag(1 + x², 1), has no polynomial inverse, and no
declaration of it is valid.

A frame is a declaration. It is not a value, and no primitive produces a
value of the type `F<X>`.

Rules:

- The family must have the `frame` representation. Otherwise it is an error
  (`E_FRAME`).
- A frame must name exactly one object. Otherwise it is an error
  (`E_FRAME`).
- The object must be a smooth affine object, and the family must accept it.
  Otherwise it is an error (`E_FRAME`).
- `columns(…)` must have `dim X` columns, each of `dim X` entries.
  Otherwise it is an error (`E_FRAME`). The frame of a 0-dimensional object
  is `columns()`.
- The rules of [polynomial expressions](smooth-declarations.md#polynomial-expressions)
  apply to each entry. All entries of one frame, its inverse included, share
  one work budget.
- A constant frame must not declare `inverse = …`. Otherwise it is an error
  (`E_FRAME`), even when the declared inverse is correct.
- The columns of a constant frame must be linearly independent. A singular
  constant frame is an error (`E_FRAME`).
- Each entry of a constant frame must have at most `metricEntryBits` bits in
  its numerator and in its denominator, and the
  [matrix bound](smooth-declarations.md#metrics) of $P_b$ must be less than
  2^`metricMatrixBits` ([limits](../appendix/limits.md#frames)). Otherwise it
  is an error (`E_LIMIT`). The kernel checks both bounds before it computes
  the inverse, so a singular frame beyond them is an error (`E_LIMIT`) too.
- A frame that is not constant must declare its inverse with
  `inverse = columns(…)`. Otherwise it is an error (`E_FRAME`).
- The declared inverse must have the shape of the frame: `dim X` columns of
  `dim X` entries. Otherwise it is an error (`E_FRAME`).
- $P_b\,Q_b = I$ and $Q_b\,P_b = I$ must hold as identities of polynomials.
  Otherwise it is an error (`E_FRAME`). The products must stay within the
  term and work budgets that
  [the limits of frames](../appendix/limits.md#frames) give, which charge
  each product for the steps of its computation. Otherwise it is an error
  (`E_LIMIT`).
- `coordinates` declares no inverse: `coordinates inverse = …` is an error
  (`E_PARSE`). So is `inverse = …` before the columns, and a column that is
  not a parenthesized group.
- Any other word after `=` is an error (`E_TYPE`).
- A frame used as a value, or called, is an error (`E_TYPE`).

> **Implementation note.** The kernel computes the inverse of a constant
> frame with the procedure that inverts a Gram matrix, and it checks both
> products again before it accepts the frame. A request of protocol 9 holds
> the columns of a frame and the declared inverse of a frame that is not
> constant, and never the inverse of a constant frame: a request with one is
> an error (`E_FRAME`), even when the inverse is correct. The declaration
> audit checks every frame again (`FrameDeclarations.checkFrame`). The oracle
> theorem `VastitasOracle.FrameDeclarations.frame_sound` states that the
> matrices of an accepted frame are inverse at every point, and the bridge
> theorem `VastitasBridge.Differential.frame_realBasis` that the frame vectors
> form a basis of ℝⁿ at every real point.

Example, from
[`main.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/frames/src/main.vast):

```vast
{{#include ../../examples/packages/frames/src/main.vast:frames}}
```

$P_r$ at the point (x, y) has the columns (1, 0) and (x, 1), and its inverse
$Q_r$ has the columns (1, 0) and (−x, 1).

The following frame is constant and declares its inverse:

```vast
{{#include ../../examples/reject/packages/frame-constant-inverse/main.vast:declaration}}
```

```text
{{#include ../../examples/reject/packages/frame-constant-inverse.stderr}}
```

The columns of the following constant frame are linearly dependent:

```vast
{{#include ../../examples/reject/packages/frame-singular/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/frame-singular.stderr}}
```

The following frame depends on the point and declares no inverse:

```vast
{{#include ../../examples/reject/packages/frame-missing-inverse/main.vast:declaration}}
```

```text
{{#include ../../examples/reject/packages/frame-missing-inverse.stderr}}
```

The inverse that the following frame declares is not its inverse:

```vast
{{#include ../../examples/reject/packages/frame-wrong-inverse/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/frame-wrong-inverse.stderr}}
```

## Encoding and decoding

> **Syntax**
>
> ```text
> FrameBinding -> FrameEncodingBinding | FrameMapBinding
>     | FrameContractionBinding | FrameObservationBinding
> FrameEncodingBinding -> `frame_encode` `(` Path `,` Path `,` `frame` `=` Path `)`
>     | `frame_decode` `(` Path `,` Path `,` `frame` `=` Path `)`
>     | `frame_vector` `(` Path `,` Path `,` `frame` `=` Path `)`
> ```

`indexed primitive p = binding;` declares a function `p` whose operands and
result the binding fixes, as [Primitives](../indexed-source.md#primitives)
says. `FrameBinding` gives the bindings of this chapter. In the tables of
this chapter, `S` is a family with the `smooth` representation, and `Z` is a
0-dimensional smooth affine object, so that a value of `S<Z, X>` is a
[rational point](smooth-declarations.md#smooth-map-primitives) of `X`. `b` is
a frame of `X`, a smooth affine object of dimension n. In the table below,
`F` is a tangent or cotangent family and `C` is a family of frame arrays of
the same variance: `C` holds the arrays of vectors when `F` is a tangent
family, and the arrays of covectors when `F` is a cotangent family.

| Binding | Operands | Result | Value |
| --- | --- | --- | --- |
| `frame_encode(F, C, frame = b)` | `F<X>` | `C<b>` | The array of the vector v at p, $Q_b(p)\,v$, or of the covector α at p, $P_b(p)^\top \alpha$ |
| `frame_decode(C, F, frame = b)` | `C<b>` | `F<X>` | The vector $P_b(p)\,a$ or the covector $Q_b(p)^\top a$ of the array a at p |
| `frame_vector(C, S, frame = b)` | `S<Z, X>`, then one operand of type `Int` for each frame vector of `b` | `C<b>` | The array with these components at the point |

All three keep the point. `frame_encode` and `frame_decode` send ⊥ to ⊥.
Decoding after encoding gives the fiber again, and encoding after decoding
gives the array again. In the coordinate frame, the array of a fiber has the
components of the fiber.

Rules:

- The path after `frame =` must name a frame declaration. Otherwise it is an
  error (`E_FRAME`). A missing `frame =` is an error (`E_PARSE`).
- The fiber family `F` of `frame_encode` and `frame_decode` must have the
  `tangent` or `cotangent` representation, and the array family `C` the
  `frame_vector` or `frame_covector` representation. Otherwise it is an
  error (`E_TYPE`).
- `F` and `C` must both hold vectors, or both covectors. A tangent family
  with a `frame_covector` family, or a cotangent family with a `frame_vector`
  family, is an error (`E_FRAME`).
- The array family of `frame_vector` must have the `frame_vector` or
  `frame_covector` representation, and `S` the `smooth` representation.
  Otherwise it is an error (`E_TYPE`). The array holds vectors or covectors
  as its family says.
- The rules of [operand checks](#operand-checks) apply.

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/frames/src/main.vast:encoding}}
```

`main` builds these values:

```vast
{{#include ../../examples/packages/frames/src/main.vast:values}}
```

At p = (1, 2), the vector v = (3, 2) has the array (2, 1) in `b`, and
`dec_b(w)` is v again. The covector df = (2, 1) has the array (2, 4) in the
coframe dual to `b`, and their pairing is 8 in both forms:
2 · 2 + 4 · 1 = 2 · 3 + 1 · 2. `enc_e(v)` has the components (3, 2) of v.
`in_r(p, 1, 2)` is the array (1, 2) in `r`, which decodes to
1 · (1, 0) + 2 · (1, 1) = (3, 2), the vector v.

The following binding relates a family of vectors to a family of covector
arrays:

```vast
{{#include ../../examples/reject/packages/frame-encode-variance/main.vast:declaration}}
```

```text
{{#include ../../examples/reject/packages/frame-encode-variance.stderr}}
```

## Map arrays and transitions

> **Syntax**
>
> ```text
> FrameMapBinding -> `frame_matrix` `(` Path `,` Path `,` `source` `=` Path `,` `target` `=` Path `)`
>     | `frame_transition` `(` Path `,` Path `,` `source` `=` Path `,` `target` `=` Path `)`
> ```

In the table, `M` is a family with the `frame_map` representation. `b` is a
frame of `X`, and `c` is a frame of `Y` for `frame_matrix` and a frame of `X`
for `frame_transition`. F is the map of the first operand, p is the point,
and J(p) is the Jacobian of F at p.

| Binding | Operands | Result | Value |
| --- | --- | --- | --- |
| `frame_matrix(S, M, source = b, target = c)` | `S<X, Y>`, `S<Z, X>` | `M<b, c>` | The map array of the tangent map of F at p, from `b` at p to `c` at F(p): $Q_c(F(p))\,J(p)\,P_b(p)$ |
| `frame_transition(S, M, source = b, target = c)` | `S<Z, X>` | `M<b, c>` | The transition from `b` to `c` at p: $Q_c(p)\,P_b(p)$, from p to p |

The **transition** from a frame `b` to a frame `c` of one object, at a point
p, is the map array of the identity of the tangent fiber at p. It sends the
array of a vector in `b` to its array in `c`. The transition from `b` to `b`
is the identity, the transition from `b` to `c` followed by the transition
from `c` to `d` is the transition from `b` to `d`, and the transitions from
`b` to `c` and from `c` to `b` are inverse. A map array in other frames
follows from the transitions: for frames `b` and `b′` of `X` and `c` and `c′`
of `Y`, the map array of F at p from `b′` to `c′` is the transition from `c`
to `c′` at F(p), after the map array from `b` to `c`, after the transition
from `b′` to `b` at p. Both map arrays stand for one linear map. The map
array of a composite G ∘ F at p is the map array of G at F(p) after the map
array of F at p, as [contraction in frames](#contraction-in-frames)
composes them.

Rules:

- `S` must have the `smooth` representation, and `M` the `frame_map`
  representation. Otherwise it is an error (`E_TYPE`).
- The paths after `source =` and `target =` must name frame declarations.
  Otherwise it is an error (`E_FRAME`). A missing `source =` or `target =` is
  an error (`E_PARSE`).
- The two frames of `frame_transition` must be frames of one object.
  Otherwise the declaration is an error (`E_ENDPOINT`), whose message names
  both frames and both objects.
- The rules of [operand checks](#operand-checks) apply.

> **Implementation note.** `frame_matrix` computes row i of the map array
> from row i of $Q_c(F(p))$, a covector at F(p). It pulls that covector back
> along F at p and encodes the result in `b`. The pullback is the recomputing
> reverse pass of a `recomputed`
> [pullback](smooth-declarations.md#reverse-pass-primitives), on the program
> value that checked Core builds. The call runs one reverse pass for each row
> of the result. It expands no composite and forms no Jacobian, and no frame
> binding has a derivative rule of its own. No limit bounds the size of the
> rational entries of a map array in an executable. The oracle theorems
> `VastitasOracle.FrameCore.core_frame_matrix` and
> `core_frame_chain_rule_terms` state the value of an accepted call and the
> rule for composites, `VastitasOracle.FrameRuntime.transition_laws` the laws
> of transitions, and `change_of_frames` the change of frames of a map array.
> The bridge theorem
> `VastitasBridge.Differential.frameMatrix_eq_toMatrix_fderiv` identifies a
> map array with the matrix of the derivative of the map in the two bases.

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/frames/src/main.vast:maps}}
```

For f(x, y) = x² + y at p = (1, 2), J(p) = (2, 1) and f(p) = 3. With the
frame `l` of the line, whose frame vector is 2, `matrix_bl(f(), p)` is the
map array (1, 2) and `matrix_cl(f(), p)` is the map array (5/2, 3/2). The two
arrays differ, and both stand for one map. `move_bc(p)` is the transition with
the rows (1, −1) and (−1, 3), and `matrix_cl(f(), p)` after `move_bc(p)` is
`matrix_bl(f(), p)`.

The following transition names frames of two objects:

```vast
{{#include ../../examples/reject/packages/frame-other-object/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/frame-other-object.stderr}}
```

## Contraction in frames

> **Syntax**
>
> ```text
> FrameContractionBinding -> `frame_apply` `(` Path `,` Path `)`
>     | `frame_coapply` `(` Path `,` Path `)`
>     | `frame_compose` `(` Path `)`
>     | `frame_pairing` `(` Path `,` Path `)`
> ```

In the table, `M` is a family with the `frame_map` representation, `C` a
family with the `frame_vector` representation and `D` a family with the
`frame_covector` representation. A is the matrix of a map array from p to q.

| Binding | Operands | Result | Value |
| --- | --- | --- | --- |
| `frame_apply(M, C)` | `M<b, c>`, `C<b>` | `C<c>` | The array A a at q of the array a at p; ⊥ unless the array lies over p |
| `frame_coapply(M, D)` | `M<b, c>`, `D<c>` | `D<b>` | The array $A^\top \beta$ at p of the array β at q; ⊥ unless the array lies over q |
| `frame_compose(M)` | `M<c, d>`, `M<b, c>` | `M<b, d>` | The first map array after the second; ⊥ unless the target point of the second is the source point of the first |
| `frame_pairing(D, C)` | `D<b>`, `C<b>` | `Pair<Int>` | The pairing $\sum_i \beta_i a_i$, reduced; `(0, 0)` for ⊥ or for arrays at different points |

The frames of the operands are static, and the points are checked when the
program runs. `frame_apply`, `frame_coapply` and `frame_compose` send ⊥ to ⊥.
The pairing of two arrays in one frame is the pairing of the vector and the
covector that they decode to, in every frame. Coapplying the map array of F
at p to the array of a covector η at F(p) gives the array of the
[cotangent pullback](smooth-declarations.md#reverse-pass-primitives) of η
along F at p. No binding of this chapter consults a metric.

Rules:

- `M` must have the `frame_map` representation, `C` the `frame_vector`
  representation and `D` the `frame_covector` representation. Otherwise it
  is an error (`E_TYPE`).
- The rules of [operand checks](#operand-checks) apply. In particular, an
  array in another frame than the source frame of `frame_apply`, or than the
  target frame of `frame_coapply`, two map arrays whose middle frames differ
  and two arrays of `frame_pairing` in different frames are errors
  (`E_ENDPOINT`).

> **Implementation note.** The kernel checks the frames of each call before
> code generation, and the generated code checks the points. The oracle
> theorems `VastitasOracle.FrameRuntime.pairing_invariant`,
> `coapply_eq_pullback` and `contraction_endpoints` state the pairing in
> frames, the pullback in frames and the points of a contraction.

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/frames/src/main.vast:contraction}}
```

`apply_map(matrix_bl(f(), p), w)` is the array 4 at the point 3 of the line:
the vector 8 there, the image of v. `coapply_map(matrix_bl(f(), p),
coenc_l(dt))` is the array (2, 4) of df in `b`, the pullback of dt along f at
p. `apply_map(move_bc(p), …)` of an array at the point (0, 0) is ⊥.

In this program the transition from `b` takes arrays in `b`, and the operand
is an array in `r`:

```vast
{{#include ../../examples/reject/packages/frame-apply-frame/main.vast:program}}
```

```text
{{#include ../../examples/reject/packages/frame-apply-frame.stderr}}
```

## Components, entries and equality

> **Syntax**
>
> ```text
> FrameObservationBinding -> `frame_component` `(` Path `,` INTEGER_LITERAL `)`
>     | `frame_entry` `(` Path `,` INTEGER_LITERAL `,` INTEGER_LITERAL `)`
>     | `frame_equal` `(` Path `)`
>     | `frame_at` `(` Path `,` Path `)`
> ```

In the table, `C` is a family of frame arrays, `M` a family with the
`frame_map` representation, and `G` one of them.

| Binding | Operands | Result | Value |
| --- | --- | --- | --- |
| `frame_component(C, i)` | `C<b>` | `Pair<Int>` | Component i as a reduced numerator and a positive denominator; `(0, 0)` for ⊥ |
| `frame_entry(M, i, j)` | `M<b, c>` | `Pair<Int>` | The entry in row i and column j, as a reduced fraction; `(0, 0)` for ⊥ |
| `frame_equal(G)` | Two values of one type of `G` | `Bool` | Whether the points and the components or entries are equal; ⊥ equals nothing, itself included |
| `frame_at(C, S)` | `C<b>`, `S<Z, X>` | `Bool` | Whether the array lies over the point; `false` for ⊥ |

Components and entries count from 0. A component or an entry that is zero
reads `(0, 1)`, and no rational number reads `(0, 0)`.

Rules:

- `C` must have the `frame_vector` or `frame_covector` representation, `M`
  the `frame_map` representation, `G` one of the three, and `S` the
  `smooth` representation. Otherwise it is an error (`E_TYPE`).
- i and j must be unsigned integer literals (`E_PARSE`) with at most 64
  digits (`E_LIMIT`).
- In a call of `frame_component`, i must be less than the dimension of the
  object of the frame of the array. In a call of `frame_entry`, i must be
  less than the dimension of the object of the target frame, and j less than
  the dimension of the object of the source frame. Otherwise the call is an
  error (`E_ENDPOINT`). The check is static.
- The rules of [operand checks](#operand-checks) apply.

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/frames/src/main.vast:observations}}
```

`first(w)` reads `(2, 1)`, and `entry_01(matrix_cl(f(), p))` reads `(3, 2)`.
`over(apply_map(matrix_bl(f(), p), w), line_at(3))` is `true`.

The components of an array in a frame of the plane are 0 and 1:

```vast
{{#include ../../examples/reject/packages/frame-component-bound/main.vast:program}}
```

```text
{{#include ../../examples/reject/packages/frame-component-bound.stderr}}
```

## Operand checks

These rules apply to every call of a primitive of this chapter.

Rules:

- A call must have the number of operands that the binding fixes. Otherwise
  it is an error (`E_ARITY`).
- An operand that the table of its binding gives as `Int` must have type
  `Int`. Otherwise it is an error (`E_TYPE`).
- A value that is not a value of a family, such as an `Int`, in the place of
  a fiber, an array, a map array, a map or a point is an error (`E_TYPE`).
  The point of a `frame_vector` primitive is the exception: such a value
  there is an error (`E_ENDPOINT`), as for the point of a `fiber_vector`
  primitive.
- Any other operand from the wrong family, in the wrong frame or over the
  wrong object is an error (`E_ENDPOINT`). Examples are a fiber in the place
  of a frame array, a covector array in the place of a vector array, an
  array in another frame than the frame that the binding or the map array
  names, two map arrays whose middle frames differ, a fiber over another
  object than the object of the frame, and a point of another object.
- The two operands of `frame_equal` must have one type. Otherwise it is an
  error (`E_ENDPOINT`).
- The source of a point must be a 0-dimensional smooth affine object.
  Otherwise it is an error (`E_ENDPOINT`).
- The type of a call names the frames of its result. A binding, a parameter
  or a result of another type is an error (`E_TYPE`), as for every value.

> **Implementation note.** The message of an `E_ENDPOINT` names the first
> failed check in most cases: the operand, the frame, object or bound that
> the binding expects, and the one supplied. In other cases, such as a fiber
> in the place of an array or two operands of `frame_equal` in different
> frames, it lists the types of the operands.

In this program `same_coords` compares an array in `b` with an array in
`b2`, two frames of one object:

```vast
{{#include ../../examples/reject/packages/frame-other-frame/main.vast:program}}
```

```text
{{#include ../../examples/reject/packages/frame-other-frame.stderr}}
```

## The Gram matrix in a frame

No frame binding reads a metric. The Gram matrix of a
[metric](smooth-declarations.md#metrics) g with the Gram matrix G, in a frame
`b` at a point p, is $P_b(p)^\top G\,P_b(p)$. A program computes it from
`flat`: it decodes the array of frame vector j, applies `flat`, and encodes
the covector in `b`. The result is column j of the Gram matrix in `b`. For a
second frame `c` with the transition T from `b` to `c`, the Gram matrices
satisfy $G_b = T^\top G_c\,T$. With nondegenerate evidence, `sharp` with
encoding and decoding gives the inverse of the Gram matrix in `b` in the same
way.

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/frames/src/main.vast:gram}}
```

The metric `Skew` has the Gram matrix ((2, 1), (1, 1)). Its Gram matrix in
`b` has the columns (2, 4) and (4, 10).

> **Implementation note.** The oracle theorems
> `VastitasOracle.FrameRuntime.gram_in_frame` and `frameGram_transport`, and
> the bridge theorems `VastitasBridge.Differential.gram_transport_frame` and
> `posDef_gram_in_frame`, state the Gram matrix in a frame and its transport.
> The checking and the values of `flat`, `sharp` and the metric declarations
> do not depend on frame declarations.

## Scope of frames

Frames cover global frames of the tangent fibers of a smooth affine object:
frame vectors whose components are polynomials with rational coefficients
and whose determinant is a nonzero constant. The coframes are their duals. A
program declares each frame, and each primitive names its frames, so the
library has no primitive that is generic over frames. A function body
declares no frame. Frame arrays and map arrays hold rational numbers. They
are not storage, and they are no values of the spaces of
[Numerical maps](../linalg/maps-and-gemm.md). The language has no primitive
that pushes a vector forward along a map, apart from `frame_apply` on a map
array. [Physical dimensions](physical-dimensions.md) gives physical
meanings to the coordinates of an object and to its metrics, and gives none
to frames.
