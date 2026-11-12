# Smooth affine declarations

This chapter defines the declarations of smooth real affine geometry: smooth
affine objects, smooth maps between them, tangent and cotangent fibers,
tapes, metrics and metric evidence, and the primitive bindings that act on
them. A **smooth affine object** is the real affine space ℝⁿ with n named
coordinates. A **smooth map** between two smooth affine objects is a
polynomial map with rational coefficients.
The general rules of `indexed` declarations, such as visibility, names,
markers and classifications, are in
[Indexed declarations](../indexed-source.md).
[Notation](notation.md) explains the Syntax blocks, and the
[glossary](../appendix/glossary.md) defines the terms.

The examples quote the tested package
[`examples/packages/smooth-geometry/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/smooth-geometry),
whose executable prints `42`. Each rejected program is a package on the
profile of the standard library. It appears with the diagnostic that the
compiler prints for it.

The declarations of this chapter are the forms of `SmoothDeclaration`, and
they share the production `CoordinateName`:

> **Syntax**
>
> ```text
> SmoothDeclaration -> SmoothImplementation | SmoothFamily | AffineSpaceDeclaration
>     | MorphismDeclaration | MetricDeclaration | EvidenceDeclaration
> CoordinateName -> IDENTIFIER ( `::` IDENTIFIER )*
> ```

A [`Path`](names-and-paths.md) names a declaration in scope, as in a `use`
declaration. A `CoordinateName` names a coordinate of an object. Each
declaration of this chapter is an [item](items.md): `SmoothDeclaration` is one
form of [`IndexedDeclaration`](../indexed-source.md). So is
`PrimitiveDeclaration`, whose bindings in this chapter are the forms of
`SmoothBinding`. `pub` before a declaration makes it visible outside its
module.

## The smooth profile

> **Syntax**
>
> ```text
> SmoothImplementation -> `indexed` `implementation` IDENTIFIER
>     `(` Path `,` `smooth_affine` `)` `capabilities` `(` Capabilities? `)` `;`
> SmoothFamily -> `indexed` `family` IDENTIFIER `(` Parameters? `)`
>     `=` SmoothRepresentation `constraints` `(` Constraints? `)` `;`
> SmoothRepresentation -> `smooth` | `cotangent` | `tangent` | `tape` | `metric_form`
> ```

[Implementations](../indexed-source.md#implementations) gives the production
`Capabilities`, and [Families](../indexed-source.md#families) gives
`Parameters` and `Constraints`.

An implementation with the `smooth_affine` representation backs the smooth
affine objects. A classification whose domain lists such an implementation,
such as `CInfAffine` below, is the classification over which the families of
this chapter range. The representation of a family says which values its
indexed types have. The table names the families of the example below:

| Representation | Indexed type | Values |
| --- | --- | --- |
| `smooth` | `Smooth<X, Y>` | The smooth maps from `X` to `Y` |
| `cotangent` | `Cotangent<X>` | The covectors at the points of `X`, and the [failure value](#fiber-primitives) |
| `tangent` | `Tangent<X>` | The vectors at the points of `X`, and the failure value |
| `tape` | `Tape<X, Y>` | The [tapes](#reverse-pass-primitives) of the smooth maps from `X` to `Y` |
| `metric_form` | `MetricForm<X>` | None. An [`indexed metric`](#metrics) declaration names the type |

The `token`, `point` and `morphism` representations are in
[Families](../indexed-source.md#families), and the `relative` representation
is in [The presented profile](../affine-geometry.md#the-presented-profile).

The constraint `canonical(i)` holds for an indexed type when its argument `i`
is a declared smooth affine object. It compares declarations, never
dimensions. Only a declared object satisfies it. A parameter and a local
object, such as one that `Affine(CInfReal, n)` builds in a function body,
never do.

The standard library declares one smooth profile.
`std::geometry::smooth::affine` declares the implementation `SmoothR`, the
classification `CInfAffine`, the families `Smooth`, `Tape`, `Tangent` and
`Cotangent` and the objects `Pt` and `Line`. Its primitives are
`compose_smooth`, `composite`, `same_smooth`, `line_at`, `lies_over`,
`tangent_over`, `same_covector`, `same_vector` and `pairing`.
`std::geometry::metric` declares the family `MetricForm`, and
`std::differential` declares the primitives `pullback`, `differential`,
`linearize` and `backward`. A program may use these declarations or declare
a profile of its own. Each declaration is a distinct object or family, so a
program's own `Affine(1)[t]` is not the library's `Line`.

Rules:

- A `smooth_affine` implementation must list no capabilities. Otherwise it is
  an error (`E_TYPE`).
- A marker that a `smooth_affine` implementation names must not also be the
  marker of an implementation with the coefficient kind `complex`. Otherwise
  it is an error (`E_TYPE`). A `smooth_affine` implementation counts as
  `real`, as
  [Linear implementations](../linalg/maps-and-gemm.md#linear-implementations)
  says.
- A family with the `smooth` or `tape` representation must have exactly two
  parameters, both of the form `object(C)`, and exactly the constraints
  `canonical(0), canonical(1)`, in this order. Otherwise it is an error
  (`E_TYPE`).
- A family with the `cotangent`, `tangent` or `metric_form` representation
  must have exactly one parameter, of the form `object(C)`, and exactly the
  constraint `canonical(0)`. Otherwise it is an error (`E_TYPE`).
- Every implementation in the domain of each `C` must have the `smooth_affine`
  representation. Otherwise it is an error (`E_TYPE`). In particular, these
  families never range over presented affine objects or descriptor objects.
- The position of `canonical(i)` must be the position of an `object(…)`
  parameter. Otherwise it is an error (`E_TYPE`). A family with the `token`
  representation may state the constraint.
- A type whose argument fails a `canonical` constraint is an error
  (`E_TYPE`). An example is `Smooth<Line, QLine>` for a presented affine
  object `QLine`.

Example, from
[`profile.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/smooth-geometry/src/profile.vast):

```vast
{{#include ../../examples/packages/smooth-geometry/src/profile.vast:profile}}
```

In the following function on the profile of the standard library, `X` is an
object of the classification `CInfAffine`, and it is a parameter:

```vast
{{#include ../../examples/reject/packages/smooth-parameter-object/main.vast:function}}
```

```text
{{#include ../../examples/reject/packages/smooth-parameter-object.stderr}}
```

## Smooth affine objects

> **Syntax**
>
> ```text
> AffineSpaceDeclaration -> `indexed` `affine` IDENTIFIER `(` Path `)`
>     `=` AffineSpace `;`
> AffineSpace -> `Affine` `(` ( Path `,` )? INTEGER_LITERAL `)` `[` Coordinates? `]`
> Coordinates -> IDENTIFIER ( `,` IDENTIFIER )* `,`?
> ```

`indexed affine X(Impl) = Affine(n)[c₁, …, cₙ];` declares a smooth affine
object under the implementation `Impl`: the real affine space ℝⁿ with the
coordinates `c₁, …, cₙ`. The number `n` is the dimension of the object. Each
declaration is one object with its own
[nominal identity](../appendix/glossary.md#nominal-identity). Two
declarations with the same dimension and the same coordinates are different
objects, and no rule identifies them.

`Affine(K, n)[g₁, …, gₙ]`, with a base `K`, is another spelling of
`spec[g₁, …, gₙ] over K`, the declaration of a presented affine object. The
rules of [presented affine objects](../affine-geometry.md#presented-affine-objects)
apply to it. [Presented affine declarations](../affine-geometry.md) gives
the other forms of `indexed affine`: `spec[…]`, `fiber(…)` and
`localize(…)`.

Rules:

- The dimension must be an unsigned integer literal. Otherwise it is an error
  (`E_PARSE`).
- The dimension must have at most 64 decimal digits and must be at most 16.
  Otherwise it is an error (`E_LIMIT`).
- `Affine(n)[…]` must name an implementation with the `smooth_affine`
  representation. A presented or descriptor implementation is an error
  (`E_SMOOTH`).
- `Affine(n)[…]` must list exactly `n` coordinates, and they must be distinct.
  Otherwise it is an error (`E_SMOOTH`).
- `Affine(K, n)[…]` must list exactly `n` coordinates. Otherwise it is an
  error (`E_AFFINE_COORDINATE`).
- `spec[…]`, `fiber(…)` and `localize(…)`, and therefore `Affine(K, n)[…]`,
  under a `smooth_affine` implementation are an error (`E_SMOOTH`).
- An `indexed global` under a `smooth_affine` implementation is an error
  (`E_SMOOTH`). Every smooth affine object is an `Affine(n)[…]` declaration.
- In a function body, `Affine(QQ, n)` and `Affine(CInfReal, n)` keep their
  meaning in the [geometric core](geometric-types.md). They build
  descriptor objects, not smooth affine objects.

Example, from `profile.vast`:

```vast
{{#include ../../examples/packages/smooth-geometry/src/profile.vast:objects}}
```

`Pt` is the point ℝ⁰, `Line` is the line with the coordinate `t`, and `Plane`
is the plane with the coordinates `x` and `y`.

The following declaration states the dimension 2 and lists one coordinate:

```vast
{{#include ../../examples/reject/packages/smooth-coordinate-count/main.vast:declaration}}
```

```text
{{#include ../../examples/reject/packages/smooth-coordinate-count.stderr}}
```

## Polynomial expressions

> **Syntax**
>
> ```text
> Polynomial -> PolynomialTerm ( ( `+` | `-` ) PolynomialTerm )*
> PolynomialTerm -> PolynomialFactor ( `*` PolynomialFactor )*
> PolynomialFactor -> `-` PolynomialFactor | PolynomialAtom ( `^` INTEGER_LITERAL )?
> PolynomialAtom -> INTEGER_LITERAL | `(` Polynomial `)` | Fraction | CoordinateName
> Fraction -> `frac` `(` `-`? INTEGER_LITERAL `,` INTEGER_LITERAL `)`
> ```

A **polynomial expression** denotes a polynomial with rational coefficients
in the coordinates of one object. The images of a smooth map are polynomial
expressions in the coordinates of its source, and the entries of a
[Gram matrix](#metrics) are polynomial expressions in the coordinates of the
object of the metric.
[Presented affine declarations](../affine-geometry.md) write relations and
images as polynomial expressions too.

`frac(n, d)` is the fraction n/d. `frac` followed by `(` starts a fraction,
and any other `frac` is a coordinate name. Unary `-` applies to the whole
factor, so `-x^2` is −(x²).

Rules:

- A literal must have at most 64 decimal digits. Otherwise it is an error
  (`E_LIMIT`).
- An expression must have at most 64 levels. Otherwise it is an error
  (`E_LIMIT`). A literal, a fraction or a coordinate name is one level. A
  sum, a product, a negation or a power is one level more than its deepest
  operand. A chain of `+` and `-` is one sum, in which `- p` is the negation
  of `p`, and a chain of `*` is one product. Parentheses add no level. For
  example, `1 - x*2` has four levels: the sum, the negation, the product and
  `x`.
- Parentheses and unary `-` signs must nest at most 63 deep, counted
  together. Otherwise it is an error (`E_LIMIT`).
- Exponents and degrees must be at most 16, and the expanded polynomial must
  stay within the term and work budgets of
  [exact affine algebra](../appendix/limits.md#exact-affine-algebra).
  Otherwise it is an error (`E_LIMIT`).
- A fraction with a zero denominator is an error (`E_AFFINE_COORDINATE`).
- A coordinate name that the object does not have is an error
  (`E_AFFINE_COORDINATE`).

Example, from
[`main.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/smooth-geometry/src/main.vast):

```vast
{{#include ../../examples/packages/smooth-geometry/src/main.vast:polynomials}}
```

`cubic` is the map t ↦ t³/2 − (t + 1)², which sends 2 to −5. `negSquare` is
the map t ↦ −t², which sends 3 to −9.

The following image has the exponent 17:

```vast
{{#include ../../examples/reject/packages/smooth-degree/main.vast:declaration}}
```

```text
{{#include ../../examples/reject/packages/smooth-degree.stderr}}
```

## Smooth maps

> **Syntax**
>
> ```text
> MorphismDeclaration -> `indexed` `morphism` IDENTIFIER `:` Path
>     `<` Path ( `,` Path )* `>` `=` MorphismDefinition `;`
> MorphismDefinition -> `pullback` `(` ImageBindings? `)` | `identity`
>     | `structure` | `first` | `second` | `restrict` `(` Path `)`
> ImageBindings -> ImageBinding ( `,` ImageBinding )* `,`?
> ImageBinding -> CoordinateName `->` Polynomial
> ```

A morphism declared at a family with the `smooth` representation is a smooth
map. `indexed morphism f: S<X, Y> = pullback(y₁ -> p₁, …, yₘ -> pₘ);` gives
each coordinate `yᵢ` of the target `Y` its image `pᵢ`, a polynomial
expression in the coordinates of the source `X`. The declaration denotes the
polynomial map x ↦ (p₁(x), …, pₘ(x)). `identity` is the identity map of `X`.
The declaration defines a function of no operands: `f()` is the map, of type
`S<X, Y>`. The definitions `structure`, `first`, `second` and `restrict(…)`
belong to [morphisms over a base](../affine-geometry.md#morphisms-over-a-base).

Rules:

- A smooth map must name exactly two objects, its source and its target.
  Otherwise it is an error (`E_SMOOTH`).
- Both objects must be smooth affine objects. Otherwise it is an error
  (`E_SMOOTH`).
- `pullback(…)` must give each coordinate of the target exactly one image. A
  missing, repeated or unknown coordinate of the target is an error
  (`E_AFFINE_COORDINATE`).
- Each image must be a polynomial expression in the coordinates of the
  source. Any other name in an image, including a coordinate of the target,
  is an error (`E_AFFINE_COORDINATE`). The rules of
  [polynomial expressions](#polynomial-expressions) apply to each image.
- A declaration may list the images in any order. The map holds them in the
  order of the coordinates of the target.
- `identity` must have one object as its source and its target. Otherwise it
  is an error (`E_SMOOTH`).
- `structure`, `first`, `second` and `restrict(…)` at a family with the
  `smooth` representation are an error (`E_SMOOTH`).
- Any other word after `=` is an error (`E_TYPE`).
- A call of the declared function with operands is an error (`E_ARITY`).

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/smooth-geometry/src/main.vast:maps}}
```

`f` is the map t ↦ (t, t²), and `g` is the map (x, y) ↦ x² + y. `shear` and
`shearYFirst` are one map: (x, y) ↦ (x + y, y).

The following declaration names the coordinate `x` of its target in an image:

```vast
{{#include ../../examples/reject/packages/smooth-target-coordinate/main.vast:declaration}}
```

```text
{{#include ../../examples/reject/packages/smooth-target-coordinate.stderr}}
```

## Smooth map primitives

> **Syntax**
>
> ```text
> SmoothBinding -> SmoothMapBinding | FiberBinding | ReverseBinding | MetricBinding
> SmoothMapBinding -> `smooth_compose` `(` Path `)`
>     | `smooth_equal` `(` Path `)`
>     | `smooth_composite` `(` Path `)`
>     | `smooth_int_point` `(` Path `,` Path `,` Path `)`
> ```

`indexed primitive p = binding;` declares a function `p` whose operands and
result the binding fixes, as [Primitives](../indexed-source.md#primitives)
says. `SmoothBinding` gives the bindings of this chapter. In the tables of
this chapter, `S` is a family with the `smooth` representation, and `P` is a
0-dimensional smooth affine object. A **rational point** of `X` is a value of
`S<P, X>`: a smooth map from `P` to `X`. Its images are constants, the
coordinates of the point. This chapter calls it a point of `X`. The bindings
for `point` and `morphism` families are in
[Primitives](../indexed-source.md#primitives), and the `relative_*` bindings
are in [Morphism primitives](../affine-geometry.md#morphism-primitives).

| Binding | Operands | Result | Value |
| --- | --- | --- | --- |
| `smooth_compose(S)` | `S<Y, Z>`, `S<X, Y>` | `S<X, Z>` | The first map after the second |
| `smooth_equal(S)` | `S<X, Y>`, `S<X, Y>` | `Bool` | Whether the two maps are the same polynomial map |
| `smooth_composite(S)` | `S<X, Y>` | `S<X, Y>` | The same map, as one map |
| `smooth_int_point(S, X, P)` | One operand of type `Int` for each coordinate of `X` | `S<P, X>` | The point of `X` with these coordinates, in coordinate order |

`smooth_compose` composes in the written order: its first operand is applied
after its second. With a point as its second operand, it gives the image of
the point.

Rules:

- The family `S` must have the `smooth` representation. Otherwise it is an
  error (`E_TYPE`).
- `smooth_int_point(S, X, P)` must name a smooth affine object `X` and a
  0-dimensional smooth affine object `P`. Otherwise it is an error
  (`E_SMOOTH`).
- The rules of [operand checks](#operand-checks) apply.

> **Implementation note.** `smooth_compose` builds a program node and never
> expands the composite. `smooth_equal` and `smooth_composite` expand it at
> run time, without a budget.

Example, from `profile.vast`:

```vast
{{#include ../../examples/packages/smooth-geometry/src/profile.vast:map-primitives}}
```

`compose(g(), f())` is g after f, the map t ↦ 2t². `line_at(3)` is the point
3 of `Line`, and `compose(f(), line_at(3))` is the point (3, 9) of `Plane`.

The following binding names `Line` as the source of its points:

```vast
{{#include ../../examples/reject/packages/smooth-point-object/main.vast:declaration}}
```

```text
{{#include ../../examples/reject/packages/smooth-point-object.stderr}}
```

## Fiber primitives

> **Syntax**
>
> ```text
> FiberBinding -> `fiber_vector` `(` Path `,` Path `,` Path `)`
>     | `fiber_at` `(` Path `,` Path `)`
>     | `fiber_equal` `(` Path `)`
>     | `fiber_component` `(` Path `,` Path `,` CoordinateName `)`
>     | `fiber_pairing` `(` Path `,` Path `)`
> ```

A tangent family is a family with the `tangent` representation, and a
cotangent family is one with the `cotangent` representation. A
**tangent or cotangent fiber** is a value of a type `F<X>` of such a family
`F`. It is a vector or a covector at a point of `X`, with one rational
component for each coordinate of `X`, in the coordinate frame or coframe. It
may also be the **failure value** ⊥, which stands for no vector and no
covector. ⊥ lies over no point. This chapter calls a tangent or cotangent
fiber a fiber. In the table, `F` is a cotangent or tangent family, `C` a
cotangent family and `T` a tangent family.

| Binding | Operands | Result | Value |
| --- | --- | --- | --- |
| `fiber_vector(F, S, X)` | `S<P, X>`, then one operand of type `Int` for each coordinate of `X` | `F<X>` | The covector or vector at the point with these components |
| `fiber_at(F, S)` | `F<X>`, `S<P, X>` | `Bool` | Whether the fiber lies over the point; `false` for ⊥ |
| `fiber_equal(F)` | `F<X>`, `F<X>` | `Bool` | Whether the points and the components are equal; ⊥ equals nothing, itself included |
| `fiber_component(F, X, c)` | `F<X>` | `Pair<Int>` | The component at `c` as a reduced numerator and a positive denominator; `(0, 0)` for ⊥ |
| `fiber_pairing(C, T)` | `C<X>`, `T<X>` | `Pair<Int>` | The pairing α(v) = Σᵢ αᵢvᵢ, reduced; `(0, 0)` for ⊥ or for fibers at different points |

The pairing uses no metric. A component that is zero reads `(0, 1)`, and no
rational number reads `(0, 0)`.

Rules:

- The family `F` must have the `cotangent` or `tangent` representation, and
  `S` the `smooth` representation. Otherwise it is an error (`E_TYPE`).
- The object `X` of `fiber_vector` and `fiber_component` must be a smooth
  affine object. Otherwise it is an error (`E_SMOOTH`).
- The coordinate `c` must be a coordinate of `X`. Otherwise it is an error
  (`E_AFFINE_COORDINATE`).
- `fiber_pairing(C, T)` must name a cotangent family and then a tangent
  family. A tangent family in the place of the cotangent family, or the
  reverse, is an error (`E_SMOOTH`). A family that is neither is an error
  (`E_TYPE`).
- The rules of [operand checks](#operand-checks) apply.

Example, from `profile.vast` and `main.vast`:

```vast
{{#include ../../examples/packages/smooth-geometry/src/profile.vast:fiber-primitives}}
{{#include ../../examples/packages/smooth-geometry/src/main.vast:fibers}}
```

`dline(line_at(18), 1)` is the covector dt at the point 18 of `Line`. It lies
over `line_at(18)` and not over `line_at(3)`, and `dt` reads its component as
`(1, 1)`. A component −5/2 reads `(-5, 2)`. For the covector (2, 1) and the
vector (5, −7) at one point of `Plane`, `pairing` gives `(3, 1)`. For a
covector and a vector at two points, it gives `(0, 0)`.

The following binding names the tangent family first:

```vast
{{#include ../../examples/reject/packages/smooth-pairing-order/main.vast:declaration}}
```

```text
{{#include ../../examples/reject/packages/smooth-pairing-order.stderr}}
```

## Reverse-pass primitives

> **Syntax**
>
> ```text
> ReverseBinding -> `cotangent_pullback` `(` Path `,` Path `,` PullbackMode `)`
>     | `differential` `(` Path `,` Path `,` Path `)`
>     | `linearize` `(` Path `,` Path `)`
>     | `cotangent_backward` `(` Path `,` Path `)`
> PullbackMode -> `saved` | `recomputed`
> ```

The **cotangent pullback** of a covector η at F(x) along a smooth map F at a
point x is the covector Jᵀη at x, where J is the Jacobian of F at x. The
covector that a pullback starts from is its **seed**. For a function φ from
`X` to a 1-dimensional object `L`, the **differential** of φ at x is the
pullback of the coordinate covector of `L` at φ(x), whose component is 1.

A pullback along a composite Fₖ ∘ ⋯ ∘ F₁ at x has two parts. The
**forward pass** evaluates the points x₁ = F₁(x), x₂ = F₂(x₁) and so on, up
to the image xₖ. The **reverse pass** pulls the seed back along Fₖ at xₖ₋₁,
then along each earlier map, and along F₁ at x last. The **pullback mode** of
a `cotangent_pullback` binding says where the reverse pass takes the points
from. With `saved`, it reads the points that one forward pass kept. With
`recomputed`, it evaluates again the points that it reads. These are the
strategies Retain and Recompute of
[Residual retention](../storage-ownership.md#residual-retention). A **tape**
of F at x is a value that holds the points of one forward pass of F at x.

In the table, `C` is a cotangent family, `T` a family with the `tape`
representation, and `L` a 1-dimensional smooth affine object. F is the map
of the first operand, or the function φ of a `differential` primitive. x is
the point, and η is the seed.

| Binding | Operands | Result | Value |
| --- | --- | --- | --- |
| `cotangent_pullback(S, C, mode)` | `S<X, Y>`, `S<P, X>`, `C<Y>` | `C<X>` | Jᵀη at x when the seed η lies over F(x); otherwise ⊥ |
| `differential(S, C, L)` | `S<X, L>`, `S<P, X>` | `C<X>` | The differential of φ at x |
| `linearize(S, T)` | `S<X, Y>`, `S<P, X>` | `T<X, Y>` | The tape of F at x |
| `cotangent_backward(T, C)` | `T<X, Y>`, `C<Y>` | `C<X>` | The reverse pass over the tape; ⊥ unless the seed lies over the image that the tape holds |

A pullback of ⊥ is ⊥. The modes `saved` and `recomputed` give the same value
for all operands. For a seed η, the reverse pass over the tape of F at x is
the pullback of η along F at x. None of these bindings consults a metric, so
adding or removing metric declarations changes neither their checking nor
their value.

Rules:

- `S` must have the `smooth` representation, and `T` the `tape`
  representation. Otherwise it is an error (`E_TYPE`).
- `C` must have the `cotangent` representation. A tangent family is an error
  (`E_SMOOTH`). A family that is neither is an error (`E_TYPE`).
- The mode must be `saved` or `recomputed`. Any other word is an error
  (`E_TYPE`).
- The object `L` of `differential` must be a 1-dimensional smooth affine
  object. Otherwise it is an error (`E_SMOOTH`).
- Only a primitive with the binding `linearize` builds a tape. A tape has no
  literal and no declaration, so a value of another type that a program
  annotates, binds or returns as a tape is an error (`E_TYPE`).
  [Operand checks](#operand-checks) gives the error for another value as the
  tape of a `cotangent_backward` primitive.
- The rules of [operand checks](#operand-checks) apply.

> **Implementation note.** After the check, the kernel compiles each reverse
> pass that it can read into
> [compiled reverse Core](../appendix/glossary.md#compiled-reverse-core).
> [Forward Core](../appendix/glossary.md#forward-core) at the call evaluates
> the image of the input point along each map of the pass. A generated
> function, the [backward Core](../appendix/glossary.md#backward-core), pulls
> the seed back one map at a time. It pulls a declared map back by its
> [Jacobian table](../appendix/glossary.md#jacobian-table), a literal that the
> kernel computes from the map. Any other map value, such as a function
> parameter, the value of a branch or `composite(…)`, is an
> [opaque step](../appendix/glossary.md#opaque-step). The
> [runtime reverse pass](../appendix/glossary.md#runtime-reverse-pass) over
> the program value that `smooth_compose` builds pulls the seed back along
> it, in the mode of the call. The `saved` mode passes every point to the
> backward Core: the input point, the intermediate points and the image.
> The `recomputed` mode passes the input point, and the backward Core
> evaluates again the intermediate points that it reads. Neither mode expands
> the composite. The reverse pass of a tape bound by `let` is compiled when
> the map and the point of its `linearize` are bindings, literals or calls of
> primitives that allocate nothing; a tape over a call result or a branch
> value, and a tape passed to a function, keep the runtime reverse pass.
> [Compiled reverse Core](../verification.md#compiled-reverse-core) lists the
> limits of the compilation. Points are runtime values, so a seed over another
> point of the right object gives ⊥ at run time, not a static error.

Example, from `profile.vast` and `main.vast`:

```vast
{{#include ../../examples/packages/smooth-geometry/src/profile.vast:reverse-primitives}}
{{#include ../../examples/packages/smooth-geometry/src/main.vast:stepwise}}
```

With `x = line_at(3)` and the seed `dline(line_at(18), 1)`, `stepwise` gives
the covector 12 dt at 3. `pullback(compose(g(), f()), x, seed)` is the same
covector, and so are the results of `pullback_recomputed` and of
`backward(linearize(compose(g(), f()), x), seed)`. The seed
`dline(line_at(17), 1)` does not lie over g(f(3)) = 18, and its pullback
is ⊥. `differential(g(), plane_at(1, 2))` is the covector (2, 1).

The following binding names a mode that does not exist:

```vast
{{#include ../../examples/reject/packages/smooth-pullback-mode/main.vast:declaration}}
```

```text
{{#include ../../examples/reject/packages/smooth-pullback-mode.stderr}}
```

## Metrics

> **Syntax**
>
> ```text
> MetricDeclaration -> `indexed` `metric` IDENTIFIER `:` Path
>     `<` Path ( `,` Path )* `>` `=` GramForm `;`
> GramForm -> `euclidean` | `gram` `(` GramRows? `)`
> GramRows -> GramRow ( `,` GramRow )* `,`?
> GramRow -> `(` ( Polynomial ( `,` Polynomial )* `,`? )? `)`
> ```

A **metric form** is a family `M` with the `metric_form` representation.
`indexed metric g: M<X> = gram(…);` declares a **smooth metric** `g` of the
metric form `M`: a constant symmetric bilinear form on the smooth affine
object `X`. This chapter calls it a metric. Its **Gram matrix** G gives the
form in the coordinates of `X`, so that g(v, w) = vᵀGw. Each parenthesized
group of `gram(…)` is one row of G. `euclidean` is the identity matrix of
dimension `dim X`. A metric is a declaration. No primitive produces a value
of the type `M<X>`, and no operation selects a metric by default, not even
the Euclidean metric.

Rules:

- The family must have the `metric_form` representation. Otherwise it is an
  error (`E_METRIC`).
- A metric must name exactly one object. Otherwise it is an error
  (`E_METRIC`).
- The object must be a smooth affine object. Otherwise it is an error
  (`E_METRIC`).
- `gram(…)` must have `dim X` rows of `dim X` entries. Otherwise it is an
  error (`E_METRIC`).
- Each entry must be a polynomial expression in the coordinates of `X` that
  expands to a constant. An entry that is not constant is an error
  (`E_METRIC`).
- The rules of [polynomial expressions](#polynomial-expressions) apply to
  each entry. All entries of one metric share one work budget.
- The numerator and the denominator of each entry must have at most
  `metricEntryBits` bits ([limits](../appendix/limits.md#smooth-metrics)).
  Otherwise it is an error (`E_LIMIT`).
- The Gram matrix must be symmetric. Otherwise it is an error (`E_METRIC`).
- The **matrix bound** of the Gram matrix must be less than
  2^`metricMatrixBits` ([limits](../appendix/limits.md#smooth-metrics)). It
  is the product ‖A₁‖ ⋯ ‖Aₙ‖ · max Dᵢ, where Dᵢ is the least common
  denominator of row i, Aᵢ is row i times Dᵢ, and ‖Aᵢ‖ is the Euclidean norm
  of Aᵢ, or 1 for a zero row. Otherwise it is an error (`E_LIMIT`), even when
  no evidence names the metric.
- Any word other than `euclidean` or `gram` after `=` is an error (`E_TYPE`).
- A call of a metric is an error (`E_TYPE`).

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/smooth-geometry/src/main.vast:metrics}}
```

The following Gram matrix is not symmetric:

```vast
{{#include ../../examples/reject/packages/smooth-asymmetric-metric/main.vast:declaration}}
```

```text
{{#include ../../examples/reject/packages/smooth-asymmetric-metric.stderr}}
```

## Metric evidence

> **Syntax**
>
> ```text
> EvidenceDeclaration -> `indexed` `evidence` IDENTIFIER `=` EvidenceKind `(` Path `)` `;`
> EvidenceKind -> `nondegenerate` | `riemannian`
> ```

An `indexed evidence` declaration certifies a property of the metric that it
names. **Nondegenerate evidence** `nondegenerate(g)` certifies that the Gram
matrix of `g` is invertible. **Riemannian evidence** `riemannian(g)`
certifies that it is positive definite. Evidence is a declaration. It is not
a function, and only a [`sharp`](#flat-and-sharp) binding names it.

Rules:

- The path must name a metric. A path that names another indexed declaration
  is an error (`E_METRIC`).
- `nondegenerate(g)` for a singular Gram matrix, such as diag(1, 0), is an
  error (`E_METRIC`).
- `riemannian(g)` for a Gram matrix that is not positive definite, such as
  diag(1, −1), is an error (`E_METRIC`). The same diag(1, −1) has
  nondegenerate evidence.
- Any word other than `nondegenerate` or `riemannian` is an error (`E_TYPE`).
- Several evidence declarations may name one metric.
- A call of evidence is an error (`E_TYPE`).

> **Implementation note.** The kernel computes an inverse B with
> GB = BG = I for nondegenerate evidence. For Riemannian evidence it computes a
> factorization G = L D Lᵀ, with L unit lower triangular and every diagonal
> entry of D positive, and an inverse of L. It checks every identity again
> before acceptance. A certificate never comes from the frontend. The
> [matrix bound](#metrics) of the metric limits the size of a certificate,
> and the kernel checks that bound before it computes one. The kernel
> computes one certificate for each metric and kind. Further evidence
> declarations of that kind for that metric carry the same certificate, and
> the declaration audit checks equal evidence declarations once.

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/smooth-geometry/src/main.vast:evidence}}
```

The metric diag(1, −1) has nondegenerate evidence and no Riemannian evidence:

```vast
{{#include ../../examples/reject/packages/smooth-indefinite-metric/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/smooth-indefinite-metric.stderr}}
```

A singular Gram matrix has no nondegenerate evidence:

```vast
{{#include ../../examples/reject/packages/smooth-singular-metric/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/smooth-singular-metric.stderr}}
```

## Flat and sharp

> **Syntax**
>
> ```text
> MetricBinding -> `flat` `(` Path `,` Path `,` `using` `=` Path `)`
>     | `sharp` `(` Path `,` Path `,` `using` `=` Path
>       `,` `evidence` `=` Path `)`
> ```

`flat` and `sharp` convert between vectors and covectors by a named metric g
with the Gram matrix G on the object `X`. In the table, `T` is a tangent
family and `C` a cotangent family.

| Binding | Operand | Result | Value |
| --- | --- | --- | --- |
| `flat(T, C, using = g)` | `T<X>` | `C<X>` | The covector Gv at the point of v |
| `sharp(C, T, using = g, evidence = e)` | `C<X>` | `T<X>` | The vector G⁻¹α at the point of α |

Both send ⊥ to ⊥. For one metric, `sharp` after `flat` gives the vector
again, and `flat` after `sharp` gives the covector again. There is no
gradient primitive. The **gradient** of a function at a point under a metric
is the vector that `sharp` gives for the differential, and a program computes
it with an ordinary function.

Rules:

- `flat` must name a metric with `using =`. `sharp` must name a metric with
  `using =` and evidence with `evidence =`, in this order. A missing
  selection is an error (`E_PARSE`).
- The path after `using =` must name a metric. Otherwise it is an error
  (`E_METRIC`).
- The path after `evidence =` must name evidence. Otherwise it is an error
  (`E_METRIC`).
- The evidence must certify the metric after `using =`. Evidence for another
  metric is an error (`E_METRIC`).
- The evidence must be nondegenerate evidence. Riemannian evidence is an
  error (`E_METRIC`).
- `flat` must name a tangent family and then a cotangent family, and `sharp`
  must name them in the reverse order. A tangent family in the place of a
  cotangent family, or the reverse, is an error (`E_SMOOTH`). A family that
  is neither is an error (`E_TYPE`).
- The operand must lie over the object of the metric. Otherwise the call is
  an error (`E_ENDPOINT`). The rules of [operand checks](#operand-checks)
  apply.
- A path names a metric as it names any other declaration, by the rules of
  [Names and paths](names-and-paths.md). A module that imports two metrics
  of one name is an error (`E_DUPLICATE`).
- A metric that a path names is that metric. Evidence for another metric of
  the same name does not certify it (`E_METRIC`).

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/smooth-geometry/src/main.vast:musical}}
```

For g(x, y) = x² + y at (1, 2), the differential is (2, 1), and
`gradient_skew(g(), plane_at(1, 2))` is the vector (1, 0). `flat_skew` sends
the vector (5, −7) to the covector (3, −2), and `sharp_skew` sends that
covector to the vector (5, −7).

In the following program `Euclid` is the only metric, and `flat` names none:

```vast
{{#include ../../examples/reject/packages/smooth-default-metric/main.vast:declaration}}
```

```text
{{#include ../../examples/reject/packages/smooth-default-metric.stderr}}
```

## Operand checks

These rules apply to every call of a primitive of this chapter.

Rules:

- A call must have the number of operands that the binding fixes. Otherwise it
  is an error (`E_ARITY`).
- An operand that the table of its binding gives as `Int` must have type
  `Int`. Otherwise it is an error (`E_TYPE`).
- An operand whose kind does not fit the table of its binding is an error
  (`E_TYPE`). This covers a value that is not a value of a family, such as an
  `Int` or a `Bool`, in the place of a map, a point, a fiber or a tape,
  except as the point of a `fiber_vector` primitive. It also covers a value
  of a family with a number of object arguments other than two as a map of
  `smooth_compose`, `cotangent_pullback`, `differential` or `linearize`, or
  as the tape of `cotangent_backward`.
- Any other operand from the wrong family or over the wrong object is an
  error (`E_ENDPOINT`). Examples are a vector in the place of a covector, a
  seed over the wrong object, two maps whose middle objects differ, and a
  function into a second declaration of the object `L` of a `differential`
  primitive.
- When each operand has the number of object arguments that the table gives,
  two for a map, a point or a tape and one for a covector or a vector, the
  `E_ENDPOINT` message names the first failed check: the operand, the family
  or object that the binding expects, and the one supplied. The compiler
  checks families before objects. One check has no such message: the source
  of a point must be a 0-dimensional smooth affine object.
- The message lists the types of the operands instead for a point whose
  source is not such an object, for a covector as the point of a
  `cotangent_pullback` or `fiber_vector` primitive, and for a value that is
  not a value of a family as the point of a `fiber_vector` primitive.

In this program `f` leads from `Line` to `Plane`, and the seed is a covector
on `Line`:

```vast
{{#include ../../examples/reject/packages/smooth-seed-object/main.vast:program}}
```

```text
{{#include ../../examples/reject/packages/smooth-seed-object.stderr}}
```

In this program `Axis` is declared like the library's `Line`, and
`differential` of the standard library has the binding
`differential(Smooth, Cotangent, Line)`:

```vast
{{#include ../../examples/reject/packages/smooth-other-line/main.vast:program}}
```

```text
{{#include ../../examples/reject/packages/smooth-other-line.stderr}}
```

## Scope of smooth affine geometry

Smooth affine geometry covers the declarations of this chapter. Its objects
are the affine spaces ℝⁿ of dimension at most 16, and its maps are polynomial
maps with rational coefficients. A metric is constant: its Gram matrix is
the same at every point. A function body composes maps, builds points,
covectors and vectors from integers, and pulls covectors back. It creates no
object, and it declares no map and no metric. The language has no
declaration of a manifold or of a chart. Presented affine geometry is in
[Presented affine declarations](../affine-geometry.md), and the descriptor
objects of the core are in [Geometric types](geometric-types.md).
