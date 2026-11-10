# Smooth affine declarations

This chapter defines the declarations of smooth real affine geometry: smooth
affine objects, smooth maps between them, tangent and cotangent fibers,
tapes, metrics and metric evidence, and the primitive bindings that act on
them. The general rules of `indexed` declarations, such as visibility, names
and markers, are in [Indexed declarations](../indexed-source.md).
[Notation](notation.md) explains the Syntax blocks, and the
[glossary](../appendix/glossary.md) defines the terms.

The examples quote the tested programs in
[`examples/packages/smooth-differential/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/smooth-differential).
A rejected fragment is shown with the code and message of the diagnostic that
the compiler prints for it; the file position depends on where the fragment
appears.

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

An implementation with the `smooth_affine` representation backs the
[smooth affine objects](../appendix/glossary.md#smooth-affine-object). A
classification whose domain lists such an implementation, such as
`CInfAffine` below, is the classification over which the smooth families
range. The five representations give the families of
[smooth maps](../appendix/glossary.md#smooth-map) (`smooth`), of cotangent and
tangent [fibers](../appendix/glossary.md#tangent-or-cotangent-fiber)
(`cotangent`, `tangent`), of [tapes](../appendix/glossary.md#tape) (`tape`)
and of [metric forms](../appendix/glossary.md#metric-form) (`metric_form`).
The `token`, `point` and `morphism` representations are in
[Families](../indexed-source.md#families), and
the `relative` representation is in
[presented affine declarations](../affine-geometry.md#the-presented-profile).

The standard library declares one smooth profile.
`std::geometry::smooth::affine` declares the implementation `SmoothR`, the
classification `CInfAffine`, the families `Smooth`, `Tape`, `Tangent` and
`Cotangent`, the objects `Pt` and `Line`, and the profile-wide primitives.
`std::geometry::metric` declares `MetricForm`. `std::differential` binds
`pullback`, `differential`, `linearize` and `backward`. A program may use
these declarations or declare a profile of its own. Each declaration is a
distinct object or family, so an application's own `Affine(1)[t]` is not the
library's `Line`.

The constraint `canonical(i)` holds for an application when its index `i` is
a declared smooth affine object. It compares declarations, never dimensions.
A local object, such as one that `Affine(CInfReal, n)` builds in a function
body, never satisfies it.

Rules:

- A `smooth_affine` implementation must list no capabilities. Otherwise it is
  an error (`E_TYPE`).
- A marker that a `smooth_affine` implementation names must not also be named
  by an implementation with complex coefficients. Otherwise it is an error
  (`E_TYPE`).
- A family with the `smooth` or `tape` representation must have exactly two
  parameters, both `object(C)`, and exactly the constraints `canonical(0),
  canonical(1)`. Otherwise it is an error (`E_TYPE`).
- A family with the `cotangent`, `tangent` or `metric_form` representation
  must have exactly one parameter `object(C)` and exactly the constraint
  `canonical(0)`. Otherwise it is an error (`E_TYPE`).
- Every implementation in the domain of `C` must have the `smooth_affine`
  representation. Otherwise it is an error (`E_TYPE`). In particular, these
  families never range over presented or descriptor objects.
- The slot of `canonical(i)` must be an `object(…)` parameter. Otherwise it is
  an error (`E_TYPE`).
- A type whose index fails `canonical(i)`, such as `Smooth<Line, QLine>` for a
  presented object `QLine`, is an error (`E_TYPE`).

Example, from
[`profile.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/smooth-differential/src/profile.vast):

```vast
pub indexed marker CInfReal;
pub indexed implementation SmoothR(CInfReal, smooth_affine) capabilities();
pub indexed classification CInfAffine { parents(); domain(SmoothR); };
pub indexed family Smooth(object(CInfAffine), object(CInfAffine))
    = smooth constraints(canonical(0), canonical(1));
pub indexed family Cotangent(object(CInfAffine)) = cotangent constraints(canonical(0));
pub indexed family Tangent(object(CInfAffine)) = tangent constraints(canonical(0));
pub indexed family Tape(object(CInfAffine), object(CInfAffine))
    = tape constraints(canonical(0), canonical(1));
pub indexed family MetricForm(object(CInfAffine)) = metric_form constraints(canonical(0));
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

`indexed affine X(Impl) = Affine(n)[c₁, …, cₙ]` declares a smooth affine
object: the smooth real affine space ℝⁿ with the coordinates `c₁, …, cₙ`.
Each declaration is one canonical object. Two declarations of the same
dimension are different objects.

`Affine(K, n)[g₁, …, gₙ]`, with a base `K`, is the algebraic spelling. It is
the declaration `spec[g₁, …, gₙ] over K` of a presented object, and the rules
of [presented affine objects](../affine-geometry.md#presented-affine-objects) apply to it.
The other forms of `indexed affine` (`spec[…]`, `fiber(…)` and `localize(…)`)
are in [presented affine declarations](../affine-geometry.md#presented-affine-objects).

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

Example:

```vast
pub indexed affine Pt(SmoothR) = Affine(0)[];
pub indexed affine Line(SmoothR) = Affine(1)[t];
pub indexed affine Plane(SmoothR) = Affine(2)[x, y];
```

`indexed affine Bad(SmoothR) = Affine(2)[t];` is rejected with:

```text
E_SMOOTH: Affine(2) needs 2 coordinates, but 1 are given
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

A polynomial expression has exact rational coefficients. The images of a
smooth map are polynomial expressions in the source coordinates, and the
entries of a Gram matrix are polynomial expressions in the coordinates of the
metric's object. `frac` followed by `(` starts a fraction; any other `frac` is
a coordinate name. Unary `-` applies to the whole factor, so `-x^2` is
`-(x²)`.

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
  [exact affine algebra](../appendix/limits.md#exact-affine-algebra-stage-2).
  Otherwise it is an error (`E_LIMIT`).
- A fraction with a zero denominator is an error (`E_AFFINE_COORDINATE`).
- A coordinate name that the object does not have is an error
  (`E_AFFINE_COORDINATE`).

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
map. `indexed morphism f: Smooth<X, Y> = pullback(y₁ -> p₁, …, yₘ -> pₘ)`
gives each target coordinate `yᵢ` of `Y` as a polynomial `pᵢ` in the source
coordinates of `X`. It denotes the polynomial map x ↦ (p₁(x), …, pₘ(x)).
`identity` is the identity map of `X`. The declaration defines a function of
no operands: `f()` is the map, of type `Smooth<X, Y>`. The other definitions
belong to [morphisms over a base](../affine-geometry.md#morphisms-over-a-base).

Rules:

- A smooth map must name exactly two objects, its source and its target.
  Otherwise it is an error (`E_SMOOTH`).
- Both objects must be smooth affine objects. Otherwise it is an error
  (`E_SMOOTH`).
- `pullback(…)` must give each target coordinate exactly one image. A missing,
  repeated or unknown target coordinate is an error (`E_AFFINE_COORDINATE`).
- Each image must be a polynomial expression in the source coordinates. Any
  other name in an image, including a target coordinate, is an error
  (`E_AFFINE_COORDINATE`).
- The images may be written in any order. The map stores them in the order
  of the target's coordinates.
- `identity` must have the same object as source and target. Otherwise it is
  an error (`E_SMOOTH`).
- `structure`, `first`, `second` and `restrict(…)` at a smooth family are an
  error (`E_SMOOTH`).
- Any other word after `=` is an error (`E_TYPE`).

Example, from
[`main.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/smooth-differential/src/main.vast):

```vast
indexed morphism f: Smooth<Line, Plane> = pullback(x -> t, y -> t^2);
indexed morphism g: Smooth<Plane, Line> = pullback(t -> x^2 + y);
indexed morphism idP: Smooth<Plane, Plane> = identity;
indexed morphism shearA: Smooth<Plane, Plane> = pullback(x -> x + y, y -> y);
```

`indexed morphism bad: Smooth<Line, Plane> = pullback(x -> x, y -> t);` uses
the target coordinate `x` in an image. It is rejected with:

```text
E_AFFINE_COORDINATE: unknown coordinate x
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
this chapter, `S` is a smooth family, and `P` is any 0-dimensional smooth
affine object. A *point* of `X` is a value of `S<P, X>`: a rational point of
`X`. The bindings for `point` and `morphism` families are in
[Primitives](../indexed-source.md#primitives), and the `relative_*` bindings
are in
[presented affine declarations](../affine-geometry.md#morphism-primitives).

| Binding | Operands | Result | Value |
| --- | --- | --- | --- |
| `smooth_compose(S)` | `S<Y, Z>`, `S<X, Y>` | `S<X, Z>` | The first map after the second |
| `smooth_equal(S)` | `S<X, Y>`, `S<X, Y>` | `Bool` | Whether the two maps are the same polynomial map |
| `smooth_composite(S)` | `S<X, Y>` | `S<X, Y>` | The same map, as one map |
| `smooth_int_point(S, X, P)` | `dim X` operands of type `Int` | `S<P, X>` | The point of `X` with these coordinates, in coordinate order |

Rules:

- The family `S` must have the `smooth` representation. Otherwise it is an
  error (`E_TYPE`).
- `smooth_int_point(S, X, P)` must name a smooth affine object `X` and a
  0-dimensional smooth affine object `P`. Otherwise it is an error
  (`E_SMOOTH`).
- The operand rules of [operand checks](#operand-checks) apply.

> **Implementation note.** `smooth_compose` builds a program node and never
> expands the composite. `smooth_equal` and `smooth_composite` expand it at
> run time, without a budget.

Example:

```vast
pub indexed primitive compose = smooth_compose(Smooth);
pub indexed primitive same = smooth_equal(Smooth);
pub indexed primitive composite = smooth_composite(Smooth);
pub indexed primitive line_at = smooth_int_point(Smooth, Line, Pt);
```

`compose(g(), f())` is g after f, and `line_at(3)` is the point 3 of `Line`.

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

A value of `Cotangent<X>` or `Tangent<X>` is a covector or a vector at a
point of `X`, with one component per coordinate in the coordinate coframe or
frame, or the [failure value](../appendix/glossary.md#failure-value) ⊥. In
the table, `F` is a cotangent or tangent family, `C` a cotangent family and
`T` a tangent family.

| Binding | Operands | Result | Value |
| --- | --- | --- | --- |
| `fiber_vector(F, S, X)` | `S<P, X>`, then `dim X` operands of type `Int` | `F<X>` | The covector or vector at the point with these components |
| `fiber_at(F, S)` | `F<X>`, `S<P, X>` | `Bool` | Whether the fiber lies over the point; `false` for ⊥ |
| `fiber_equal(F)` | `F<X>`, `F<X>` | `Bool` | Whether the points and the components are equal; ⊥ equals nothing, itself included |
| `fiber_component(F, X, c)` | `F<X>` | `Pair<Int>` | The component at `c` as a reduced numerator and a positive denominator; `(0, 0)` for ⊥ |
| `fiber_pairing(C, T)` | `C<X>`, `T<X>` | `Pair<Int>` | The pairing α(v) = Σᵢ αᵢvᵢ, reduced; `(0, 0)` for ⊥ or for fibers at different points |

The pairing uses no metric.

Rules:

- The family `F` must have the `cotangent` or `tangent` representation, and
  `S` the `smooth` representation. Otherwise it is an error (`E_TYPE`).
- The object `X` of `fiber_vector` and `fiber_component` must be a smooth
  affine object. Otherwise it is an error (`E_SMOOTH`).
- The coordinate `c` must be a coordinate of `X`. Otherwise it is an error
  (`E_AFFINE_COORDINATE`).
- `fiber_pairing(C, T)` must name a cotangent family and then a tangent
  family. A family of the wrong variance is an error (`E_SMOOTH`); a family
  that is neither is an error (`E_TYPE`).
- The operand rules of [operand checks](#operand-checks) apply.

Example, from `profile.vast` and `main.vast`:

```vast
indexed primitive dline = fiber_vector(Cotangent, Smooth, Line);
indexed primitive dt = fiber_component(Cotangent, Line, t);
pub indexed primitive lies_over = fiber_at(Cotangent, Smooth);
pub indexed primitive pairing = fiber_pairing(Cotangent, Tangent);
```

`dline(line_at(18), 1)` is the covector dt at the point 18 of `Line`.

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

The [cotangent pullback](../appendix/glossary.md#cotangent-pullback) of a
covector η at F(x) along a smooth map F at a point x is the covector Jᵀη at
x, where J is the Jacobian of F at x. The covector that a pullback starts
from is its [seed](../appendix/glossary.md#seed). In the table, `C` is a
cotangent family, `T` a tape family, and `L` a 1-dimensional smooth affine
object.

| Binding | Operands | Result | Value |
| --- | --- | --- | --- |
| `cotangent_pullback(S, C, mode)` | `S<X, Y>`, `S<P, X>`, `C<Y>` | `C<X>` | Jᵀη at x when the seed η lies over F(x); otherwise ⊥ |
| `differential(S, C, L)` | `S<X, L>`, `S<P, X>` | `C<X>` | The pullback of the coordinate covector of `L` at φ(x) |
| `linearize(S, T)` | `S<X, Y>`, `S<P, X>` | `T<X, Y>` | The [tape](../appendix/glossary.md#tape) of F at x |
| `cotangent_backward(T, C)` | `T<X, Y>`, `C<Y>` | `C<X>` | The reverse pass over the tape; ⊥ unless the seed lies over the tape's output point |

A pullback of ⊥ is ⊥. The modes `saved` and `recomputed` give the same value
for every operand. `cotangent_backward(linearize(F, x), η)` is the pullback of
η along F at x. None of these bindings consults a metric, so adding or
removing metric declarations changes neither their checking nor their value.

Rules:

- `S` must have the `smooth` representation, and `T` the `tape`
  representation. Otherwise it is an error (`E_TYPE`).
- `C` must have the `cotangent` representation. A tangent family is an error
  (`E_SMOOTH`); a family that is neither is an error (`E_TYPE`).
- The mode must be `saved` or `recomputed`. Any other word is an error
  (`E_TYPE`).
- The object `L` of `differential` must be a 1-dimensional smooth affine
  object. Otherwise it is an error (`E_SMOOTH`).
- `linearize` is the only way to build a tape. A tape has no literal or
  declaration form, so a value of another type annotated, bound or returned as
  a tape is an error (`E_TYPE`). In the tape slot of `cotangent_backward`, the
  [operand checks](#operand-checks) apply.
- The operand rules of [operand checks](#operand-checks) apply.

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

Example:

```vast
pub indexed primitive pullback = cotangent_pullback(Smooth, Cotangent, saved);
pub indexed primitive pullback_recomputed = cotangent_pullback(Smooth, Cotangent, recomputed);
pub indexed primitive differential = differential(Smooth, Cotangent, Line);
pub indexed primitive linearize = linearize(Smooth, Tape);
pub indexed primitive backward = cotangent_backward(Tape, Cotangent);
```

The pullback along g at f(x), then along f at x, is an ordinary function:

```vast
fn stepwise(x: Smooth<Pt, Line>, seed: Cotangent<Line>) -> Cotangent<Line> {
    pullback(f(), x, pullback(g(), compose(f(), x), seed))
}
```

With `x = line_at(3)` and the seed `dline(line_at(18), 1)`, it gives 12 dt at
3, the same covector as `pullback(compose(g(), f()), x, seed)`.

`indexed primitive bad = cotangent_pullback(Smooth, Cotangent, cached);` is
rejected with:

```text
E_TYPE: a cotangent pullback mode is saved or recomputed
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

`indexed metric g: MetricForm<X> = gram(…)` declares a metric: a constant
symmetric bilinear form on the smooth affine object `X`, given by its Gram
matrix G in the coordinates of `X`, so that g(v, w) = vᵀGw. Each parenthesized
group is one row. `euclidean` is the identity matrix of dimension `dim X`. A
metric is a declaration. No primitive produces a value of a metric form type,
and no operation selects a metric by default, not even the Euclidean metric.

Rules:

- The family must have the `metric_form` representation. Otherwise it is an
  error (`E_METRIC`).
- A metric must name exactly one object. Otherwise it is an error
  (`E_METRIC`).
- The object must be a smooth affine object. Otherwise it is an error
  (`E_METRIC`).
- `gram(…)` must have `dim X` rows of `dim X` entries. Otherwise it is an
  error (`E_METRIC`).
- Each entry must be a constant polynomial expression in the coordinates of
  `X`. A non-constant entry is an error (`E_METRIC`).
- The rules of [polynomial expressions](#polynomial-expressions) apply to
  each entry. All entries of one metric share one work budget.
- The numerator and the denominator of each entry must have at most
  `metricEntryBits` bits ([limits](../appendix/limits.md#smooth-metrics)).
  Otherwise it is an error (`E_LIMIT`).
- The Gram matrix must be symmetric. Otherwise it is an error (`E_METRIC`).
- The [matrix bound](../appendix/glossary.md#matrix-bound) of the Gram matrix
  must be less than 2^`metricMatrixBits`
  ([limits](../appendix/limits.md#smooth-metrics)). It is the product
  ‖A₁‖ ⋯ ‖Aₙ‖ · max Dᵢ, where Dᵢ is the least common denominator of row i,
  Aᵢ is row i times Dᵢ, and ‖Aᵢ‖ is the Euclidean norm of Aᵢ, or 1 for a
  zero row. Otherwise it is an error (`E_LIMIT`), even when no evidence names
  the metric.
- Any word other than `euclidean` or `gram` after `=` is an error (`E_TYPE`).

Example:

```vast
indexed metric Euclid: MetricForm<Plane> = euclidean;
indexed metric Skew: MetricForm<Plane> = gram((2, 1), (1, 1));
indexed metric Lorentz: MetricForm<Plane> = gram((1, 0), (0, -1));
```

With `gram((2, 1), (0, 1))` in place of the Gram matrix of `Skew`, the
package `smooth_differential` is rejected with:

```text
E_METRIC: the metric `smooth_differential::Skew` is not symmetric: the entries in row 1, column 2 and in row 2, column 1 differ
```

## Metric evidence

> **Syntax**
>
> ```text
> EvidenceDeclaration -> `indexed` `evidence` IDENTIFIER `=` EvidenceKind `(` Path `)` `;`
> EvidenceKind -> `nondegenerate` | `riemannian`
> ```

Evidence certifies a property of the metric it names.
[Nondegenerate evidence](../appendix/glossary.md#nondegenerate-evidence)
`nondegenerate(g)` certifies that the Gram matrix of `g` is invertible.
[Riemannian evidence](../appendix/glossary.md#riemannian-evidence)
`riemannian(g)` certifies that it is positive definite.

Rules:

- The path must name a metric. A path that names another indexed declaration
  is an error (`E_METRIC`).
- `nondegenerate(g)` for a singular Gram matrix, such as diag(1, 0), is an
  error (`E_METRIC`).
- `riemannian(g)` for a Gram matrix that is not positive definite, such as
  diag(1, −1), is an error (`E_METRIC`). The same diag(1, −1) has
  nondegenerate evidence.
- Any word other than `nondegenerate` or `riemannian` is an error (`E_TYPE`).

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

Example:

```vast
indexed evidence SkewInvertible = nondegenerate(Skew);
indexed evidence SkewPositive = riemannian(Skew);
indexed evidence LorentzInvertible = nondegenerate(Lorentz);
```

`indexed evidence LorentzPositive = riemannian(Lorentz);` is rejected with:

```text
E_METRIC: the metric `smooth_differential::Lorentz` is not positive definite, so it has no Riemannian evidence
```

## Flat and sharp

> **Syntax**
>
> ```text
> MetricBinding -> `flat` `(` Path `,` Path `,` `using` `=` Path `)`
>     | `sharp` `(` Path `,` Path `,` `using` `=` Path
>       `,` `evidence` `=` Path `)`
> ```

`flat` and `sharp` are the musical maps of a named metric g with Gram matrix
G on the object `X`. In the table, `T` is a tangent family and `C` a
cotangent family.

| Binding | Operand | Result | Value |
| --- | --- | --- | --- |
| `flat(T, C, using = g)` | `T<X>` | `C<X>` | The covector Gv at the point of v |
| `sharp(C, T, using = g, evidence = e)` | `C<X>` | `T<X>` | The vector G⁻¹α at the point of α |

Both map ⊥ to ⊥. For one metric, `sharp(flat(v)) = v` and `flat(sharp(α)) = α`.
There is no gradient primitive. A gradient is an ordinary function that
applies `sharp` to a differential.

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
- `flat` must name a tangent family and then a cotangent family; `sharp` must
  name them in the reverse order. A family of the wrong variance is an error
  (`E_SMOOTH`). A family that is neither is an error (`E_TYPE`).
- The operand must lie over the object of the metric. The operand rules of
  [operand checks](#operand-checks) apply.

A metric is named like any other declaration. A module that imports two
metrics of one name is an error (`E_DUPLICATE`), and a metric named by path is
that metric.

Example:

```vast
indexed primitive flat_skew = flat(Tangent, Cotangent, using = Skew);
indexed primitive sharp_skew = sharp(Cotangent, Tangent, using = Skew, evidence = SkewInvertible);

fn gradient_skew(h: Smooth<Plane, Line>, p: Smooth<Pt, Plane>) -> Tangent<Plane> {
    sharp_skew(differential(h, p))
}
```

For g(x, y) = x² + y at (1, 2), the differential is (2, 1) and
`gradient_skew(g(), plane_at(1, 2))` is the vector (1, 0).

`indexed primitive flat_euclid = flat(Tangent, Cotangent);` is rejected with:

```text
E_PARSE: `flat` needs an explicit metric: write `using = …`
```

## Operand checks

These rules apply to every call of a primitive of this chapter.

- A call must have the number of operands that the binding fixes. Otherwise it
  is an error (`E_ARITY`).
- An operand whose shape does not fit its slot is an error (`E_TYPE`). This
  covers a value that is not a family application, such as an `Int` or a
  `Bool`, where a map, point, fiber or tape is required, except in the point
  slot of `fiber_vector`. It also covers a value with one object index in a
  map slot of `smooth_compose`, `cotangent_pullback`, `differential` or
  `linearize`, or in the tape slot of `cotangent_backward`.
- Any other operand from the wrong family or over the wrong object is an
  error (`E_ENDPOINT`). Examples are a `Tangent` value where a `Cotangent`
  value is required, a seed over the wrong object, and two maps whose middle
  objects differ.
- When every operand has the index shape that its slot expects, two object
  indices for a map, point or tape and one for a covector or vector, and an
  operand has the wrong family or object, the `E_ENDPOINT` message names the
  first failed requirement: the operand, and
  the family or object that it requires and the one supplied. Families are
  checked before objects. Otherwise the message lists the operand types.
  Examples are a covector in the point slot of `cotangent_pullback` or
  `fiber_vector`, a value that is not a family application in the point slot
  of `fiber_vector`, and a point whose source object is not 0-dimensional.

For example, `pullback(g(), plane_at(3, 9), dplane(plane_at(3, 9), 1, 0))`
pulls back a seed on `Plane` along a map to `Line`. It is rejected with:

```text
E_ENDPOINT: pullback requires a seed with object Line (the map's target), but the supplied seed has object Plane
```
