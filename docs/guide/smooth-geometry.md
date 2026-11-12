# Smooth geometry and reverse pullbacks

This chapter builds one program step by step. It declares two polynomial
maps between real affine spaces and composes them. It then pulls a covector
back along the composite, from the target of the maps to their source, and
computes a differential and a gradient. Every number in the program is an
exact rational number, and the program prints `42` only when every
observation holds.

The program is
[`examples/packages/stdlib-differential/main.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/stdlib-differential/main.vast).
Run it from the repository root:

```sh
python3 scripts/build_stdlib_package.py
target/debug/vastitas build --manifest-path examples/packages/stdlib-differential/Vastitas.toml -o target/stdlib-differential
./target/stdlib-differential
```

The first command generates the standard library's package root; see
[using the standard library](stdlib.md#using-the-standard-library).

## The smooth profile of the standard library

A [*smooth affine object*](../appendix/glossary.md#smooth-affine-object) is
the real affine space ℝⁿ with a name for each of its n coordinates. It is
not one of the descriptor objects of the
[smooth setting](indexed-geometry.md#two-settings), which record a dimension
and have no coordinates. The standard library declares the types of this
geometry and two objects, and the program imports them:

```vast
{{#include ../../examples/packages/stdlib-differential/main.vast:imports}}
```

| Name | Meaning |
| --- | --- |
| `SmoothR` | The implementation of the smooth affine objects |
| `Smooth<X, Y>` | The type of the smooth maps from `X` to `Y` |
| `Cotangent<X>` | The type of the covectors at the points of `X` |
| `Tangent<X>` | The type of the vectors at the points of `X` |
| `Pt` | The object of dimension 0, a single point |
| `Line` | The object of dimension 1, with the coordinate `t` |
| `MetricForm<X>` | The type that the declaration of a metric on `X` names |

The other imports are primitives of the library. The sections below
introduce each of them where the program uses it.

## Objects, maps and points

The program declares the plane, a primitive that builds its points, and two
maps:

```vast
{{#include ../../examples/packages/stdlib-differential/main.vast:objects}}
```

`indexed affine Plane(SmoothR) = Affine(2)[x, y];` declares an object of the
implementation `SmoothR`. `Affine(2)` gives its dimension, and the brackets
name its coordinates `x` and `y`. The library declares `Pt` as `Affine(0)[]`
and `Line` as `Affine(1)[t]` in the same way.

A [*smooth map*](../appendix/glossary.md#smooth-map) between two smooth
affine objects is a polynomial map. Its declaration has the form of the
morphisms of the [previous chapter](affine-geometry.md#morphisms-are-written-as-pullbacks):
for each coordinate of the target, `pullback` gives a polynomial in the
coordinates of the source. `f` sends the point `t` of the line to the point
`(t, t²)` of the plane, and `g` sends `(x, y)` to `x² + y`. Each declaration
defines a function without parameters, so `f()` is the map, of type
`Smooth<Line, Plane>`.

A point of an object `X` is a smooth map from `Pt` to `X`. Its coordinates
are rational numbers, so it is a
[*rational point*](../appendix/glossary.md#rational-point). The binding
`smooth_int_point(Smooth, Plane, Pt)` builds a point of `Plane` from one
integer for each coordinate: `plane_at(1, 2)` is the point (1, 2), of type
`Smooth<Pt, Plane>`. The library declares `line_at` for `Line` with the same
binding, and `line_at(3)` is the point 3.

`compose_smooth(g, f)` is `g` after `f`. With a point as its second operand
it gives the image of the point: `compose_smooth(f(), line_at(3))` is the
point (3, 9) of the plane. `compose_smooth(g(), f())` sends `t` to
`t² + t²`, which is `2t²`. The composite keeps both maps: the program does
not multiply their polynomials out.

## Covectors and vectors

A vector at a point of `X` has one component for each coordinate of `X`. A
covector at the point is a linear function on these vectors, and it has one
component for each coordinate too. On the line, the covector with the
component 1 is dt. On the plane, the covector with the components `a` and
`b` is a dx + b dy. The values of the types `Cotangent<X>` and `Tangent<X>`
are covectors and vectors at rational points of `X`, the
[*cotangent and tangent fibers*](../appendix/glossary.md#tangent-or-cotangent-fiber)
of the library.

The program declares primitives that build covectors and vectors and
primitives that read their components:

```vast
{{#include ../../examples/packages/stdlib-differential/main.vast:fibers}}
```

The binding `fiber_vector(Cotangent, Smooth, Line)` builds a covector on
`Line` from a point and one integer for each coordinate.
`dline(line_at(18), 1)` is the covector dt at the point 18. In the same way,
`vplane(p, 1, 0)` is the vector (1, 0) at the point `p` of the plane.

The binding `fiber_component(Cotangent, Line, t)` reads the component of a
covector at the coordinate `t`. A component is a fraction: a `Pair<Int>` of
a numerator and a denominator, as the coefficients of the
[previous chapter](affine-geometry.md#comparing-morphisms) are.

Four primitives of the library compare and combine covectors and vectors:

| Call | Value |
| --- | --- |
| `lies_over(α, x)` | Whether `α` is a covector at the point `x` |
| `same_covector(α, β)` | Whether `α` and `β` are covectors at one point with equal components |
| `same_vector(v, w)` | Whether `v` and `w` are vectors at one point with equal components |
| `pairing(α, v)` | The number α(v) for a covector and a vector at one point: the sum of the products of their components, as a fraction |

## Pulling a covector back

Let `F` be a smooth map from `X` to `Y`, `x` a point of `X`, and η a covector
at the point `F(x)` of `Y`. The
[*cotangent pullback*](../appendix/glossary.md#cotangent-pullback) of η along
`F` at `x` is a covector at `x`. The chain rule gives its components: each
is a sum of products of the components of η with partial derivatives of `F`
at `x`. The covector η that a pullback starts from is its
[*seed*](../appendix/glossary.md#seed). `pullback(F, x, η)` of
`std::differential` computes the pullback.

`main` begins with a point, a seed, the composite and a pullback in two
steps:

```vast
{{#include ../../examples/packages/stdlib-differential/main.vast:pullbacks}}
```

`x` is the point 3 of the line. Its image under `f` is (3, 9), and the image
of that point under `g` is 18, so the seed is dt at 18. The inner call pulls
the seed back along `g` at (3, 9). The function `x² + y` has the partial
derivatives `2x` and 1, so the result is the covector 6 dx + dy at (3, 9).
The outer call pulls that covector back along `f` at 3. The images `t` and
`t²` of `f` have the derivatives 1 and `2t`, so dx pulls back to dt and dy
to 6 dt. The result is 6 dt + 6 dt: `stepped` is the covector 12 dt at 3.

The composite sends `t` to `2t²`, whose derivative at 3 is 12. So the
pullback of the seed along `gAfterF` at `x` is 12 dt as well, in one call.
Codes 1 to 3 of [`main`](#the-observations) check that `stepped` has the
component 12, that it equals `pullback(gAfterF, x, seed)`, and that it lies
over `x`.

A pullback moves a covector against the maps: from the target of the
composite back to its source, and along `g`, the last map, first. For this
reason the pullback of a covector is also called a
[*reverse pullback*](../appendix/glossary.md#reverse-pullback).

## A seed must lie over the image point

A seed is a covector at one point. The pullback along `F` at `x` needs a seed
at `F(x)`. The seed `dline(line_at(17), 1)` lies over 17 and not over
`g(f(3))`, which is 18, so its pullback is the
[*failure value*](../appendix/glossary.md#failure-value) instead of a
covector. The failure value lies over no point and equals no covector, and
every pullback of it is the failure value again. Code 6 checks that the
result does not lie over `x`.

Points are run-time values, so the checker cannot reject a seed over the
wrong point. It does reject a seed over the wrong object. In a program with
the declarations of this chapter, the following function passes a seed on
`Line` to a pullback along `f`, whose target is `Plane`:

```vast
{{#include ../../examples/reject/packages/smooth-seed-object/main.vast:function}}
```

```text
{{#include ../../examples/reject/packages/smooth-seed-object.stderr}}
```

## The forward pass and the reverse pass

The pullback along `gAfterF` at 3 needs the intermediate point (3, 9),
because the pullback along `g` starts there. The
[*forward pass*](../appendix/glossary.md#forward-pass) computes such points:
it applies the maps in order, `f` first. The
[*reverse pass*](../appendix/glossary.md#reverse-pass) then pulls the seed
back along each map in the opposite order, `g` first.

The library's `pullback` runs the forward pass once and keeps its points for
the reverse pass. A pullback with the mode `recomputed` does not keep them:
its reverse pass computes each point again when it reads it. The library
declares a pullback with the mode `saved` only, and the program declares the
other one itself:

```vast
{{#include ../../examples/packages/stdlib-differential/main.vast:recomputed}}
```

A program can also hold the points of the forward pass as a value.
`linearize(F, x)` runs the forward pass and returns its points as a
[*tape*](../appendix/glossary.md#tape), and `backward(tape, η)` runs the
reverse pass over the tape. The three ways give one covector: codes 4 and 5
compare `pullback_recomputed(gAfterF, x, seed)` and
`backward(linearize(gAfterF, x), seed)` with `stepped`. A seed that does not
lie over the image of the tape's point gives the failure value here too.

## The differential

The [*differential*](../appendix/glossary.md#differential) of a function at
a point is the covector of its partial derivatives. For a smooth map `φ` from
`X` to `Line`, `differential(φ, p)` is the pullback of dt at `φ(p)` along
`φ` at `p`, so it needs no seed. `main` computes the differential of `g` at
the point (1, 2) as `differential(g(), p)`. The differential of `x² + y` is
`2x` dx + dy, which is 2 dx + dy at (1, 2). Code 7 reads the components 2
and 1 with `dx` and `dy`. The differential uses no metric.

## Metrics and gradients

A [*gradient*](../appendix/glossary.md#gradient) turns the differential into
a vector, and that step needs a
[*metric*](../appendix/glossary.md#smooth-metric): a symmetric bilinear form
on the vectors at a point, the same form at every point. The program
declares its metric, evidence for the metric, and the primitives and the
function that use it:

```vast
{{#include ../../examples/packages/stdlib-differential/main.vast:metric}}
```

`indexed metric Skew: MetricForm<Plane> = gram((2, 1), (1, 1));` declares a
metric on `Plane`. `MetricForm` is a family of the library, and the type
`MetricForm<Plane>` names the object of the metric. No value has this type:
a metric is a declaration, which other declarations name. `gram` gives the
[*Gram matrix*](../appendix/glossary.md#gram-matrix) of the metric by rows,
in the coordinates `x` and `y`. The matrix is constant, and it must be
symmetric.

`indexed evidence SkewInvertible = nondegenerate(Skew);` is
[*nondegenerate evidence*](../appendix/glossary.md#nondegenerate-evidence):
the statement that the Gram matrix has an inverse. The compiler computes the
inverse and checks it. It rejects the declaration for a matrix without an
inverse:

```vast
{{#include ../../examples/reject/packages/smooth-singular-metric/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/smooth-singular-metric.stderr}}
```

The bindings `flat` and `sharp` convert between vectors and covectors.
`flat_skew(v)` is the covector whose components are the Gram matrix times
the components of `v`. `sharp_skew(α)` is the vector whose components are
the inverse of the Gram matrix times the components of `α`, so the binding
`sharp` names the evidence that the inverse exists. Both bindings name their
metric with `using =`. The compiler chooses no metric: a `flat` binding
without `using =` is an error, even in a program with one metric.

`gradient` is an ordinary function: `sharp_skew` applied to the
differential. Under `Skew`, the gradient of `g` at (1, 2) is the vector
(1, 0), which codes 8 and 11 check. `flat_skew` sends it back to the
differential (code 9), and the pairing of the differential with it is 2
(code 10). With the Gram matrix `euclidean`, the identity matrix, the
gradient of `g` at (1, 2) is (2, 1): two metrics give two gradients of one
differential.

The metric, its evidence, `flat_skew`, `sharp_skew` and `gradient` stand in
the program, next to the metric that they name. A metric is not a value, and
a type such as `Tangent<X>` accepts a declared object and never a parameter.
So no function of a library takes the metric or the object of a program as
a parameter, and the standard library has no `gradient`.

## The observations

Two helper functions keep `main` short. `verdict` turns a failed observation
into its code, and `reads` compares a component with a fraction:

```vast
{{#include ../../examples/packages/stdlib-differential/main.vast:helpers}}
```

Each observation adds its code to 42 when it fails:

```vast
{{#include ../../examples/packages/stdlib-differential/main.vast:main}}
```

## Each declaration is its own object

An object is the declaration that introduces it. A second declaration with
the same dimension and the same coordinates is another object, and the
checker never confuses the two. In a program with the declarations of this
chapter, `Axis` is declared like the library's `Line`. The library's
`differential` takes a map into `Line`, and it does not accept a map into
`Axis`:

```vast
{{#include ../../examples/reject/packages/smooth-other-line/main.vast:program}}
```

```text
{{#include ../../examples/reject/packages/smooth-other-line.stderr}}
```

> **What is checked.** The checker rejects a seed, a point or a map over the
> wrong object before the compiler generates code, and the compiler builds
> only programs that it has checked. It then turns each reverse pass that it
> can read into ordinary code and checks that code again. The
> [proofs](../verification.md#smooth-affine-geometry-and-reverse-pullbacks)
> cover the generated reverse functions and the reverse pass over the checked
> program. They also cover the chain rule, the agreement of the saved and
> the recomputing passes, the comparison with the derivative of real
> analysis, and the meaning of metric evidence. Tests cover native execution,
> the diagnostics, the agreement of the tested programs with their source,
> and agreement with independent reference programs. A seed over the wrong
> point of the right object gives the failure value at run time, not an error
> of the compiler.

## See also

- [Smooth affine declarations](../language/smooth-declarations.md): the
  declaration forms, their rules and their diagnostics.
  [The smooth profile](../language/smooth-declarations.md#the-smooth-profile)
  has the families and the declarations of the standard library.
- [Smooth affine objects](../language/smooth-declarations.md#smooth-affine-objects)
  and [Smooth maps](../language/smooth-declarations.md#smooth-maps):
  `Affine(n)[…]`, `pullback(…)` and `identity`.
- [Polynomial expressions](../language/smooth-declarations.md#polynomial-expressions):
  the syntax of images and of the entries of a Gram matrix.
- [Smooth map primitives](../language/smooth-declarations.md#smooth-map-primitives)
  and [Fiber primitives](../language/smooth-declarations.md#fiber-primitives):
  composition, equality, points, covectors, vectors, components and
  pairings.
- [Reverse-pass primitives](../language/smooth-declarations.md#reverse-pass-primitives):
  pullbacks and their modes, differentials and tapes.
- [Metrics](../language/smooth-declarations.md#metrics),
  [Metric evidence](../language/smooth-declarations.md#metric-evidence) and
  [Flat and sharp](../language/smooth-declarations.md#flat-and-sharp).
- [Operand checks](../language/smooth-declarations.md#operand-checks): the
  errors of a call.
- [The standard library](https://github.com/MGYamada/Vastitas/blob/main/stdlib/README.md):
  the modules `std::geometry::smooth::affine`, `std::geometry::metric` and
  `std::differential`.
- [Smooth affine geometry and reverse pullbacks](../verification.md#smooth-affine-geometry-and-reverse-pullbacks):
  what is proved and what is tested.
