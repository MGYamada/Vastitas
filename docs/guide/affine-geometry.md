# Presented affine geometry

This chapter builds one program step by step. It declares geometric objects
by polynomial equations and maps between them. It then puts a curve over a
line, takes the fiber of the curve over a point, and restricts a map to an
open subset. Every coefficient in the program is an exact rational number,
and the program prints `42` only when every observation holds.

The program is
[`examples/packages/stdlib-affine/main.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/stdlib-affine/main.vast).
Run it from the repository root:

```sh
python3 scripts/build_stdlib_package.py
target/debug/vastitas build --manifest-path examples/packages/stdlib-affine/Vastitas.toml -o target/stdlib-affine
./target/stdlib-affine
```

The first command generates the standard library's package root; see
[using the standard library](stdlib.md#using-the-standard-library).

## Objects given by equations

A *presented affine object* has coordinates and polynomial relations between
them. Its points are the solutions of the relations. Its functions are the
polynomials in the coordinates, and two polynomials are the same function
when they differ by a multiple of the relations.

The standard library declares three such objects. The program imports them
with the family `Over`, the implementation `AffineQQ` and two functions:

```vast
{{#include ../../examples/packages/stdlib-affine/main.vast:imports}}
```

| Object | Declared as | Meaning |
| --- | --- | --- |
| `SpecQQ` | `spec[]` | A single point: it has no coordinates |
| `Line` | `spec[t] over SpecQQ` | The line with the coordinate `t` |
| `DualNumbers` | `spec[e] relations(e^2) over SpecQQ` | A point with a direction: `e` is not zero, and `e^2` is zero |

`spec[…]` lists the coordinates, and `relations(…)` lists the polynomials
that are zero on the object. `over SpecQQ` names the *base* of an object; a
[later section](#objects-over-a-base) uses bases. A program declares objects
of its own under the implementation `AffineQQ`.

## Morphisms are written as pullbacks

`Over<X, Y, S>` is the type of the morphisms from `X` to `Y` over the base
`S`. A declaration gives a morphism by what it does to functions. For each
coordinate of the target, it gives a polynomial in the coordinates of the
source:

```vast
{{#include ../../examples/packages/stdlib-affine/main.vast:points}}
```

`p` sends the coordinate `t` of the line to `e`. As a map of points, `p`
places the dual numbers on the line at `t = 0`, with their direction along
the line. `q` sends `t` to `0`: it places them at the same point and forgets
the direction. `closed` is the only point of the dual numbers. Each
declaration defines a function without parameters, so `p()` is the morphism.

A polynomial uses `+`, `-`, `*`, integer literals, `^` with a literal
exponent and `frac(n, d)` for a fraction.

The compiler checks that a morphism respects the relations of its target.
`e^2` is zero on the dual numbers, so its image must be zero on the source.
No morphism from the line to the dual numbers sends `e` to `t`, because
`t^2` is not zero on the line:

```vast
{{#include ../../examples/reject/packages/affine-relation/main.vast:declaration}}
```

```text
{{#include ../../examples/reject/packages/affine-relation.stderr}}
```

## Comparing morphisms

`same(f, g)` tells whether two morphisms are equal. A coefficient primitive
reads one coefficient of a morphism:

```vast
{{#include ../../examples/packages/stdlib-affine/main.vast:coefficient}}
```

`eps(f)` is the coefficient of `e` in the image of `t`. It is a `Pair<Int>`
of a numerator and a denominator, so `eps(p())` holds 1 and 1, and
`eps(q())` holds 0 and 1.

`compose(g, f)` is `g` after `f`. `p` and `q` differ, but
`compose(p(), closed())` and `compose(q(), closed())` are equal: both are
the point `t = 0` of the line. The two morphisms pass through one point and
differ in their direction. Codes 1 to 3 of [`main`](#the-observations) check
this.

## Composition

The order of the operands of `compose` matters:

```vast
{{#include ../../examples/packages/stdlib-affine/main.vast:composition}}
```

`sq` squares a point of the line, and `shift` adds one. `compose(sq(), shift())`
adds one and then squares, so it sends `t` to `(t + 1)^2`, which is
`t^2 + 2t + 1`. `slope` reads the coefficient of `t`, which is 2. In the
other order the image is `t^2 + 1`, and the coefficient is 0. Codes 4 and 5
check the two orders.

## Rational points

A point of the line is a morphism from `SpecQQ` to the line. One primitive
builds such a point from an integer, and another reads its coordinate:

```vast
{{#include ../../examples/packages/stdlib-affine/main.vast:rational-points}}
```

`at(3)` is the point `t = 3`. The image of `t` under a point is a constant,
and `value` reads it as the coefficient of the monomial `1`.
`compose(sq(), at(3))` is the point 9, which code 6 checks.

## Objects over a base

An object can lie over another object, its base. The declaration says how:

```vast
{{#include ../../examples/packages/stdlib-affine/main.vast:family}}
```

`Curve` is the curve `x^2 = t` in the plane with the coordinates `t` and `x`.
`over Line by(t -> t)` says that the curve lies over the line by sending the
point `(t, x)` to `t`. `by` gives each coordinate of the base as a polynomial
in the coordinates of the object. `Origin` is the point `t = 0` of the line,
and `DoublePoint` is a copy of the dual numbers over that point.

A morphism over the base `Line` must agree with these maps to the line.
`toCurve` sends `t` to `0` and `x` to `e`. The compiler accepts it for two
reasons. It respects the relation of the curve, because `e^2 - 0` is zero on
the double point. It agrees with the maps to the line, because both ways
from the double point to the line send `t` to `0`. The definition `structure`
names the map from an object to its base, and code 7 checks that
`curveToLine` after `toCurve` is `doubleToLine`.

A declaration over a base with coordinates must say where they go. Without
`by`, the compiler reports the coordinate that has no image:

```vast
{{#include ../../examples/reject/packages/affine-missing-image/main.vast:declaration}}
```

```text
{{#include ../../examples/reject/packages/affine-missing-image.stderr}}
```

## Changing the base

The third index of `Over` is part of the type. `sq` is a morphism over
`SpecQQ` and `curveToLine` is a morphism over `Line`, so `compose` rejects
the pair. Every object over the line also lies over `SpecQQ`, the base of the
line, and a view changes the base of a morphism accordingly:

```vast
{{#include ../../examples/packages/stdlib-affine/main.vast:view}}
```

`overPoint(curveToLine())` is the same morphism as `curveToLine()`, with the
type `Over<Curve, Line, SpecQQ>`. Followed by `sq`, it sends `t` to `t^2`.
On the curve `t` equals `x^2`, so `t^2` and `x^4` are the same function, and
code 8 checks that the composite equals `fourth`. The compiler compares
functions, not the polynomials as they are written.

## The fiber over a point

The fiber of the curve over the origin is the part of the curve where
`t = 0`:

```vast
{{#include ../../examples/packages/stdlib-affine/main.vast:fiber}}
```

`fiber(Curve, Origin)` is the fiber product of the two objects over their
common base, the line. Its coordinates are the coordinates of both factors,
each with the name of its factor in front, as in `Curve::x`. Its relations
are `x^2 = t` from the curve and `t = 0` from the origin, so `x^2` is zero
on the fiber. The fiber is a double point, not a single point: the two
square roots of `t` meet at the origin.

The program states this as a checked fact. `first` is the projection from
the fiber to its first factor, the curve. `lift(a, b)` combines a morphism to
the curve and a morphism to the origin into one morphism to the fiber.
`indexed cartesian` declares that `DoublePoint` with its morphisms `toCurve`
and `toOrigin` is the fiber: `back` must be the inverse of
`lift(toCurve(), toOrigin())`, and the compiler checks both composites. Code
9 checks that the lift followed by the projection is `toCurve`.

## Open subsets

`localize` declares the open subset of an object where a polynomial has an
inverse:

```vast
{{#include ../../examples/packages/stdlib-affine/main.vast:opens}}
```

`Punctured` is the line without its origin. It has the coordinates `t` and
`u` and the relation `u * t = 1`, so `u` is the inverse of `t`. `sq` maps a
point into `Punctured` exactly when its square is not zero, and
`PuncturedSq` is the open subset where `t^2` has the inverse `v`.
`restrict(sq)` is `sq` between the two open subsets. It sends `u` to `v`,
because the inverse of `t` pulls back to the inverse of `t^2`. Code 10 reads
that coefficient.

A morphism between open subsets can have an inverse:

```vast
{{#include ../../examples/packages/stdlib-affine/main.vast:transition}}
```

`invert` exchanges `t` and `u`: it sends a point of the punctured line to
its inverse. `indexed iso` declares that two morphisms are inverse to each
other, and the compiler checks both composites. Here `invert` is its own
inverse, and code 11 checks that `invert` after `invert` is the identity
morphism `stay`.

## The observations

Two helper functions keep `main` short. `verdict` turns a failed observation
into its code, and `reads` compares a coefficient with a fraction:

```vast
{{#include ../../examples/packages/stdlib-affine/main.vast:helpers}}
```

Each observation adds its code to 42 when it fails:

```vast
{{#include ../../examples/packages/stdlib-affine/main.vast:main}}
```

## Each declaration is its own object

An object is the declaration that introduces it. A second declaration with
the same coordinates and relations is another object, and the checker never
confuses the two. In this program `Copy` is declared like the library's
`Line`, and `same` receives one morphism into each:

```vast
{{#include ../../examples/reject/packages/affine-other-object/main.vast:program}}
```

```text
{{#include ../../examples/reject/packages/affine-other-object.stderr}}
```

To relate two such objects, a program declares morphisms between them and
states with `indexed iso` that they are inverse to each other.

> **What is checked.** The compiler computes with exact rational polynomials.
> It accepts a declaration only after it has checked each equation that the
> declaration states. These are the relations that a morphism respects, its
> agreement with the maps to the base, and both composites of an
> `indexed iso` or an `indexed cartesian` declaration. The compiler rejects
> a check that grows too large with `E_LIMIT`, and it accepts nothing
> unchecked. The [proofs](../verification.md#presented-affine-geometry) cover
> what an accepted declaration means. Two polynomials that the compiler
> finds equal are the same function. A declared fiber product has the
> universal property of a fiber product, and a declared open subset is the
> localization of its object. Tests cover native execution, the diagnostics
> and the agreement of the polynomial arithmetic with an independent
> reference program.

## See also

- [Presented affine declarations](../affine-geometry.md): the declaration
  forms, their rules and their diagnostics.
  [The presented profile](../affine-geometry.md#the-presented-profile) has
  the family `Over` and the standard library's declarations.
- [Presented affine objects](../affine-geometry.md#presented-affine-objects):
  coordinates, relations, bases and structure maps.
- [Morphisms over a base](../affine-geometry.md#morphisms-over-a-base) and
  [Morphism primitives](../affine-geometry.md#morphism-primitives):
  `pullback`, `structure`, composition, equality, views, coefficients and
  points.
- [Fiber products](../affine-geometry.md#fiber-products),
  [Cartesian squares](../affine-geometry.md#cartesian-squares),
  [Principal opens](../affine-geometry.md#principal-opens) and
  [Isomorphisms](../affine-geometry.md#isomorphisms).
- [Polynomial expressions](../language/smooth-declarations.md#polynomial-expressions):
  the syntax of relations and images.
- [Limits](../affine-geometry.md#limits) and
  [Operand checks](../affine-geometry.md#operand-checks): the bounds of the
  checks and the errors of a call.
- [The geometry library](https://github.com/MGYamada/Vastitas/blob/main/stdlib/src/geometry/README.md):
  the module `std::geometry::scheme::affine`.
- [Presented affine geometry](../verification.md#presented-affine-geometry)
  in the verification boundaries: what is proved and what is tested.
