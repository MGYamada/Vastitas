# Gluing charts

The projective line is the line with one point added at infinity. No single
line covers it, but two lines do. One line has the coordinate x and misses
the point at infinity. The other has the coordinate y and misses the origin
of the first. Where both are defined, a point has the coordinates x and
y = 1/x. Gluing is the construction that builds the projective line from
these two pieces.

This chapter builds one program that glues in this way. It glues the
projective line over the rational numbers, checks that the result is
separated and that it is the projective line, and certifies that two open
subsets cover the line. It then glues the real projective line, a circle,
from two real lines. Every check is exact. The glued objects and their
claims have no value at run time. The executable composes morphisms of the
earlier chapters with the same images as the transition, writes
`failures = 0` and exits with status 0.

The program is the package
[`examples/packages/geometry/projective-line/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/geometry/projective-line).
Run it from the repository root:

```sh
python3 scripts/build_stdlib_package.py
target/debug/vastitas build --manifest-path examples/packages/geometry/projective-line/Vastitas.toml -o target/projective-line
./target/projective-line
```

The first command generates the standard library's package root; see
[using the standard library](stdlib.md#using-the-standard-library).

## Two charts

The two pieces are two lines and an open subset of each:

```vast
{{#include ../../examples/packages/geometry/projective-line/src/main.vast:charts}}
```

`L1` and `L2` are lines over the point `SpecQQ`, with the coordinates `x`
and `y`. They are two declarations, so they are two objects, although their
presentations agree. `localize` declares the open subset on which a
polynomial has an inverse, as in
[Presented affine geometry](affine-geometry.md#open-subsets). `U1` is the
first line without its origin, and `xi` is the inverse of `x` there. `U2` is
the second line without its origin, with the inverse `yi` of `y`. The two
lines are the charts of the gluing, and `U1` and `U2` are the parts that
overlap.

## Gluing along a transition

`indexed glued` glues the two lines along their open subsets:

```vast
{{#include ../../examples/packages/geometry/projective-line/src/main.vast:glue}}
```

`glue(U1, U2)` names the open subsets. `by(…)` says how a point of `U1` is
a point of `U2`, and `inverse(…)` says the way back. Like a morphism, `by`
gives each coordinate of its target as a polynomial in the coordinates of
its source: `y` is `xi` and `yi` is `x`. So the point x of the first line is
the point 1/x of the second. `inverse` sends `x` to `yi` and `xi` to `y`.

The compiler checks that both maps respect the relations `x * xi = 1` and
`y * yi = 1`, that they undo each other, and that they agree with the maps
of both lines to `SpecQQ`. A map that sends y to 2/x breaks the relation of
`U2`:

```vast
{{#include ../../examples/reject/packages/gluing-broken-relation/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/gluing-broken-relation.stderr}}
```

A gluing has exactly two charts. Three charts would need conditions on the
parts where all three overlap, and the compiler checks no such condition, as
[Glued objects](../language/gluing.md#glued-objects) says.

## Is the gluing separated?

The same lines glued by y = x instead of y = 1/x give another object:

```vast
{{#include ../../examples/packages/geometry/projective-line/src/main.vast:doubled}}
```

`Doubled` is the line with a doubled origin. Away from the origins, the two
lines are glued point by point. The two origins are not glued, and no
function tells them apart. The gluing is valid, so the compiler accepts it.
A gluing on its own says nothing about whether the result is separated.

A separation claim says it, with a witness:

```vast
{{#include ../../examples/packages/geometry/projective-line/src/main.vast:separated}}
```

`by(xi -> L2::y)` claims that the inverse `xi` of the first chart is the
polynomial `L2::y` of the coordinates of both charts. Each coordinate
carries the name of its chart, as the coordinates of a fiber product do.
The transition sends `y` to `xi`, so the claim holds on the overlap. The
witness shows that every function on the overlap comes from the two
charts. For a gluing of two lines, this is what separated means.

For the doubled origin the transition sends `y` to `x`, and no polynomial
in `x` and `y` is 1/x on the overlap:

```vast
{{#include ../../examples/reject/packages/gluing-not-separated/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/gluing-not-separated.stderr}}
```

## The projective line

A projective claim states that the glued object is the projective line:

```vast
{{#include ../../examples/packages/geometry/projective-line/src/main.vast:projective}}
```

A point of the projective line is a pair (s : t), up to a common factor,
with s and t not both zero. The standard chart where s is not zero has the
coordinate t/s, and the standard chart where t is not zero has the
coordinate s/t. `chart(L1, s, x)` says that `L1` is the chart where s is
not zero, with x = t/s, so its points are (1 : x). `inverse(x -> t)` gives
`x` back from the coordinate of that chart, which the name `t` stands for.
The second entry says that `L2` is the chart where t is not zero, with
y = s/t, so its points are (y : 1).

The compiler checks that each line is its standard chart, and that `U1`
and `U2` are the parts of the charts where both s and t are not zero. It
checks that the points (1 : x) and (y : 1) agree where the charts overlap:
there y = 1/x, so (y : 1) = (1 : x). For the doubled origin the same
entries fail, because y = x on its overlap:

```vast
{{#include ../../examples/reject/packages/gluing-wrong-projective/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/gluing-wrong-projective.stderr}}
```

## A cover of the line

A cover states that open subsets cover an object:

```vast
{{#include ../../examples/packages/geometry/projective-line/src/main.vast:cover}}
```

`Dt` is the line of the standard library without the point t = 0, and
`Dmt` is the line without t = 1. `by(1, 1)` gives a coefficient for each
open subset, and the compiler checks that 1 · t + 1 · (1 − t) = 1. At each
point t or 1 − t is then not zero, so the point lies in one of the two open
subsets.

The polynomial t² + 1 is not zero at any real point, but its open subset
is no cover of the line over the rational numbers: it misses the point
where t² + 1 = 0, which has no rational coordinate. No coefficient makes
the identity hold:

```vast
{{#include ../../examples/reject/packages/gluing-false-cover/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/gluing-false-cover.stderr}}
```

## The real projective line

The same construction works for real lines:

```vast
{{#include ../../examples/packages/geometry/projective-line/src/main.vast:smooth}}
```

`SmoothR` is the smooth implementation of the standard library, and
`Affine(1)` declares a real line, as in
[Smooth geometry and reverse pullbacks](smooth-geometry.md). Under a smooth
implementation, `localize` declares the open subset of the real points on
which the polynomial is not zero: `W1` is the line without x = 0, and `u`
is 1/x there. `RP1` glues the two lines by y = 1/x. It is the real
projective line, a circle.

`manifold(RP1, 1)` claims that the real points of `RP1` form a manifold of
dimension 1. Its witness has the form of a separation witness, and it shows
that any two points of the glued space have disjoint neighborhoods.

The implementation of a gluing chooses its kind of open subset. The open
subsets `U1` and `U2` of the presented lines cannot be glued under
`SmoothR`:

```vast
{{#include ../../examples/reject/packages/gluing-swapped-site/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/gluing-swapped-site.stderr}}
```

The real lines glued by y = x form the real line with a doubled origin. Its
two origins have no disjoint neighborhoods, and its manifold claim fails:

```vast
{{#include ../../examples/reject/packages/gluing-not-manifold/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/gluing-not-manifold.stderr}}
```

## The observations

A glued object, a cover and a claim are checked when the program is
compiled, and they have no value. A function cannot name them, and the
program generates the same code without them. The executable composes
morphisms over `SpecQQ` that have the same images as the transition of `P`.
They are separate declarations with values, and nothing ties them to `P`:

```vast
{{#include ../../examples/packages/geometry/projective-line/src/main.vast:observers}}
```

`there` and `back` have the images of `by(…)` and `inverse(…)`. `main`
checks that both composites are identities, which the gluing checked when
the program was compiled:

```vast
{{#include ../../examples/packages/geometry/projective-line/src/main.vast:main}}
```

> **What is checked.** The compiler checks each gluing, cover and claim by
> identities of exact rational polynomials before it generates code: the
> relations and both composites of a transition, the identity of a cover,
> the witness of a separation or a manifold claim, and the charts and the
> overlap of a projective claim. It accepts nothing unchecked, and it
> rejects a check that grows too large with `E_LIMIT`. The
> [proofs](../verification.md#gluing-two-charts) cover what an accepted
> declaration satisfies: the identities that it states, and the kind of
> open subsets that it reads. Tests cover the diagnostics of the rejected
> programs, the records that the compiler sends to its checker, native
> execution, and the program without its gluing declarations, which
> generates the same code. That the glued object is the projective line or
> a circle in the sense of a library of mathematics is not proved.

## See also

- [Gluing declarations](../language/gluing.md): the declaration forms,
  their rules and their diagnostics.
- [Sites](../language/gluing.md#sites) and
  [Smooth opens](../language/gluing.md#smooth-opens): the two kinds of open
  subsets and the open subsets of real lines.
- [Glued objects](../language/gluing.md#glued-objects) and
  [Covers](../language/gluing.md#covers): `glue(…)` and `cover(…)`.
- [Separation claims](../language/gluing.md#separation-claims),
  [Manifold claims](../language/gluing.md#manifold-claims) and
  [Projective claims](../language/gluing.md#projective-claims): the
  witnesses and the chart entries.
- [Principal opens](../affine-geometry.md#principal-opens) and
  [Smooth affine objects](../language/smooth-declarations.md#smooth-affine-objects):
  the charts and their open subsets.
- [Gluing two charts](../verification.md#gluing-two-charts) in the
  verification boundaries: what is proved and what is tested.
