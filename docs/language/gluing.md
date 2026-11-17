# Gluing declarations

This chapter defines the declarations that glue two affine charts along open
subsets and that state checked facts about the result: smooth opens, glued
objects, covers, and separation, manifold and projective claims. Each chart
is a [presented affine object](../affine-geometry.md#presented-affine-objects)
over the rational numbers or a
[smooth affine object](smooth-declarations.md#smooth-affine-objects)
$\mathbb{R}^n$. A gluing identifies an open subset of the first chart with an
open subset of the second. The general rules of `indexed` declarations are in
[Indexed declarations](../indexed-source.md). [Notation](notation.md)
explains the Syntax blocks, and the [glossary](../appendix/glossary.md)
defines the terms.

These declarations compute nothing. None of them is a value: a path in a
function body that names one is an error (`E_TYPE`), and so is a call of one.
They change no value of a program, and a program without them generates the
same code. Every check of this chapter is an identity of polynomials with
rational coefficients, which the compiler decides by exact arithmetic within
the bounds of [Limits](#limits).

A path in a declaration of this chapter that resolves to nothing is an error
of [resolution](names-and-paths.md#resolution) (`E_NAME`), before the rules
of this chapter apply. A declaration may name a declaration that its module
declares after it. The compiler checks the glued objects and the covers
before the claims, so a program reports the first error in that order.

The examples quote the tested package
[`examples/packages/geometry/projective-line/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/geometry/projective-line),
which glues the projective line over the rational numbers and the real
projective line, each from two lines. Its executable writes `failures = 0`
and exits with status 0. Each rejected program is a package on the profile
of the standard library. It appears with the diagnostic that the compiler
prints for it.

The declarations of this chapter are the forms of `GluingDeclaration`:

> **Syntax**
>
> ```text
> GluingDeclaration -> GluedDeclaration | CoverDeclaration
>     | SeparationDeclaration | ManifoldDeclaration | ProjectiveDeclaration
> ```

Each declaration of this chapter is an [item](items.md): `GluingDeclaration`
is one form of [`IndexedDeclaration`](../indexed-source.md). `pub` before a
declaration makes it visible outside its module. A
[smooth open](#smooth-opens) has the form of a principal open, a
`PresentedObjectDeclaration` of
[Principal opens](../affine-geometry.md#principal-opens), and it has no
production of its own.
[Classifications](../indexed-source.md#classifications) defines `Paths`,
[Smooth affine objects](smooth-declarations.md#smooth-affine-objects)
defines `Coordinates`, and [Smooth maps](smooth-declarations.md#smooth-maps)
defines `ImageBindings` and `ImageBinding`. The images, coefficients and
witnesses of this chapter are
[polynomial expressions](smooth-declarations.md#polynomial-expressions), and
the rules of that section apply to each of them.

> **Implementation note.** `IndexedGluingSource.lean` elaborates the
> declarations of this chapter and gives their diagnostics.
> `GluingValidity.lean` holds the checks of the declaration audit, which run
> the actions of `GluingDeclarations.lean`. Elaboration runs the same
> actions, so an elaborated declaration passes its audit.
> [Gluing forms](../protocol.md#gluing-forms) gives the records of the wire.

## Sites

A **site** is the kind of open subset along which a declaration of this
chapter glues and by which it covers. The implementation of a declaration
chooses its site, and the site fixes which declarations are its objects and
its opens:

| Implementation | Site | Objects | Opens of an object `X` |
| --- | --- | --- | --- |
| `presented_affine(rational)` | The **Zariski site** | [Presented affine objects](../affine-geometry.md#presented-affine-objects) | The [principal opens](../affine-geometry.md#principal-opens) `localize(X, f)`: the open subsets $D(f)$ of $\operatorname{Spec} A$ on which $f$ is a unit |
| `smooth_affine` | The **smooth site** | [Smooth affine objects](smooth-declarations.md#smooth-affine-objects) | The [smooth opens](#smooth-opens) `localize(X, f)`: the open subsets $\{x \in \mathbb{R}^n : f(x) \neq 0\}$ |

The two sites read one polynomial in two ways. In the Zariski site,
$D(t^2 + 1)$ is a proper open subset of the line over the rational numbers:
it misses the closed point $(t^2 + 1)$, which has no rational coordinate. In
the smooth site, $\{t^2 + 1 \neq 0\}$ is the whole real line. No declaration
converts an object or an open of one site into the other.

Rules:

- Every object and every open that a declaration of this chapter names must
  belong to the site of the declaration and have its implementation.
  Otherwise it is an error (`E_GLUE`). In particular, a principal open in the
  smooth site and a smooth open in the Zariski site are errors.

The following gluing names the principal opens of two lines under the
smooth implementation of the standard library:

```vast
{{#include ../../examples/reject/packages/gluing-swapped-site/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/gluing-swapped-site.stderr}}
```

## Smooth opens

`indexed affine W(Impl) = localize(X, f) inverse u;` under a `smooth_affine`
implementation `Impl` declares the **smooth open** $\{f \neq 0\}$ of the
smooth affine object `X`: the open subset of $\mathbb{R}^n$ on which the
polynomial $f$ is not zero. The declaration has the form of a
[principal open](../affine-geometry.md#principal-opens), and it has the
presentation that a principal open derives:

- Its coordinates are the coordinates of `X` and then `u`.
- Its relation is $u f - 1$.

The real points $(x, u)$ with $u f(x) = 1$ are the points $x$ of
$\{f \neq 0\}$, each with $u = 1/f(x)$. The polynomials in the coordinates of
the presentation are the functions on the open that are polynomials in the
coordinates of `X` and in $1/f$.

A smooth open is neither a smooth affine object nor a presented affine
object. It is an open of a [glued object](#glued-objects) or of a
[cover](#covers), and no other declaration takes it.

Rules:

- `X` must be a smooth affine object of the implementation of the open.
  Otherwise it is an error (`E_SMOOTH`), including a presented affine object,
  a smooth open and a smooth affine object of another implementation.
- `f` must be a polynomial expression in the coordinates of `X`. Any other
  name is an error (`E_AFFINE_COORDINATE`).
- `u` must differ from every coordinate of `X`. Otherwise it is an error
  (`E_AFFINE_COORDINATE`).
- `X` must have at most 15 coordinates, so that the open has at most 16
  (`E_LIMIT`).
- `f` may be zero. The smooth open is then empty.
- A declaration of another chapter that names a smooth open where it
  requires an object has the error that it gives for any other declaration
  there. For example, a smooth map whose source is a smooth open is an error
  (`E_SMOOTH`), and so is a presented affine object over a smooth open
  (`E_AFFINE_BASE`).

> **Implementation note.** The kernel derives the presentation of each
> smooth open from the coordinates of its object before it elaborates the
> presented affine objects, and the declaration audit derives it again and
> compares it. A request carries a smooth open as the record of a principal
> open.

Example, from
[`main.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/geometry/projective-line/src/main.vast):

```vast
{{#include ../../examples/packages/geometry/projective-line/src/main.vast:smooth-opens}}
```

`M1` and `M2` are two real lines. `W1` is the open $\{x \neq 0\}$ of `M1`,
on which `u` is $1/x$, and `W2` is the open $\{y \neq 0\}$ of `M2`, on which
`v` is $1/y$.

## Glued objects

> **Syntax**
>
> ```text
> GluedDeclaration -> `indexed` `glued` IDENTIFIER `(` Path `)` `=` `glue`
>     `(` Paths? `)` `by` `(` ImageBindings? `)`
>     `inverse` `(` ImageBindings? `)` `;`
> ```

`indexed glued P(Impl) = glue(U1, U2) by(c₁ -> p₁, …) inverse(d₁ -> q₁, …);`
declares a **glued object** under the implementation `Impl`, whose site
[Sites](#sites) gives. `U1` and `U2` are opens $U_1 \subset X_1$ and
$U_2 \subset X_2$ of that site, and the objects $X_1$ and $X_2$ are the two
**charts** of `P`. `by(…)` gives each coordinate $c_i$ of $U_2$, the
coordinates of $X_2$ and the inverse coordinate of $U_2$, its image $p_i$, a
polynomial expression in the coordinates of $U_1$. These images define the
**chart transition** $\varphi \colon U_1 \to U_2$, whose ring map sends each
$c_i$ to $p_i$, as a [pullback](../affine-geometry.md#morphisms-over-a-base)
does. `inverse(…)` gives each coordinate $d_j$ of $U_1$ its image $q_j$ in
the coordinates of $U_2$. These images define a map
$\psi \colon U_2 \to U_1$.

`P` is the union of the two charts in which each point $u$ of $U_1$ is the
point $\varphi(u)$ of $U_2$. In the Zariski site it is the scheme glued from
$X_1$ and $X_2$ along the isomorphism $\varphi$. In the smooth site its
points are the real points of the two charts, glued along the
diffeomorphism $\varphi$ between the two open subsets. With two charts the
chart transition and its inverse are all the data of the gluing: no
condition on triple overlaps arises.

A glued object is a declaration with no value. It is neither a presented
affine object nor a smooth affine object, so no family takes it as an index
and no morphism has it as its source or its target. A
[separation claim](#separation-claims), a
[manifold claim](#manifold-claims) and a
[projective claim](#projective-claims) state its properties. A glued object
need not be separated or Hausdorff, and the gluing alone proves neither.

Rules:

- `glue(…)` must name exactly two opens. Otherwise it is an error
  (`E_GLUE`). Three or more charts would need conditions on their triple
  overlaps, which the language does not check.
- The implementation must be a `presented_affine` or a `smooth_affine`
  implementation. Otherwise it is an error (`E_GLUE`).
- Each open must be an open of an object of the implementation in its
  site. Otherwise it is an error (`E_GLUE`), including a presented affine
  object or a smooth affine object in the place of an open.
- The two opens must be opens of two different charts. Two opens of one
  chart are an error (`E_GLUE`), even when their polynomials differ.
- In the Zariski site, the two charts must have one base: one declaration,
  or no base for both. Otherwise it is an error (`E_GLUE`).
- `by(…)` must give each coordinate of $U_2$ exactly one image, and
  `inverse(…)` each coordinate of $U_1$. A missing, repeated or unknown
  coordinate is an error (`E_AFFINE_COORDINATE`).
- Each image of `by(…)` must be a polynomial expression in the coordinates
  of $U_1$, and each image of `inverse(…)` one in the coordinates of $U_2$.
  Any other name is an error (`E_AFFINE_COORDINATE`). A declaration may list
  the images in any order.
- $\varphi$ must send every relation of $U_2$ to zero in the coordinate ring
  of $U_1$, and $\psi$ every relation of $U_1$ to zero in the coordinate ring
  of $U_2$. Otherwise it is an error (`E_GLUE`).
- $\psi \circ \varphi$ must be the identity of $U_1$, and
  $\varphi \circ \psi$ the identity of $U_2$. Otherwise it is an error
  (`E_GLUE`).
- In the Zariski site over a base $B$, $\varphi$ must commute with the
  structure maps to $B$: each coordinate of $B$ must have one image along
  $U_1 \to X_1 \to B$ and along $U_1 \to U_2 \to X_2 \to B$. Otherwise it is
  an error (`E_GLUE`).
- The [limits](#limits) apply to the checks of this section.

> **Implementation note.** The kernel stores each image as its normal form
> in the coordinate ring of its source. It runs the checks of the two maps,
> of their composites and of the structure maps in one run of the
> arithmetic.

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/geometry/projective-line/src/main.vast:charts}}
{{#include ../../examples/packages/geometry/projective-line/src/main.vast:glue}}
```

`L1` and `L2` are two lines over `SpecQQ`. `U1` is $D(x)$, on which `xi` is
$1/x$, and `U2` is $D(y)$, on which `yi` is $1/y$. The chart transition sends
`y` to `xi` and `yi` to `x`: it identifies the point $x$ of `U1` with the
point $y = 1/x$ of `U2`. Its inverse sends `x` to `yi` and `xi` to `y`. `P`
is the projective line over the rational numbers, as the
[projective claim](#projective-claims) of the program checks.

The same lines glued by $y = x$ are the line with a doubled origin. It is a
glued object too, and its [separation claim](#separation-claims) fails:

```vast
{{#include ../../examples/packages/geometry/projective-line/src/main.vast:doubled}}
```

A third chart is an error:

```vast
{{#include ../../examples/reject/packages/gluing-third-chart/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/gluing-third-chart.stderr}}
```

The map $y = 2/x$ sends the relation $y \cdot y_i - 1$ of `U2` to
$2 \cdot x_i \cdot x - 1$, which is 1 in the coordinate ring of `U1`:

```vast
{{#include ../../examples/reject/packages/gluing-broken-relation/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/gluing-broken-relation.stderr}}
```

The maps $y = -1/x$ and $x = 1/y$ each respect the relations, but their
composite sends $x$ to $-x$, so they are not inverse to each other:

```vast
{{#include ../../examples/reject/packages/gluing-not-inverse/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/gluing-not-inverse.stderr}}
```

## Covers

> **Syntax**
>
> ```text
> CoverDeclaration -> `indexed` `cover` IDENTIFIER `=` `cover` `(` Paths `)`
>     `by` `(` Coefficients? `)` `;`
> Coefficients -> Polynomial ( `,` Polynomial )* `,`?
> ```

`indexed cover c = cover(X, U1, …, Uk) by(a₁, …, aₖ);` declares a
**cover**: the checked statement that the opens $U_i$ of the object `X`, with
the polynomials $f_i$, cover `X`. The coefficients $a_i$ are polynomial
expressions in the coordinates of `X`. They certify the cover by the
identity

$$
\sum_i a_i f_i = 1
$$

in the coordinate ring of `X`, which says that the $f_i$ generate the unit
ideal. In the Zariski site this is the condition for the principal opens
$D(f_i)$ to cover $\operatorname{Spec} A$: no prime ideal contains every
$f_i$. In the smooth site the identity gives some $f_i(x) \neq 0$ at every
real point $x$, so the smooth opens cover $\mathbb{R}^n$. The converse fails
in the smooth site. $\{t^2 + 1 \neq 0\}$ is the whole real line, but no
polynomial $a$ gives $a \cdot (t^2 + 1) = 1$, so no cover declaration states
that this open covers the line.

A cover is a declaration with no value, and no other declaration names it.

Rules:

- `cover(…)` must name the object `X` first and then its opens. An empty
  list is an error (`E_PARSE`).
- `X` must be a presented affine object or a smooth affine object.
  Otherwise it is an error (`E_GLUE`), including a glued object and an open.
  The implementation of `X` chooses the site of the cover.
- Each open must be an open of `X` in its site. Otherwise it is an error
  (`E_GLUE`), including an open of another object.
- An open must not appear twice. Otherwise it is an error (`E_GLUE`).
- A cover must name at most `algebraRelations` = 32 opens. Otherwise it is
  an error (`E_LIMIT`).
- `by(…)` must give exactly one coefficient for each open, and a cover must
  name at least one open. Otherwise it is an error (`E_AFFINE_COORDINATE`).
- Each coefficient must be a polynomial expression in the coordinates of
  `X`. Any other name, including the inverse coordinate of an open, is an
  error (`E_AFFINE_COORDINATE`).
- $\sum_i a_i f_i - 1$ must be zero in the coordinate ring of `X`. Otherwise
  it is an error (`E_GLUE`).
- The [limits](#limits) apply to the check.

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/geometry/projective-line/src/main.vast:cover}}
```

`Line` is the line of the standard library. Its opens $D(t)$ and
$D(1 - t)$ cover it, because $1 \cdot t + 1 \cdot (1 - t) = 1$.

$D(t^2 + 1)$ alone is no Zariski cover of the line:

```vast
{{#include ../../examples/reject/packages/gluing-false-cover/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/gluing-false-cover.stderr}}
```

## Separation claims

> **Syntax**
>
> ```text
> SeparationDeclaration -> `indexed` `separated` IDENTIFIER `=` `separated`
>     `(` Path `)` Witness `;`
> Witness -> `by` `(` ImageBinding `,`? `)`
> ```

`indexed separated s = separated(P) by(u -> w);` declares a **separation
claim**: the checked statement that the glued object `P` of the Zariski site
is separated. The binding `u -> w` is its **separation witness**. `u` names
the inverse coordinate of the first open $U_1 = D(f_1)$ of `P`, which is
$1/f_1$ in the coordinate ring of $U_1$. `w` is a polynomial expression in
the coordinates of both charts. Each coordinate carries the name of its
chart, as in `L1::x` and `L2::y`, like a coordinate of a
[fiber product](../affine-geometry.md#fiber-products). When both charts have
the same name, the qualifiers are `first` and `second`.

The compiler replaces each coordinate of $X_1$ in `w` by itself and each
coordinate of $X_2$ by its image under the chart transition. It requires the
result to equal `u` in the coordinate ring of $U_1$. The witness then shows
that the ring map

$$
\mathcal{O}(X_1) \otimes \mathcal{O}(X_2) \to \mathcal{O}(U_1), \qquad
a \otimes b \mapsto a \cdot \varphi^{\#}(b)
$$

is onto: its image holds the coordinates of $X_1$ and $1/f_1$, which
generate $\mathcal{O}(U_1)$. So the embedding of $U_1$ in $X_1 \times X_2$
by the inclusion and by $\varphi$ is a closed immersion, which is the
criterion for a scheme glued from two affine charts to be separated. Every
separated gluing has a witness, because a preimage of $1/f_1$ is one. The
compiler checks the witness of the declaration and searches for no other.

Rules:

- The path must name a glued object. Otherwise it is an error (`E_GLUE`).
- The glued object must belong to the Zariski site. A glued object of the
  smooth site is an error (`E_GLUE`), and a
  [manifold claim](#manifold-claims) states its property.
- The witness must be exactly one binding. Otherwise it is an error
  (`E_PARSE`).
- The name before `->` must be the inverse coordinate of the first open of
  the glued object. Otherwise it is an error (`E_GLUE`).
- `w` must be a polynomial expression in the qualified coordinates of the
  two charts. Any other name is an error (`E_AFFINE_COORDINATE`), including
  a coordinate without its qualifier and the inverse coordinate of an open.
- With each coordinate of the second chart replaced by its image under the
  chart transition, `w` must equal `u` in the coordinate ring of $U_1$.
  Otherwise it is an error (`E_GLUE`), even when the glued object is
  separated with another witness.
- The [limits](#limits) apply to the check.

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/geometry/projective-line/src/main.vast:separated}}
```

The chart transition of `P` sends `y` to `xi`, so `L2::y` is $1/x$ on the
overlap. In the doubled origin the transition sends `y` to `x`, and no
polynomial in $x$ and $y$ is $1/x$ on the overlap:

```vast
{{#include ../../examples/reject/packages/gluing-not-separated/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/gluing-not-separated.stderr}}
```

## Manifold claims

> **Syntax**
>
> ```text
> ManifoldDeclaration -> `indexed` `manifold` IDENTIFIER `=` `manifold`
>     `(` Path `,` INTEGER_LITERAL `)` Witness `;`
> ```

`indexed manifold m = manifold(R, n) by(u -> w);` declares a **manifold
claim**: the checked statement that the real points of the glued object `R`
of the smooth site form a smooth manifold of dimension `n`. Both charts of
`R` have dimension `n`, and `u -> w` is a
[separation witness](#separation-claims) with the check of that section.

The witness gives $1/f_1$ at a point $x$ of $U_1$ as the polynomial
$w(x, \varphi(x))$. A point $(x, y)$ of $\mathbb{R}^n \times \mathbb{R}^n$
then lies on the graph of $\varphi$ exactly when $f_1(x)\, w(x, y) = 1$ and
$y$ is the image of $x$ under the chart transition, with $w(x, y)$ in the
place of $1/f_1(x)$. These are polynomial equations, so the graph is closed,
and the glued space is Hausdorff. The two charts are copies of
$\mathbb{R}^n$, and the chart transition and its inverse are smooth, so the
glued space has a smooth atlas of two charts. Two charts make it second
countable.

The witness is sufficient, not necessary. The two real lines glued by the
identity along $\{t^2 + 1 \neq 0\}$ form the real line, which is Hausdorff.
No polynomial in the coordinates of the two charts is $1/(t^2 + 1)$ on the
overlap, so the manifold claim of that gluing is an error.

Rules:

- The path must name a glued object of the smooth site. A glued object of
  the Zariski site is an error (`E_GLUE`), and a
  [separation claim](#separation-claims) states its property. Any other
  declaration is an error (`E_GLUE`).
- The dimension must be an unsigned integer literal. Otherwise it is an
  error (`E_PARSE`). It must have at most 64 decimal digits. Otherwise it is
  an error (`E_LIMIT`).
- Both charts must have dimension `n`. Otherwise it is an error (`E_GLUE`).
- The rules of the witness of [separation claims](#separation-claims)
  apply.

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/geometry/projective-line/src/main.vast:smooth}}
```

`RP1` glues the two real lines by $y = 1/x$. It is the real projective
line, a circle. The witness `u -> M2::y` states that $1/x$ is the coordinate
$y$ of the second chart on the overlap.

The real lines glued by $y = x$ are the real line with a doubled origin,
whose two origins have no disjoint neighborhoods:

```vast
{{#include ../../examples/reject/packages/gluing-not-manifold/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/gluing-not-manifold.stderr}}
```

## Projective claims

> **Syntax**
>
> ```text
> ProjectiveDeclaration -> `indexed` `projective` IDENTIFIER `=` `proj`
>     `(` Path `)` `[` Coordinates? `]` ProjectiveChart* `;`
> ProjectiveChart -> `chart` `(` Path `,` IDENTIFIER `,` Polynomial `)`
>     `inverse` `(` ImageBindings? `)`
> ```

`indexed projective h = proj(P)[s, t] chart(X1, c₁, p₁) inverse(…) chart(X2, c₂, p₂) inverse(…);`
declares a **projective claim**: the checked statement that the glued object
`P` of the Zariski site is isomorphic to the projective line
$\operatorname{Proj} \mathbb{Q}[s, t]$. `s` and `t` are its **homogeneous
coordinates**. The projective line is the union of its two **standard
charts**: $D_+(s) = \operatorname{Spec} \mathbb{Q}[t/s]$, on which $s$ is a
unit, and $D_+(t) = \operatorname{Spec} \mathbb{Q}[s/t]$. They overlap in
$D_+(st)$.

An entry `chart(X, c, p) inverse(…)` states that the chart `X` of `P` is the
standard chart $D_+(c)$. The polynomial `p`, in the coordinates of `X`, is
the image of the coordinate of $D_+(c)$: the other homogeneous coordinate
divided by `c`. The homogeneous coordinates on `X` are therefore $(1 : p)$
when `c` is `s`, and $(p : 1)$ when `c` is `t`. `inverse(…)` gives each
coordinate of `X` as a polynomial expression in the coordinate of $D_+(c)$,
which the name of the other homogeneous coordinate denotes. In
`chart(L1, s, x) inverse(x -> t)`, `t` stands for $t/s$.

The compiler checks that each chart map is an isomorphism onto its standard
chart, and that the open of each chart in `P` is the preimage of the
overlap $D_+(st)$. It checks that the homogeneous coordinates of the two
charts agree on the overlap of `P`. With $(s_1 : t_1)$ the homogeneous
coordinates of the first chart and $(s_2 : t_2)$ those of the second, this
is the identity

$$
s_1 \cdot \varphi^{\#}(t_2) - t_1 \cdot \varphi^{\#}(s_2) = 0
$$

in the coordinate ring of $U_1$. Together the checks make the two chart
isomorphisms agree on the overlap, so that they glue to an isomorphism of
`P` with the projective line.

Rules:

- The path must name a glued object of the Zariski site. Otherwise it is an
  error (`E_GLUE`), including a glued object of the smooth site.
- The homogeneous coordinates must be exactly two distinct names. Otherwise
  it is an error (`E_GLUE`).
- Each chart of the glued object must have no base, or a base without
  coordinates and without relations, such as `SpecQQ`. Otherwise it is an
  error (`E_GLUE`).
- The claim must give exactly one entry for each chart of the glued object,
  in either order. A missing entry, a third entry and an entry for another
  object are an error (`E_GLUE`).
- The second argument of each entry must be a homogeneous coordinate, and
  the two entries must name different homogeneous coordinates. Otherwise it
  is an error (`E_GLUE`).
- `p` must be a polynomial expression in the coordinates of the chart, and
  `inverse(…)` must give each coordinate of the chart exactly one image, a
  polynomial expression in the other homogeneous coordinate. Any other name,
  and a missing or repeated coordinate, is an error (`E_AFFINE_COORDINATE`).
- The chart map and its inverse must be inverse to each other: the inverse
  must send every relation of the chart to zero, and both composites must be
  identities. Otherwise it is an error (`E_GLUE`).
- The polynomial of the open of the chart and `p` must have one normal form
  in the coordinate ring of the chart, so that the open is the preimage of
  the overlap. Otherwise it is an error (`E_GLUE`), even when the two
  polynomials differ by a nonzero constant and so define one open.
- The homogeneous coordinates must agree on the overlap, as the identity
  above states. Otherwise it is an error (`E_GLUE`).
- The [limits](#limits) apply to the checks of a claim.

> **Implementation note.** The kernel stores the chart entries in the order
> of the opens of the glued object, whatever their order in the source, and
> it stores the homogeneous coordinate of each entry as its index.

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/geometry/projective-line/src/main.vast:projective}}
```

The first chart is $D_+(s)$ with $t/s = x$, and the second is $D_+(t)$ with
$s/t = y$. The homogeneous coordinates $(1 : x)$ and $(y : 1)$ agree on the
overlap: the identity is $1 \cdot 1 - x \cdot x_i = 0$, the relation of
`U1`.

The doubled origin has the same charts, and its chart transition sends $y$
to $x$:

```vast
{{#include ../../examples/reject/packages/gluing-wrong-projective/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/gluing-wrong-projective.stderr}}
```

## Limits

The compiler checks the declarations of this chapter by the exact
polynomial arithmetic of
[presented affine declarations](../affine-geometry.md#limits).
[Appendix D](../appendix/limits.md#gluing-declarations) lists the bounds
with their values.

Rules:

- A glued object names exactly two opens (`E_GLUE`), and a cover at most
  `algebraRelations` opens (`E_LIMIT`).
- The compiler expands and reduces each image, coefficient and witness
  within one run of the arithmetic, and it runs the checks of one
  declaration within one more run. Every polynomial of a run must have at
  most `algebraTerms` terms, and each run must stay within `algebraWork`
  units of work. A declaration beyond one of these bounds is an error
  (`E_LIMIT`), even when its text is short.
- The bounds of
  [polynomial expressions](smooth-declarations.md#polynomial-expressions)
  on literals, levels, exponents and degrees apply to each expression.

## Scope of gluing

The language glues exactly two charts: over the rational numbers in the
Zariski site, and over the real numbers in the smooth site. A chart
transition is a polynomial map in the coordinates of its open, which
include the inverse of the polynomial of the open. Outside the profile are
three or more charts with the conditions on their triple overlaps, the
gluing of sections of a sheaf, other sites and any conversion between the
two sites, and smooth covers without a unit-ideal identity, such as
$\{t^2 + 1 \neq 0\}$ of the real line. So are projective spaces other than
the projective line, and the projective line over a base with coordinates.
A glued object has no value, no points and no morphisms of its own.
[Verification boundaries](../verification.md#gluing-two-charts) states what
is Proved about the declarations, and the
[acceptance record](../stage7-acceptance.md#not-claimed) names the issues
that plan the extensions.
