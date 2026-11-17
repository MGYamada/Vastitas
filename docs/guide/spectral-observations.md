# Matrix fields and their spectra

This chapter builds one program that studies a matrix whose entries depend
on the point of the plane. At the point (x, y) the matrix has the rows
(x, y) and (y, −x), and its eigenvalues are ±√(x² + y²). They meet at the
origin. The program computes the trace of the square of the matrix as a map
of the point, with its gradient. It tells apart two matrices that have the
same characteristic polynomial, and it observes eigenvalues, their
derivatives and their eigenprojectors at rational points of a region where
the eigenvalues stay apart. No part of the program computes an eigenvalue:
the program supplies each eigenvalue that it observes, and the compiler
checks the facts that make the observations meaningful. Every number is a
rational number. The program writes `failures = 0` and exits with status 0
only when every observation holds.

The program is the package
[`examples/packages/geometry/spectral-observations/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/geometry/spectral-observations).
Run it from the repository root:

```sh
python3 scripts/build_stdlib_package.py
target/debug/vastitas build --manifest-path examples/packages/geometry/spectral-observations/Vastitas.toml -o target/spectral-observations
./target/spectral-observations
```

## Two modules

The package depends on the standard library and on `nature`, as the program
of the [previous chapter](frames-and-dimensions.md) does:

```toml
{{#include ../../examples/packages/geometry/spectral-observations/Vastitas.toml}}
```

It has two modules. `profile.vast` declares the objects, the matrices and
the charts, and `main.vast` observes them. `profile.vast` imports the four
families of `std::linalg::spectral`:

| Name | Meaning |
| --- | --- |
| `FreeModule<X>` | The type that the declaration of a module with a named basis on `X` names |
| `Endomorphism<X>` | The type that the declaration of a matrix field on `X` names |
| `Spectrum<X>` | The type that the declaration of the characteristic polynomial of a field on `X` names |
| `Branch<X>` | The type that the declaration of a region of `X` where the eigenvalues stay apart names |

`main.vast` imports the smooth profile of
[Smooth geometry and reverse pullbacks](smooth-geometry.md) and the
declarations of `profile.vast`:

```vast
{{#include ../../examples/packages/geometry/spectral-observations/src/main.vast:imports}}
```

## A matrix field on the plane

A matrix acts on vectors, so the program first declares the vectors: a
[*free module*](../appendix/glossary.md#free-module) with a basis of two
named vectors. It then declares the matrix as an
[*endomorphism field*](../appendix/glossary.md#endomorphism-field) of that
module:

```vast
{{#include ../../examples/packages/geometry/spectral-observations/src/profile.vast:field}}
```

`basis(e1, e2)` names the basis vectors, which name the rows and the columns
of the matrices that act on `V`. `rows((x, y), (y, -x))` gives the rows of
`H`, each entry a polynomial in the coordinates of the plane. At (3, 4), H
has the rows (3, 4) and (4, −3).

`symmetric` claims that H equals its transpose, and the compiler checks the
claim, entry by entry. A matrix whose entry in row `e1` and column `e2` is y
and whose entry in row `e2` and column `e1` is −y is not symmetric:

```vast
{{#include ../../examples/reject/packages/spectral-not-symmetric/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/spectral-not-symmetric.stderr}}
```

## The characteristic polynomial

The eigenvalues of H at a point are the roots of its characteristic
polynomial det(tI − H). A spectrum declaration asks for it:

```vast
{{#include ../../examples/packages/geometry/spectral-observations/src/profile.vast:spectrum}}
```

`eigen(H, t)` names the variable `t` of the polynomial, the
[*fiber coordinate*](../appendix/glossary.md#fiber-coordinate), which must
differ from the coordinates of the plane and from the basis names of `V`.
The compiler computes the characteristic polynomial t² − x² − y² and the
adjugate of tI − H, the matrix tI + H, and checks the two by a second
computation before it generates code. The
program never writes them, and the compiler never chooses an eigenvalue. The
declaration of `B`, the second one of the block, is the subject of
[a later section](#simple-eigenvalues-on-a-chart).

## Invariants are smooth maps

The trace of a power of H and a coefficient of the characteristic
polynomial are polynomials in the point, so they are
[smooth maps](smooth-geometry.md#objects-maps-and-points) to the line:

```vast
{{#include ../../examples/packages/geometry/spectral-observations/src/profile.vast:invariants}}
```

`tr1` is the trace of H, the map 0. `tr2` is the trace of H², the map
2x² + 2y², and `ref2` declares the same map by hand. `c0` is the constant
coefficient of the characteristic polynomial, −x² − y², which is −1/2 times
`tr2`. These maps are like every other smooth map: the
[differential](smooth-geometry.md#the-differential) and the
[gradient](smooth-geometry.md#metrics-and-gradients) of the previous
chapters apply to them, with the reverse pass that the compiler builds for
every map.

To take a gradient, the program needs a metric. It reads the plane as a
dimensionless chart and interprets the Euclidean metric on it, with the
`nature` declarations of the [previous chapter](frames-and-dimensions.md):

```vast
{{#include ../../examples/packages/geometry/spectral-observations/src/profile.vast:chart}}
```

The interpretation is a checked statement: dx² + dy² adds two dimensionless
squares. The gradient is `sharp` of the differential:

```vast
{{#include ../../examples/packages/geometry/spectral-observations/src/main.vast:gradient}}
```

The differential of 2x² + 2y² is (4x, 4y), and the Euclidean metric turns it
into the vector (4x, 4y): (4, 8) at (1, 2), (12, 16) at (3, 4) and (0, 0) at
the origin. The origin is no exception, although the two eigenvalues meet
there: the trace of H² is a polynomial, smooth everywhere.

## Same polynomial, different matrices

The characteristic polynomial does not determine a matrix. On the point,
where every field is a constant matrix, the program declares four fields:

```vast
{{#include ../../examples/packages/geometry/spectral-observations/src/profile.vast:point}}
```

`TwoI` is twice the identity, and `J` is the Jordan block with the rows
(2, 1) and (0, 2). Both have the characteristic polynomial (t − 2)², and
their invariants agree:

```vast
{{#include ../../examples/packages/geometry/spectral-observations/src/profile.vast:point-invariants}}
```

The two traces are 4, the traces of the squares are 8, and the
coefficients are 4 and −4, for both fields. The difference shows in what a
polynomial of t does to the vectors, the action of t as the matrix:

```vast
{{#include ../../examples/packages/geometry/spectral-observations/src/main.vast:action}}
```

`annihilates(…, element = f)` asks whether f, with the matrix for t, is the
zero matrix at a point. `t - 2` gives 2I − 2I = 0 for `TwoI`, and for `J` it
gives the matrix with the rows (0, 1) and (0, 0). `action_entry` reads one
entry of that matrix: row `f1`, column `f2` is 0 for `TwoI` and 1 for `J`.
The characteristic polynomial itself gives the zero matrix for every field,
so `(t - 2)^2` annihilates `J` and `t^2` annihilates `N`. On the plane,
`ann_chi` checks the same at two points. The fields `Zero` and `N` differ in
the same way as `TwoI` and `J`.

## Simple eigenvalues on a chart

At a point where the eigenvalues are apart, each eigenvalue moves smoothly
with the point, and its derivative exists. At the origin the two eigenvalues
of H meet, and neither has a derivative there. A
[*branch*](../appendix/glossary.md#branch) declares a region where every
eigenvalue is simple. The declaration `B` of the spectrum block above is
one. `simple(S, localize = x^2 + y^2, …)` names the region where x² + y² is not
zero, the plane without the origin. The
[*gap witness*](../appendix/glossary.md#gap-witness) `frac(1, 2) * t` proves
the gap: the derivative of the characteristic polynomial in t is 2t, and
(t/2)·2t = t² equals x² + y² wherever t is an eigenvalue. So the derivative
cannot vanish at an eigenvalue in the region. The compiler checks this
identity of polynomials exactly, with no tolerance. A region that contains
the origin has no gap witness:

```vast
{{#include ../../examples/reject/packages/spectral-gap-at-origin/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/spectral-gap-at-origin.stderr}}
```

## Eigenvalues as inputs

The branch observations take a point and a number, and they observe the
eigenvalue at that point that the number names:

```vast
{{#include ../../examples/packages/geometry/spectral-observations/src/main.vast:branch}}
```

At p = (3, 4) the eigenvalues are 5 and −5. `on(p, line_at(5))` is `true`:
the point is in the region and 5 is an eigenvalue there. `on(p, line_at(4))`
is `false`, and so is `on(z, line_at(0))` at the origin, which is outside the
region although 0 is an eigenvalue there.

`dlambda(p, line_at(5))` is the differential of the eigenvalue that is 5 at
p. The eigenvalue is √(x² + y²) near p, so its differential is
(x, y)/√(x² + y²), the covector (3/5, 4/5). For −5 it is (−3/5, −4/5). The
executable computes it from the characteristic polynomial, by the rule for an
implicitly defined function, and the result has length 1 under the Euclidean
metric. Outside the region, or for a number that is no eigenvalue,
`dlambda` gives the
[*failure value*](../appendix/glossary.md#failure-value).

The [*eigenprojector*](../appendix/glossary.md#eigenprojector) of an
eigenvalue projects onto its eigenvectors. For 5 at p it is
(1/5)[[4, 2], [2, 1]], whose columns are multiples of the eigenvector (2, 1).
`p11` to `p22` read its four entries; `p12(p, line_at(5))` reads `(2, 5)`.
For −5 it is (1/5)[[1, −2], [−2, 4]]. The two projectors sum to the identity,
and both are symmetric, as H is.

## The observations

`main` builds the points and the two differentials, adds the verdict of each
observation to `failures` and shows it. It returns 1 when `failures` is
nonzero:

```vast
{{#include ../../examples/packages/geometry/spectral-observations/src/main.vast:main}}
```

Each observation adds its own power of two when it fails, so the shown
number names every failed observation. `verdict`, `reads` and `minus_half`
are small functions of `main.vast`: `reads` compares a pair with a reduced
fraction, and `minus_half` checks that one rational is −1/2 times another.

> **What is checked.** The checker computes and checks the characteristic
> polynomial of every field, checks every `symmetric` claim and every gap
> witness, and rejects an observation of one object at a point of another
> before the compiler generates code. The
> [proofs](../verification.md#spectral-observations) cover the identities
> of the characteristic polynomial, what an invariant is, the differential
> of the trace of H², the definedness of the branch observations, the laws
> of the eigenprojector, the two forms of the differential of an
> eigenvalue, the two matrices with one characteristic polynomial, and the
> fact that the declarations of modules, matrices, spectra and regions
> change no other declaration. They also compare the characteristic
> polynomial, the trace powers and their derivatives with those of real
> analysis. The differential of an eigenvalue is the derivative of every
> differentiable function through the point that keeps the eigenvalue a
> root; that such a function exists is not proved. Tests cover native
> execution, the gradient under the metric of the program, the symmetry of
> the eigenprojectors, the diagnostics and agreement with an independent
> reference program. A number that is no eigenvalue gives `false`, the
> failure value or `(0, 0)` at run time, not an error of the compiler.

## See also

- [Spectral observations](../language/spectral-observations.md): the
  spectral families, the declarations, the invariants, the observations and
  their rules.
- [Free modules](../language/spectral-observations.md#free-modules),
  [Endomorphism fields](../language/spectral-observations.md#endomorphism-fields)
  and [Spectral pairs](../language/spectral-observations.md#spectral-pairs):
  `basis(…)`, `rows(…) of V`, `symmetric` and `eigen(H, t)`.
- [Spectral invariants](../language/spectral-observations.md#spectral-invariants)
  and [Module observations](../language/spectral-observations.md#module-observations):
  `trace_power`, `char_coefficient`, `annihilates` and `action_entry`.
- [Branches](../language/spectral-observations.md#branches) and
  [Branch observations](../language/spectral-observations.md#branch-observations):
  `simple(…)`, the gap witness and the observations of an eigenvalue.
- [Smooth affine declarations](../language/smooth-declarations.md): maps,
  differentials, metrics and `sharp`.
