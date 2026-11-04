# Smooth geometry and reverse pullbacks

This chapter builds one program step by step. It declares two polynomial
maps between real affine spaces, composes them, and pulls a covector back
along the composite. It then computes a differential and a gradient. Every
number in the program is an exact rational, and the program prints `42` only
when every observation holds.

The program is
[`examples/packages/stdlib-differential/main.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/stdlib-differential/main.vast).
Run it from the repository root:

```sh
target/debug/vastitas build --manifest-path examples/packages/stdlib-differential/Vastitas.toml -o target/stdlib-differential
./target/stdlib-differential
```

## The smooth profile from the standard library

A *smooth affine object* is real affine space ℝⁿ with named coordinates. A
*smooth map* between two such objects gives each target coordinate as a
polynomial in the source coordinates. The standard library declares the
families that describe them, so a program imports them:

```vast
{{#include ../../examples/packages/stdlib-differential/main.vast:imports}}
```

`Smooth<X, Y>` is the type of smooth maps from `X` to `Y`. `Cotangent<X>` holds
covectors at points of `X`, and `Tangent<X>` holds vectors. `Pt` is the
0-dimensional object, and a point of `X` is a smooth map from `Pt` to `X`.
`Line` is the 1-dimensional object with the coordinate `t`.

## Objects and maps

The program declares the plane and two maps. `f` sends `t` to `(t, t²)`, and
`g` sends `(x, y)` to `x² + y`:

```vast
{{#include ../../examples/packages/stdlib-differential/main.vast:objects}}
```

A map's images are written in the source coordinates and listed by target
coordinate. `plane_at(1, 2)` builds the point (1, 2) of `Plane` from two
integers. Each `indexed affine` declaration introduces its own object: a
second `Affine(2)[x, y]` declaration would be a different object, and the
checker never confuses the two.

## Covectors and their components

A covector at a point is built from the point and one integer per coordinate.
Its components read back as reduced fractions, a `Pair<Int>` of numerator and
denominator:

```vast
{{#include ../../examples/packages/stdlib-differential/main.vast:fibers}}
```

`dline(line_at(18), 1)` is the covector dt at the point 18 of `Line`.

## Pulling a covector back

The composite `g ∘ f` sends `t` to `2t²`. At `t = 3`, `f(3) = (3, 9)` and
`g(f(3)) = 18`. The covector dt at 18 is the *seed*. Its pullback along the
composite at 3 is `4 · 3 · dt = 12 dt`.

`compose_smooth(g(), f())` builds the composite as a program. The program
keeps both maps and never expands the composite polynomial. `pullback(F, x, η)`
computes the pullback of the seed `η` along `F` at the point `x`.

The pullback along `g` at `f(3)`, then along `f` at 3, gives the same
covector as the pullback along the composite:

```vast
{{#include ../../examples/packages/stdlib-differential/main.vast:main}}
```

The observations in `main` read as follows:

- Code 1: the stepwise pullback is 12 dt.
- Code 2: the stepwise pullback equals the pullback along the composite.
- Code 3: the stepwise pullback lies over the point 3.
- Codes 4 and 5: the pullback that recomputes intermediate points agrees with
  it, and so does the reverse pass over a saved tape.
- Code 6: a seed over another point gives the failure value.
- Code 7: the differential of `g` at (1, 2) is (2, 1).
- Codes 8 to 11: the gradient under the metric `Skew` is (1, 0), and flat maps
  it back to the differential.

## A seed must lie over the image point

A seed is a covector at one point. The pullback along `F` at `x` needs a seed
at `F(x)`. The seed `dline(line_at(17), 1)` lies over 17, not over
`g(f(3)) = 18`, so the pullback gives the *failure value* instead of a
covector. The failure value lies over no point and equals no covector, and
every pullback of it is the failure value again. Code 6 checks this.

Points are run-time values, so the checker cannot reject a seed over the
wrong point. It does reject a seed over the wrong object. This function
passes a seed on `Line` to a pullback along `f`, whose target is `Plane`:

```vast
fn bad() -> Cotangent<Line> {
    pullback(f(), line_at(3), dline(line_at(9), 1))
}
```

The compiler reports, after the file position of the call:

```text
E_ENDPOINT: pullback requires a seed with object Plane (the map's target), but the supplied seed has object Line
```

## Saved and recomputed forward values

A pullback along a composite needs every intermediate point. The library's
`pullback` runs the forward pass once and saves the intermediate points. A
pullback with the `recomputed` mode evaluates them again during the reverse
pass. The library binds only the saved mode, and a program binds the other
one itself:

```vast
{{#include ../../examples/packages/stdlib-differential/main.vast:recomputed}}
```

`linearize(F, x)` returns the saved forward pass as a value, a *tape*, and
`backward(tape, η)` runs the reverse pass over it. All three agree, as codes 4
and 5 check. A tape remembers its point, so a seed over another point gives
the failure value here too.

## The differential

For a smooth function `φ` from `X` to `Line`, `differential(φ, p)` is the
pullback of dt at `φ(p)`. At (1, 2) the differential of `g` is
`2x dx + dy = 2 dx + dy`, which code 7 checks. The differential uses no
metric.

## Metrics and gradients

A gradient turns the differential into a vector, and that step needs a
metric. A program names its metric explicitly and gives evidence that the
metric is nondegenerate:

```vast
{{#include ../../examples/packages/stdlib-differential/main.vast:metric}}
```

- `indexed metric` declares a constant symmetric Gram matrix in the
  coordinates of `Plane`.
- `indexed evidence … = nondegenerate(Skew)` asks the compiler to compute the
  inverse of the Gram matrix and check it. A singular matrix is rejected.
- `flat` maps a vector to a covector with the Gram matrix. `sharp` maps a
  covector to a vector with the inverse, and it requires nondegenerate
  evidence for the same metric.
- `gradient` is an ordinary function: `sharp` applied to the differential.

Under `Skew`, the gradient of `g` at (1, 2) is (1, 0). With the Euclidean
metric it would be (2, 1): two metrics give two gradients of the same
differential. No metric is chosen by default.

The metric, its evidence, `flat`, `sharp` and `gradient` live in the program,
next to the metric that they name. A library function cannot take the
program's object or metric as a parameter, so the standard library does not
export a `gradient`.

## See also

- [Smooth affine declarations](../language/smooth-declarations.md): the
  declaration forms, their rules and their diagnostics.
- [The standard library](https://github.com/MGYamada/Vastitas/blob/main/stdlib/README.md): the modules
  `std::geometry::smooth::affine`, `std::geometry::metric` and
  `std::differential`.
- [Smooth affine geometry and reverse pullbacks](../verification.md#smooth-affine-geometry-and-reverse-pullbacks):
  what is proved and what is tested.
