# `std::differential`

- Module: `std::differential`, the root module of its package
- Package: `vastitas_differential`, the package of
  [`stdlib/src/differential/Vastitas.toml`](../src/differential/Vastitas.toml),
  which `vastitas_std` re-exports as `std::differential`; it depends on the
  geometry package under the alias `geometry`
- Source: [`stdlib/src/differential/mod.vast`](../src/differential/mod.vast)

The module differentiates the smooth maps of
[`std::geometry::smooth::affine`](geometry/smooth/affine.md) at rational
points, with exact rational arithmetic. Its operations are metric free: each
binds a runtime routine of the executable kernel, and none names a metric, so
a program that uses only them needs no metric module. The reverse cotangent
pullback is the standard route of automatic differentiation in `std`.

The package depends on the geometry package, and the geometry package does
not depend on it. A dependency in that direction would be a cycle of the
package graph.

## Exports

| Name | Kind | Contract |
| --- | --- | --- |
| `pullback(f, x, eta)` | primitive | `cotangent_pullback(Smooth, Cotangent, saved)`: the covector `eta ∘ Df(x)` at `x`, with saved forward values; the failure value when the seed `eta` lies over a point other than `f(x)` |
| `differential(phi, x)` | primitive | `differential(Smooth, Cotangent, Line)`: the pullback of `dt` at `phi(x)`, for a map `phi` into `Line` |
| `linearize(f, x)` | primitive | `linearize(Smooth, Tape)`: the tape of the forward values of `f` at `x`; the only way to build a tape |
| `backward(tape, eta)` | primitive | `cotangent_backward(Tape, Cotangent)`: the pullback of `eta` through the tape; the failure value unless `eta` lies over the image that the tape holds |

## What the application declares

The package exports no recomputing pullback. An application may bind one
over the families of the library, as
[`examples/packages/stdlib-differential/main.vast`](../../examples/packages/stdlib-differential/main.vast)
does:
`indexed primitive pullback_recomputed = cotangent_pullback(Smooth, Cotangent, recomputed);`.

The package exports no `gradient`. A gradient is `sharp` applied to a
differential, and `sharp` names one metric and its evidence, which the
library cannot name. A library function also cannot take the object or the
metric as an argument. So the application declares `sharp` next to its
metric, as [`std::geometry::metric`](geometry/metric.md#metrics-belong-to-the-application)
shows, and writes the gradient as an ordinary function. In the same example,
`fn gradient(h: Smooth<Plane, Line>, p: Smooth<Pt, Plane>) -> Tangent<Plane> {`
has the body `sharp_skew(differential(h, p))`.

## Use

- [`examples/packages/stdlib-differential/`](../../examples/packages/stdlib-differential)
  (`tests/examples.rs`, `tests/stdlib_differential.rs`, `tests/emit_golden.rs`)
  imports the four operations, as in `use std::differential::pullback;`. It
  pulls the seed `dt` at 18 back along g after f to 12 `dt` at 3, compares
  the saved, recomputed and tape pullbacks, gives the failure value for a
  seed at 17, computes the differential `(2, 1)` and a gradient, and prints
  `42`.
- [`examples/packages/stdlib-frames/`](../../examples/packages/stdlib-frames)
  and [`examples/packages/physical-dimensions/`](../../examples/packages/physical-dimensions)
  (`tests/examples.rs`) compute gradients under their metrics from
  `differential`.
- [`examples/packages/frames-and-dimensions/`](../../examples/packages/frames-and-dimensions)
  (`tests/frames_dimensions.rs`) uses `pullback` and `differential` with
  frames.

The book chapter
[Smooth geometry and reverse pullbacks](https://github.com/MGYamada/Vastitas/blob/main/docs/guide/smooth-geometry.md#pulling-a-covector-back)
introduces pullbacks, tapes and differentials.

## Rules and proofs

- [Reverse-pass primitives](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#reverse-pass-primitives)
  and [Operand checks](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#operand-checks):
  the bindings of this module, the pullback modes, tapes and the failure
  value.
- [Flat and sharp](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#flat-and-sharp):
  the declarations of a gradient.
- [The smooth profile](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#the-smooth-profile)
  and [Function types](https://github.com/MGYamada/Vastitas/blob/main/docs/language/types.md#function-types):
  why a library function cannot take the object or the metric.
- [The package graph](https://github.com/MGYamada/Vastitas/blob/main/docs/packages.md#the-package-graph):
  the rule against cycles of dependencies.
- The specifications [std::differential](https://github.com/MGYamada/Vastitas/blob/main/docs/spec/std-differential.md),
  the laws of the pullback, and
  [Compiled reverse Core](https://github.com/MGYamada/Vastitas/blob/main/docs/spec/reverse-core.md),
  what the generated reverse passes compute.
- [Smooth affine geometry and reverse pullbacks](https://github.com/MGYamada/Vastitas/blob/main/docs/verification.md#smooth-affine-geometry-and-reverse-pullbacks)
  and [Compiled reverse Core](https://github.com/MGYamada/Vastitas/blob/main/docs/verification.md#compiled-reverse-core):
  what is proved and what is tested.
- [ADR 0001 §6, Differentiation and the extension boundary](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#6-differentiation-and-the-extension-boundary),
  [§10, Laws](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#laws),
  [Deviation: no `gradient` export](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#deviation-no-gradient-export)
  and [Amendment: compiled reverse Core](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#amendment-compiled-reverse-core-2026-11-06).
