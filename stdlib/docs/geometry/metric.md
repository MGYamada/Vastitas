# `std::geometry::metric`

- Module: `std::geometry::metric`
- Package: `vastitas_geometry`, the package of
  [`stdlib/src/geometry/Vastitas.toml`](../../src/geometry/Vastitas.toml), which
  `vastitas_std` re-exports as `std::geometry`
- Source: [`stdlib/src/geometry/metric/mod.vast`](../../src/geometry/metric/mod.vast)

The module declares the family of the constant metric forms on the smooth
affine objects of [`std::geometry::smooth::affine`](smooth/affine.md): the
symmetric bilinear forms on an object, given by a rational Gram matrix in its
coordinates. It is a declared family, so no value has its type. A metric
declaration names the type.

`MetricForm` is distinct from the diagonal Hermitian `Metric` of the
numerical profile and from `MetricSpace`; neither of those names exists in
this module.

## Exports

| Name | Kind | Contract |
| --- | --- | --- |
| `MetricForm<X>` | family | `metric_form`, over `CInfAffine` of `std::geometry::smooth::affine`, with `canonical(0)`: the metric forms of the smooth affine object `X` |

## Metrics belong to the application

A metric's evidence, `flat` and `sharp` each name one metric. Any package
that can name the metric may declare them. The standard library declares
none, because it cannot name an application's metric, and so no metric is a
default. A program that uses no metric needs no metric module.

[`examples/packages/stdlib-differential/main.vast`](../../../examples/packages/stdlib-differential/main.vast),
which `tests/examples.rs` builds and runs, declares a metric on its plane and
the declarations that name it:

- `indexed metric Skew: MetricForm<Plane> = gram((2, 1), (1, 1));` declares
  the metric.
- `indexed evidence SkewInvertible = nondegenerate(Skew);` certifies that its
  Gram matrix is invertible.
- `indexed primitive flat_skew = flat(Tangent, Cotangent, using = Skew);`
  maps a vector to a covector with the metric.
- `indexed primitive sharp_skew = sharp(Cotangent, Tangent, using = Skew, evidence = SkewInvertible);`
  maps a covector to a vector with the metric and its evidence.

The program computes a gradient as `sharp_skew` applied to a differential of
[`std::differential`](../differential.md), and prints `42`.

## Use

- [`examples/packages/stdlib-differential/`](../../../examples/packages/stdlib-differential)
  (`tests/examples.rs`, `tests/stdlib_differential.rs`): the metric `Skew`
  above.
- [`examples/packages/stdlib-frames/`](../../../examples/packages/stdlib-frames)
  (`tests/examples.rs`): the metric `G` of a chart, with a physical
  interpretation and a gradient.
- [`examples/packages/physical-dimensions/`](../../../examples/packages/physical-dimensions)
  (`tests/examples.rs`): two metrics of one chart, as in
  `indexed metric M: MetricForm<C> = gram((1, 0), (0, -9));`.
- [`examples/packages/frames-and-dimensions/`](../../../examples/packages/frames-and-dimensions)
  (`tests/frames_dimensions.rs`): metrics in a profile module.

The book chapter
[Smooth geometry and reverse pullbacks](https://github.com/MGYamada/Vastitas/blob/main/docs/guide/smooth-geometry.md#metrics-and-gradients)
introduces metrics and gradients.

## Rules and proofs

- [Metrics](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#metrics),
  [Metric evidence](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#metric-evidence)
  and [Flat and sharp](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#flat-and-sharp):
  the declarations that name a metric form.
- [The smooth profile](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#the-smooth-profile):
  the representation `metric_form`.
- The specifications [std::geometry::metric](https://github.com/MGYamada/Vastitas/blob/main/docs/spec/std-geometry-metric.md),
  the laws of `flat` and `sharp`, and
  [Metric evidence](https://github.com/MGYamada/Vastitas/blob/main/docs/spec/metric-evidence.md).
- [Smooth affine geometry and reverse pullbacks](https://github.com/MGYamada/Vastitas/blob/main/docs/verification.md#smooth-affine-geometry-and-reverse-pullbacks):
  what is proved and what is tested.
- [ADR 0001 §10, Laws](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#laws)
  and [the public-name audit](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#compatibility-and-public-name-audit).
