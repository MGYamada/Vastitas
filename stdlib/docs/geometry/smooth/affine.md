# `std::geometry::smooth::affine`

- Module: `std::geometry::smooth::affine`
- Package: `vastitas_geometry`, the package of
  [`stdlib/src/geometry/Vastitas.toml`](../../../src/geometry/Vastitas.toml), which
  `vastitas_std` re-exports as `std::geometry`
- Source: [`stdlib/src/geometry/smooth/affine/mod.vast`](../../../src/geometry/smooth/affine/mod.vast)

The module declares one smooth affine profile, on the marker `CInfReal` of
[`std::geometry::smooth`](../smooth.md). A **smooth affine object** is a
declared real affine space `Affine(n)[c₁, …, cₙ]` with named coordinates, and
its maps are exact rational polynomial maps. The module declares the
families of smooth maps, of their tapes, and of the vectors and covectors at
the rational points of an object, the two objects `Pt` and `Line`, and the
metric-free operations on maps and fibers. A program declares its own
objects, maps, points and fiber primitives against these families.
[`std::geometry::metric`](../metric.md) declares the metric forms of these
objects, [`std::geometry::frame`](../frame.md) their frames, and
[`std::differential`](../../differential.md) their pullbacks.

The objects form the sealed classification `CInfAffine`, which has no
parent. They index neither the families of the descriptor objects of
[`std::geometry`](../../geometry.md) nor the presented family `Over`. Each
declaration of an object is one object: a program's own `Affine(1)[t]` is
not `Line`, and `std::differential::differential` does not take a function
into it.

## Exports

| Name | Kind | Contract |
| --- | --- | --- |
| `SmoothR` | implementation | `SmoothR(CInfReal, smooth_affine)`, with no capabilities: the smooth affine objects on the marker `CInfReal` |
| `CInfAffine` | classification | The domain `SmoothR`, with no parents: the sealed classification of smooth affine objects |
| `Smooth<X, Y>` | family | `smooth`, with `canonical(0), canonical(1)`: the smooth maps from `X` to `Y` |
| `Tape<X, Y>` | family | `tape`, with `canonical(0), canonical(1)`: the saved forward values of a smooth map from `X` to `Y` at a point |
| `Tangent<X>` | family | `tangent`, with `canonical(0)`: the vectors at the rational points of `X`, and the failure value |
| `Cotangent<X>` | family | `cotangent`, with `canonical(0)`: the covectors at the rational points of `X`, and the failure value |
| `Pt` | affine | `Affine(0)[]`: the point, the source of every rational point |
| `Line` | affine | `Affine(1)[t]`: the line, the target of every differential |
| `compose_smooth(after, before)` | primitive | `smooth_compose(Smooth)`: the composite program `after` after `before`; it does not expand the maps |
| `composite(map)` | primitive | `smooth_composite(Smooth)`: the same map, with its composite program expanded into one map |
| `same_smooth(a, b)` | primitive | `smooth_equal(Smooth)`: whether the two maps have equal coordinate polynomials |
| `line_at(n)` | primitive | `smooth_int_point(Smooth, Line, Pt)`: the rational point `n` of `Line`, from an `Int` |
| `lies_over(covector, point)` | primitive | `fiber_at(Cotangent, Smooth)`: whether the covector lies over the point; the failure value lies over no point |
| `tangent_over(vector, point)` | primitive | `fiber_at(Tangent, Smooth)`: whether the vector lies over the point; the failure value lies over no point |
| `same_covector(a, b)` | primitive | `fiber_equal(Cotangent)`: whether the points and the components are equal; the failure value equals nothing |
| `same_vector(a, b)` | primitive | `fiber_equal(Tangent)`: whether the points and the components are equal; the failure value equals nothing |
| `pairing(covector, vector)` | primitive | `fiber_pairing(Cotangent, Tangent)`: the metric-free pairing, as a reduced fraction; `(0, 0)` for the failure value and for fibers at two points |

The module declares no `compose`, `id`, `same` or `apply`. The bare name
`compose` of the core syntax, `std::geometry::compose` and
`std::geometry::smooth::compose` name one declaration, which takes the
morphisms of descriptor objects; `compose_smooth` and `same_smooth` take
smooth maps only. The identity smooth map of an object is a morphism
declaration with the definition `identity`, not a function, as
[Smooth maps](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#smooth-maps)
says.

## Use

Packages that depend on `std`, built and run by the tests that the list
names:

- [`examples/packages/stdlib-differential/`](../../../../examples/packages/stdlib-differential)
  (`tests/examples.rs`, `tests/stdlib_differential.rs`) declares
  `indexed affine Plane(SmoothR) = Affine(2)[x, y];` and the maps
  `indexed morphism g: Smooth<Plane, Line> = pullback(t -> x^2 + y);` and
  `f`, pulls covectors back, compares them and pairs them, and prints `42`.
- [`examples/packages/stdlib-frames/`](../../../../examples/packages/stdlib-frames)
  (`tests/examples.rs`) and
  [`examples/packages/physical-dimensions/`](../../../../examples/packages/physical-dimensions)
  (`tests/examples.rs`) declare their objects, points and fibers on the
  profile and print `42`.
- [`examples/packages/frames-and-dimensions/`](../../../../examples/packages/frames-and-dimensions)
  (`tests/frames_dimensions.rs`) uses `compose_smooth`, `line_at`,
  `lies_over`, `tangent_over`, `same_covector`, `same_vector` and `pairing`,
  and prints `42`.

`tests/stdlib_differential.rs` also runs `composite`, `same_smooth` and
`Tape` from an application, the name audit of the module, and a program
without the metric module. The book chapter
[Smooth geometry and reverse pullbacks](https://github.com/MGYamada/Vastitas/blob/main/docs/guide/smooth-geometry.md#the-smooth-profile-of-the-standard-library)
introduces the profile.

## Rules and proofs

- [Smooth affine declarations](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md):
  [the smooth profile](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#the-smooth-profile),
  [smooth affine objects](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#smooth-affine-objects),
  [polynomial expressions](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#polynomial-expressions),
  [smooth maps](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#smooth-maps),
  [smooth map primitives](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#smooth-map-primitives),
  [fiber primitives](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#fiber-primitives),
  [operand checks](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#operand-checks)
  and [the scope](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md#scope-of-smooth-affine-geometry).
- [Calls of primitives](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#calls-of-primitives):
  the errors of a call with an operand of another family.
- [Smooth affine geometry and reverse pullbacks](https://github.com/MGYamada/Vastitas/blob/main/docs/verification.md#smooth-affine-geometry-and-reverse-pullbacks):
  what is proved and what is tested.
- [ADR 0001 §10](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#10-smooth-affine-differentials-and-metrics-amendment-2026-11-04):
  [terms](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#terms),
  [contract and jurisdiction](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#contract-and-jurisdiction)
  and [the public-name audit](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#compatibility-and-public-name-audit).
