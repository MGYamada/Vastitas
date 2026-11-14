# `std::geometry::scheme::affine`

- Module: `std::geometry::scheme::affine`
- Package: `vastitas_geometry`, the package of
  [`stdlib/src/geometry/Vastitas.toml`](../../../src/geometry/Vastitas.toml), which
  `vastitas_std` re-exports as `std::geometry`
- Source: [`stdlib/src/geometry/scheme/affine/mod.vast`](../../../src/geometry/scheme/affine/mod.vast)

The module declares one presented profile of affine geometry over the
rational numbers: exact presented ℚ-algebras and the morphisms between their
spectra over a base, which the kernel checks. It declares the base `SpecQQ`
and two objects over it, the affine line and the dual numbers. Each
declaration is one canonical object, so a program's own `spec[t] over
SpecQQ` is not the library's `Line`, and the kernel compares two separately
declared presentations only through a checked isomorphism. A program
declares its own objects, morphisms, isomorphisms, fiber products, principal
opens and further primitives against this profile.

The implementation `AffineQQ` names the marker `QQ` of
[`std::geometry::scheme`](../scheme.md), but its objects are presented affine
objects, not descriptor objects: they index the family `Over` and not the
families `Point` and `Morphism` of [`std::geometry`](../../geometry.md).

## Exports

| Name | Kind | Contract |
| --- | --- | --- |
| `AffineQQ` | implementation | `AffineQQ(QQ, presented_affine(rational))`, with no capabilities: the presented affine objects over the rational numbers |
| `AffineScheme` | classification | The domain `AffineQQ`, with no parents |
| `Over<X, Y, S>` | family | `relative`, over `AffineScheme` three times, with `structural(0, 2), structural(1, 2)`: the morphisms from `X` to `Y` over the base `S` |
| `SpecQQ` | affine | `spec[]`: Spec ℚ, the base of every object of the module |
| `Line` | affine | `spec[t] over SpecQQ`: the affine line Spec ℚ[t] |
| `DualNumbers` | affine | `spec[e] relations(e^2) over SpecQQ`: the dual numbers Spec ℚ[e]/(e²) |
| `compose(after, before)` | primitive | `relative_compose(Over)`: the morphism `after` after the morphism `before`, in the written order |
| `same(a, b)` | primitive | `relative_equal(Over)`: whether two morphisms of one type are equal |

This `compose` is not the `compose` of `std::geometry`, and `Line` is not
the `Line` of `std::geometry::smooth::affine`: each module declares its own.

## Use

[`examples/packages/stdlib-affine/`](../../../../examples/packages/stdlib-affine),
which `tests/examples.rs` builds and runs, imports every export apart from
`AffineScheme`, as in
`use std::geometry::scheme::affine::Over;`. It declares morphisms such as
`indexed morphism p: Over<DualNumbers, Line, SpecQQ> = pullback(t -> e);`,
the curve
`indexed affine Curve(AffineQQ) = spec[t, x] relations(x^2 - t) over Line by(t -> t);`,
a fiber product, principal opens and an isomorphism, and prints `42` when
its eleven observations hold.

The book chapter
[Presented affine geometry](https://github.com/MGYamada/Vastitas/blob/main/docs/guide/affine-geometry.md)
walks through the example.

## Rules and proofs

- [Presented affine declarations](https://github.com/MGYamada/Vastitas/blob/main/docs/affine-geometry.md):
  [the presented profile](https://github.com/MGYamada/Vastitas/blob/main/docs/affine-geometry.md#the-presented-profile),
  [presented affine objects](https://github.com/MGYamada/Vastitas/blob/main/docs/affine-geometry.md#presented-affine-objects),
  [morphisms over a base](https://github.com/MGYamada/Vastitas/blob/main/docs/affine-geometry.md#morphisms-over-a-base),
  [morphism primitives](https://github.com/MGYamada/Vastitas/blob/main/docs/affine-geometry.md#morphism-primitives),
  [operand checks](https://github.com/MGYamada/Vastitas/blob/main/docs/affine-geometry.md#operand-checks),
  [limits](https://github.com/MGYamada/Vastitas/blob/main/docs/affine-geometry.md#limits)
  and [the scope](https://github.com/MGYamada/Vastitas/blob/main/docs/affine-geometry.md#scope-of-presented-affine-geometry).
- [Implementations](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#implementations),
  [Classifications](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#classifications)
  and [Families](https://github.com/MGYamada/Vastitas/blob/main/docs/indexed-source.md#families):
  the general rules of the declarations.
- [Exact affine algebra checker](https://github.com/MGYamada/Vastitas/blob/main/docs/verification.md#exact-affine-algebra-checker):
  what is proved and what is tested.
- [ADR 0001 §4, Mathematical family boundaries](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#4-mathematical-family-boundaries)
  and [§5, Exact coefficients](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#5-exact-coefficients-smooth-meaning-and-numerical-realizations).
