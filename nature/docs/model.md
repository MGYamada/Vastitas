# `nature::model`

- Module: `nature::model`
- Package: `vastitas_model`, the package of
  [`nature/src/model/Vastitas.toml`](../src/model/Vastitas.toml), which
  depends on `std`. The root of `vastitas_nature` re-exports it as
  `nature::model`.
- Source: [`nature/src/model/mod.vast`](../src/model/mod.vast)

The module declares the physical models of the `std` objects of the finite
profile of historical Stage 6, which ADR 0002 admits as `nature::model`. A
model on a smooth affine object `X` of
[`std::geometry::smooth::affine`](../../stdlib/docs/geometry/smooth/affine.md)
names a symmetric endomorphism field of
[`std::linalg::spectral`](../../stdlib/docs/linalg/spectral.md) on `X`, a
reading of `X` of [`nature::dimension`](dimension.md), a convention, a
prepared and an observed basis vector of the module of the field, the
transition average that it predicts, and its regime. The kernel checks
that these references fit together (`E_MODEL`). The regime, such as the rotating-wave
approximation, is a recorded assumption, which no check proves. A model and a
convention compute nothing, and they change no value, no validity and no
generated code of a `std` declaration.

The one convention of the profile is `hbar_one`, which writes energies as
angular frequencies (`ħ = 1`). An application declares it, as in
`indexed convention c = hbar_one;`.

The module declares the family only; the application declares its
conventions and models. The source syntax of these declarations and the
tested example come with the later steps of the Stage 6 tracker
[#841](https://github.com/MGYamada/Vastitas/issues/841).

## Exports

| Name | Kind | Contract |
| --- | --- | --- |
| `Model<X>` | family | `model`, over `CInfAffine` of `std::geometry::smooth::affine`, with `canonical(0)`: the models on the smooth affine object `X`, each naming a field, a reading, a convention, a prepared and an observed basis vector, a predicted transition average and its regime |

## Rules and proofs

- [ADR 0002](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0002-nature-dimension.md):
  the responsibility boundary of `nature`, its admission test, and the
  amendment that admits `nature::model`.
- The Stage 6 tracker [#841](https://github.com/MGYamada/Vastitas/issues/841):
  the acceptance conditions and the delivery of the module.
