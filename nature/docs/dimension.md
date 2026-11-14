# `nature::dimension`

- Module: `nature::dimension`
- Package: `vastitas_nature`, the package of
  [`nature/Vastitas.toml`](../Vastitas.toml), which depends on `std`
- Source: [`nature/src/dimension/mod.vast`](../src/dimension/mod.vast)

The module declares the physical dimensions of the coordinates of the smooth
affine objects of
[`std::geometry::smooth::affine`](../../stdlib/docs/geometry/smooth/affine.md),
in the finite profile of ADR 0002 §3. A reading of an object assigns a
quantity kind to each coordinate, and a physical interpretation of a `std`
metric writes its entries with scales; the kernel checks that the terms of an
interpreted metric have one dimension. Neither changes the object, its maps
or its metrics: a `std` metric is valid with and without them.

The base dimensions and quantity kinds of the module are physical
identifications, not mathematical facts. A quantity kind is nominal: equal
dimensions do not identify kinds, so `Wavelength` is not `Length` and
`Torque` is not `Energy`. Every other base dimension and quantity kind, and
every reading, scale and physical interpretation, belongs to the application.

## Exports

| Name | Kind | Contract |
| --- | --- | --- |
| `Reading<X>` | family | `reading`, over `CInfAffine` of `std::geometry::smooth::affine`, with `canonical(0)`: the readings of the smooth affine object `X`, a quantity kind for each coordinate |
| `PhysicalMetric<X>` | family | `physical_metric`, over `CInfAffine`, with `canonical(0)`: the physical interpretations of the `std` metrics of `X` |
| `L` | base dimension | Length |
| `T` | base dimension | Time |
| `M` | base dimension | Mass |
| `Length` | quantity | The quantity kind of the dimension `L` |
| `Time` | quantity | The quantity kind of the dimension `T` |
| `Mass` | quantity | The quantity kind of the dimension `M` |
| `Speed` | quantity | The quantity kind of the dimension `L * T^-1` |
| `Wavelength` | quantity | A quantity kind of the dimension `L`, other than `Length` |
| `Energy` | quantity | A quantity kind of the dimension `M * L^2 * T^-2` |
| `Torque` | quantity | A quantity kind of the dimension `M * L^2 * T^-2`, other than `Energy` |

## Use

[`examples/packages/physical-dimensions/main.vast`](../../examples/packages/physical-dimensions/main.vast),
which `tests/examples.rs` builds and runs, imports the declarations one by
one, as in `use nature::dimension::Length;`, and declares on a chart with a
length and a time coordinate:

- `indexed reading phys: Reading<C> = (x: Length, t: Time);`, a reading;
- `indexed scale l0 = 3 of Length;`, a scale;
- `indexed physical PG: PhysicalMetric<C> = interpret(G, reading = phys, gram((l0^-2, 0), (0, t0^-2)));`,
  a physical interpretation of the metric `G`;
- `indexed quantity Frequency = T^-1;`, a quantity kind of its own.

It computes gradients under its metrics and prints `42`; the
interpretations change no value.
[`examples/packages/stdlib-frames/`](../../examples/packages/stdlib-frames)
(`tests/examples.rs`) and
[`examples/packages/frames-and-dimensions/`](../../examples/packages/frames-and-dimensions)
(`tests/frames_dimensions.rs`) interpret a metric next to frames.
`tests/nature_dimension.rs` runs such an application. It checks that the
application and `nature` reach one `std` package, that the module exports
exactly its names, and that the generated code is byte-identical without the
declarations of `nature`.

## Rules and proofs

- [Physical dimensions](https://github.com/MGYamada/Vastitas/blob/main/docs/language/physical-dimensions.md):
  [families of readings and interpretations](https://github.com/MGYamada/Vastitas/blob/main/docs/language/physical-dimensions.md#families-of-readings-and-interpretations),
  [base dimensions and quantity kinds](https://github.com/MGYamada/Vastitas/blob/main/docs/language/physical-dimensions.md#base-dimensions-and-quantity-kinds),
  [readings](https://github.com/MGYamada/Vastitas/blob/main/docs/language/physical-dimensions.md#readings),
  [scales](https://github.com/MGYamada/Vastitas/blob/main/docs/language/physical-dimensions.md#scales),
  [physical interpretations](https://github.com/MGYamada/Vastitas/blob/main/docs/language/physical-dimensions.md#physical-interpretations)
  and [the scope](https://github.com/MGYamada/Vastitas/blob/main/docs/language/physical-dimensions.md#scope-of-physical-dimensions).
- [The library nature::dimension](https://github.com/MGYamada/Vastitas/blob/main/docs/language/physical-dimensions.md#the-library-naturedimension):
  how a program imports the module, and why a plain `use nature::dimension;`
  is an error.
- The specification [nature::dimension](https://github.com/MGYamada/Vastitas/blob/main/docs/spec/nature-dimension.md):
  consistency of an accepted interpretation, the rejected Euclidean metric of
  a length and a time, kinds that are not dimensions, and the independence of
  `std`, with their evidence.
- [Frames and physical dimensions](https://github.com/MGYamada/Vastitas/blob/main/docs/verification.md#frames-and-physical-dimensions):
  what is proved and what is tested.
- [ADR 0002](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0002-nature-dimension.md):
  [§1, Responsibility boundary](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0002-nature-dimension.md#1-responsibility-boundary),
  [§2, Admission test](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0002-nature-dimension.md#2-admission-test-for-a-nature-module)
  and [§3, `nature::dimension`](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0002-nature-dimension.md#3-naturedimension-finite-profile),
  with its [contract](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0002-nature-dimension.md#contract-and-jurisdiction),
  [laws](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0002-nature-dimension.md#laws)
  and [public-name audit](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0002-nature-dimension.md#compatibility-and-public-name-audit).
