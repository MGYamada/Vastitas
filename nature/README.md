# Vastitas `nature`

The `nature` package, `vastitas_nature`, holds the physical interpretations
of the mathematical objects of the standard library `std`: declared
identifications, conventions and hypotheses that give a `std` object its
meaning in the world
([ADR 0002](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0002-nature-dimension.md)).
It owns no mathematics. Every value and law that it uses is that of a `std`
object, and a check that it adds is a consistency check of an
interpretation, not a mathematical result.

## The boundary with `std`

- `nature` depends on `std`. Its manifest names the standard library at
  `../stdlib`, as applications do.
- `std` never depends on `nature`. No manifest under `stdlib/` depends on a
  package outside `stdlib/`, and no manifest under `nature/` depends on a
  package outside `stdlib/` and `nature/`. `scripts/check_boundaries.py`
  checks both rules.
- A `nature` declaration never changes the validity or the generated code of
  a `std` declaration or of a binding.

## `nature::dimension`

[`dimension/mod.vast`](dimension/mod.vast) is the module `nature::dimension`,
the physical dimensions of the coordinates of the smooth affine objects of
`std::geometry::smooth::affine`, for the finite profile of ADR 0002 §3.

| Public name | Contract |
| --- | --- |
| `Reading<X>` | The readings of a smooth affine object `X`: a quantity kind for each coordinate |
| `PhysicalMetric<X>` | The physical interpretations of the `std` metrics of `X` |
| `L`, `T`, `M` | The base dimensions length, time and mass |
| `Length`, `Time`, `Mass` | The quantity kinds of dimension `L`, `T` and `M` |
| `Speed` | The quantity kind of dimension `L T⁻¹` |
| `Wavelength` | A quantity kind of dimension `L`, distinct from `Length` |
| `Energy`, `Torque` | Two distinct quantity kinds of dimension `M L² T⁻²` |

These names are physical identifications. Equal dimensions do not identify
kinds: `Wavelength` is not `Length`, and `Torque` is not `Energy`. Every other
base dimension and quantity kind, and every reading, scale and physical
interpretation, belongs to the application:

```vast
use std::geometry::smooth::affine::SmoothR;
use std::geometry::metric::MetricForm;
use nature::dimension::Reading;
use nature::dimension::PhysicalMetric;
use nature::dimension::Length;
use nature::dimension::Time;

indexed affine C(SmoothR) = Affine(2)[x, t];
indexed metric G: MetricForm<C> = gram((frac(1, 9), 0), (0, frac(1, 4)));
indexed reading phys: Reading<C> = (x: Length, t: Time);
indexed scale l0 = 3 of Length;
indexed scale t0 = 2 of Time;
indexed physical PG: PhysicalMetric<C> = interpret(G, reading = phys, gram((l0^-2, 0), (0, t0^-2)));
```

The kernel rejects the interpretation of the Euclidean metric of `C` under
`phys` (`E_DIMENSION`): `dx²` has dimension `L²` and `dt²` has dimension `T²`.

## Use

Generate the standard-library package once from the repository root, then
depend on both packages by path:

```sh
python3 scripts/build_stdlib_package.py
```

```toml
[dependencies]
std = { path = "../Vastitas/stdlib" }
nature = { path = "../Vastitas/nature" }
```

The application and `nature` then reach one `std` package, because a package
is identified by the canonical location of its manifest. A copy of the
standard library at another location is another package, and a `nature`
package that depends on a copy does not accept the objects of the original.
`tests/nature_dimension.rs` runs such an application.

Import the items one by one, as in `use nature::dimension::Length;`, write
full paths, or bind the module under another name, as in
`use nature::dimension as dim;`. A plain `use nature::dimension;` is an error
(`E_RESERVED`): `dimension` may name a module, but it stays reserved for the
name that a `use` binds.
