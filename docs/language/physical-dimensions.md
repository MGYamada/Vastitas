# Physical dimensions

This chapter defines the declarations that give the coordinates of a smooth
affine object and its metrics a physical meaning: base dimensions, quantity
kinds, readings, scales and physical interpretations. A
**physical dimension** is a product of integer powers of base dimensions,
such as L · T⁻¹, or the dimensionless dimension 1. It is unrelated to the
dimension of an object, the number of its coordinates. The kernel checks the
declarations of this chapter, and no declaration of another chapter and no
primitive reads them. So they change neither the validity nor the generated
code of the rest of a program. [Smooth affine declarations](smooth-declarations.md)
defines smooth affine objects and their metrics, and
[Indexed declarations](../indexed-source.md) gives the general rules of
`indexed` declarations. [Notation](notation.md) explains the Syntax blocks,
and the [glossary](../appendix/glossary.md) defines the terms.

The examples quote the tested package
[`examples/packages/physical-dimensions/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/physical-dimensions),
whose executable prints `42`. It depends on the standard library and on the
library [`nature::dimension`](#the-library-naturedimension). Each rejected
program is a package on the same libraries. It appears with the diagnostic
that the compiler prints for it.

The declarations of this chapter are the forms of `DimensionDeclaration`:

> **Syntax**
>
> ```text
> DimensionDeclaration -> DimensionFamily | BaseDimensionDeclaration
>     | QuantityDeclaration | ReadingDeclaration | ScaleDeclaration
>     | PhysicalDeclaration
> ```

Each declaration of this chapter is an [item](items.md):
`DimensionDeclaration` is one form of
[`IndexedDeclaration`](../indexed-source.md). `pub` before a declaration
makes it visible outside its module.

## Families of readings and interpretations

> **Syntax**
>
> ```text
> DimensionFamily -> `indexed` `family` IDENTIFIER `(` Parameters? `)`
>     `=` DimensionRepresentation `constraints` `(` Constraints? `)` `;`
> DimensionRepresentation -> `reading` | `physical_metric`
> ```

[Families](../indexed-source.md#families) gives the productions
`Parameters` and `Constraints`. A family with the `reading` representation
indexes the [readings](#readings) of a smooth affine object, and one with the
`physical_metric` representation its [physical interpretations](#physical-interpretations).
Neither has values: a declaration names the type, as a metric names its
metric form.

Rules:

- A family with the `reading` or `physical_metric` representation must have
  exactly one parameter, of the form `object(K)`, and exactly the constraint
  `canonical(0)`. Otherwise it is an error (`E_TYPE`).
- Every implementation in the domain of `K` must have the `smooth_affine`
  representation. Otherwise it is an error (`E_TYPE`).

`nature::dimension` declares the families `Reading` and `PhysicalMetric` in
this form, over the classification `CInfAffine` of the standard library.

## Base dimensions and quantity kinds

> **Syntax**
>
> ```text
> BaseDimensionDeclaration -> `indexed` `base_dimension` IDENTIFIER `;`
> QuantityDeclaration -> `indexed` `quantity` IDENTIFIER `=` Dimension `;`
> Dimension -> INTEGER_LITERAL | DimensionFactor ( `*` DimensionFactor )*
> DimensionFactor -> Path ( `^` `-`? INTEGER_LITERAL )?
> ```

`indexed base_dimension L;` declares the **base dimension** `L`. The base
dimensions of a program generate its physical dimensions: a `Dimension` is
the literal `1`, the dimensionless dimension, or a product of powers of base
dimensions. `L * T^-1` is L · T⁻¹, and a factor without `^` has the
exponent 1. Two dimensions are equal when every base dimension has one
exponent in both, whatever the order of their factors.

`indexed quantity Speed = L * T^-1;` declares the **quantity kind** `Speed`
of the dimension L · T⁻¹. A quantity kind is nominal: two quantity
declarations with one dimension are two kinds. `Length` and `Wavelength`
both have the dimension L, and `Energy` and `Torque` both have the dimension
M · L² · T⁻², and no rule identifies them. Only
[`normalized`](#physical-interpretations) compares kinds. The other rules
compare dimensions.

Rules:

- A program must declare at most 16 base dimensions, in all its packages.
  Otherwise the declaration of the 17th is an error (`E_LIMIT`). The limit is
  `dimensionBases` of [Appendix D](../appendix/limits.md#physical-dimensions).
- The only integer literal of a dimension is `1`. Another literal is an error
  (`E_PARSE`).
- Each factor must name a base dimension. Otherwise it is an error
  (`E_DIMENSION`).
- A dimension must name each base dimension once. A second factor of one
  base dimension is an error (`E_DIMENSION`), even when one of the exponents
  is 0.
- An exponent is an integer with at most 64 digits, and its absolute value
  must be at most 64 (`dimensionExponent`). Otherwise it is an error
  (`E_LIMIT`). A factor with the exponent 0 drops out of the dimension.
- A rational exponent, such as `L^frac(1, 2)`, is an error (`E_PARSE`), and
  `/` is an error (`E_UNSUPPORTED`).
- A base dimension or a quantity used as a value, or called, is an error
  (`E_TYPE`).

Example, from
[`main.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/physical-dimensions/main.vast):

```vast
{{#include ../../examples/packages/physical-dimensions/main.vast:dimensions}}
```

`Theta` is a base dimension of the program, next to the base dimensions `L`,
`T` and `M` of `nature::dimension`. `Ratio` is dimensionless.

## Readings

> **Syntax**
>
> ```text
> ReadingDeclaration -> `indexed` `reading` IDENTIFIER `:` Path
>     `<` Path ( `,` Path )* `>` `=` `(` ReadingEntries? `)` `;`
> ReadingEntries -> ReadingEntry ( `,` ReadingEntry )* `,`?
> ReadingEntry -> CoordinateName `:` Path
> ```

`indexed reading phys: R<X> = (x: Length, t: Time);` declares the
**reading** `phys` of the smooth affine object `X` at the reading family
`R`: a quantity kind for each coordinate of `X`. The reading says that the
coordinate `x` measures a length and the coordinate `t` a time. An object may
have several readings, and a reading changes nothing about the object.

Rules:

- The family must have the `reading` representation. Otherwise it is an
  error (`E_DIMENSION`).
- A reading must name exactly one object. Otherwise it is an error
  (`E_DIMENSION`).
- The object must be a smooth affine object, and the family must accept it.
  Otherwise it is an error (`E_DIMENSION`).
- A reading must name each coordinate of the object exactly once. A missing,
  repeated or unknown coordinate is an error (`E_DIMENSION`). The
  coordinates may stand in any order.
- Each path after `:` must name a quantity kind. Otherwise it is an error
  (`E_DIMENSION`).
- A reading used as a value, or called, is an error (`E_TYPE`).

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/physical-dimensions/main.vast:chart}}
```

The following reading leaves out the coordinate `t`:

```vast
{{#include ../../examples/reject/packages/dimension-reading-coordinate/main.vast:declaration}}
```

```text
{{#include ../../examples/reject/packages/dimension-reading-coordinate.stderr}}
```

## Scales

> **Syntax**
>
> ```text
> ScaleDeclaration -> `indexed` `scale` IDENTIFIER `=` Polynomial `of` Path `;`
> ```

[Polynomial expressions](smooth-declarations.md#polynomial-expressions)
gives the production `Polynomial`.

`indexed scale l0 = 3 of Length;` declares the **scale** `l0`: the positive
rational magnitude 3 of the quantity kind `Length`. The dimension of a scale
is the dimension of its quantity kind. A scale is the size of a reference
quantity, such as the length of a ruler, and it names no unit system.

Rules:

- The magnitude must be a constant polynomial expression. The rules of
  [polynomial expressions](smooth-declarations.md#polynomial-expressions)
  apply to it, and a coordinate name in it is an error (`E_DIMENSION`).
- The magnitude must be positive. Otherwise it is an error (`E_DIMENSION`).
- The numerator and the denominator of the magnitude must have at most
  `metricEntryBits` bits
  ([limits](../appendix/limits.md#physical-dimensions)). Otherwise it is an
  error (`E_LIMIT`).
- The path after `of` must name a quantity kind. Otherwise it is an error
  (`E_DIMENSION`).
- A scale used as a value, or called, is an error (`E_TYPE`).

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/physical-dimensions/main.vast:scales}}
```

The following scale has a negative magnitude:

```vast
{{#include ../../examples/reject/packages/dimension-scale-magnitude/main.vast:declaration}}
```

```text
{{#include ../../examples/reject/packages/dimension-scale-magnitude.stderr}}
```

## Physical interpretations

> **Syntax**
>
> ```text
> PhysicalDeclaration -> `indexed` `physical` IDENTIFIER `:` Path
>     `<` Path ( `,` Path )* `>` `=` `interpret` `(` Path `,` `reading` `=` Path
>     `,` PhysicalEntries ( `,` `value` `=` Dimension )? `)` `;`
> PhysicalEntries -> `euclidean`
>     | `gram` `(` ( ScaleRow ( `,` ScaleRow )* `,`? )? `)`
>     | `normalized` `(` ( CoordinateScale ( `,` CoordinateScale )* `,`? )? `)`
> ScaleRow -> `(` ( ScaleMonomial ( `,` ScaleMonomial )* `,`? )? `)`
> ScaleMonomial -> `-`? ScaleFactor ( `*` ScaleFactor )*
> ScaleFactor -> INTEGER_LITERAL | Fraction | Path ( `^` `-`? INTEGER_LITERAL )?
> CoordinateScale -> CoordinateName `:` Path
> ```

[Polynomial expressions](smooth-declarations.md#polynomial-expressions)
gives the production `Fraction`.

`indexed physical PG: P<X> = interpret(g, reading = r, entries);` declares
the **physical interpretation** `PG` of the [metric](smooth-declarations.md#metrics)
`g` of `X` under the reading `r` of `X`. The entries give the Gram matrix of
`g` in terms of scales. The interpretation states that the terms of the
metric have one physical dimension, and the kernel checks it. The metric
stays a metric of [Smooth affine declarations](smooth-declarations.md): it is
valid with and without its interpretations, and `flat` and `sharp` read only
its Gram matrix.

Each entry of `gram(…)` is a monomial $c \cdot s_1^{e_1} \cdots s_k^{e_k}$
in distinct scales sᵢ with integer exponents eᵢ. Its coefficient c is the product of its
integer and fraction factors, negated by a leading `-`, and 1 without such a
factor. Its value is c times the products of the magnitudes, and its
dimension is the sum of eᵢ times the dimension of sᵢ. `euclidean` stands for
the identity matrix with dimensionless entries.
`normalized(x₁: s₁, …, xₙ: sₙ)` stands for the diagonal matrix with the
entries 1/sᵢ², each of the dimension −2 times the dimension of sᵢ.

The term $g_{ij}\,dx^i\,dx^j$ of the metric has the dimension of the entry
in row i and column j, plus the dimensions of the quantity kinds that the
reading gives to the coordinates xⁱ and xʲ. The value of the
interpretation is the dimension of its terms with a nonzero entry.
`value = D` declares it, and the kernel compares it with the terms.

Rules:

- The family must have the `physical_metric` representation, the
  declaration must name exactly one object, and the object must be a smooth
  affine object that the family accepts. Otherwise it is an error
  (`E_DIMENSION`).
- The path after `interpret(` must name a metric of the object. The path
  after `reading =` must name a reading of the object. Otherwise it is an
  error (`E_DIMENSION`). A missing `reading =` is an error (`E_PARSE`).
- `gram(…)` must have `dim X` rows of `dim X` entries. Otherwise it is an
  error (`E_DIMENSION`).
- Each path in an entry must name a scale, and an entry must name each scale
  once. Otherwise it is an error (`E_DIMENSION`), even when one of the
  exponents is 0.
- An entry must have at most 16 scale factors (`dimensionScaleFactors`), and
  each exponent must be at most 64 in absolute value (`dimensionExponent`).
  The numerator and the denominator of the coefficient must have at most
  `metricEntryBits` bits, and so must those of the entry multiplied out,
  counted before its factors cancel as
  [Appendix D](../appendix/limits.md#physical-dimensions) says. Otherwise it
  is an error (`E_LIMIT`).
- `normalized(…)` must name each coordinate of the object exactly once, each
  with a scale. Otherwise it is an error (`E_DIMENSION`).
- The scale of a coordinate in `normalized(…)` must be of the quantity kind
  that the reading gives to the coordinate. Otherwise it is an error
  (`E_DIMENSION`), even when the dimensions agree. In `gram(…)` only the
  dimensions of the scales count.
- Each entry, with the magnitudes of its scales, must equal the entry of the
  Gram matrix of the metric. Otherwise it is an error (`E_DIMENSION`).
- Every term with a nonzero entry must have one dimension. Otherwise it is
  an error (`E_DIMENSION`). A zero entry constrains nothing. Each exponent of
  that dimension must be at most 64 in absolute value (`dimensionExponent`),
  as in a declared value. Otherwise it is an error (`E_LIMIT`).
- A declared value must be a dimension by the rules of
  [base dimensions and quantity kinds](#base-dimensions-and-quantity-kinds),
  and it must equal the dimension of the terms. Otherwise it is an error
  (`E_DIMENSION`). An interpretation without a nonzero term has no value, and
  a declared value is an error (`E_DIMENSION`).
- Any word other than `euclidean`, `gram` or `normalized` is an error
  (`E_TYPE`).
- An interpretation used as a value, or called, is an error (`E_TYPE`).

> **Implementation note.** The kernel evaluates the entries and the
> dimensions of the terms, and the declaration audit checks every nature
> declaration again (`NatureDimension.checkPhysicalMetric`). Messages write
> a dimension as the powers of its base dimensions in their declaration
> order, as in `L^2*T^-1`, and `1` for the dimensionless one. A base
> dimension appears by its full path when another base dimension of the
> program has its name. A message writes a magnitude only within
> `metricEntryBits`, and otherwise says that it is larger. The oracle
> theorem `VastitasOracle.NatureDimension.physicalMetric_sound` states what an
> accepted interpretation means, and `euclidean_rejected` and
> `normalized_rejected_of_kind` state the two rejections of the examples
> below. `VastitasOracle.NatureWeakening.entryValid_nature_weakening`,
> `evalPrimitive_nature_weakening`, `metric_nature_free` and
> `flat_sharp_nature_free` state that nature declarations change no other
> declaration and no value.

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/physical-dimensions/main.vast:metrics}}
{{#include ../../examples/packages/physical-dimensions/main.vast:physical}}
```

With l0 = 3 and t0 = 2, `gram((l0^-2, 0), (0, t0^-2))` is diag(1/9, 1/4),
the Gram matrix of `G`. Its terms dx²/l0² and dt²/t0² are dimensionless, so
`PG` and `PN` have the value 1. `PM` reads the metric M = diag(1, −9) as
dx² − c² dt² with the speed c = 3, whose terms have the dimension L².

The Euclidean metric of the chart adds a squared length to a squared time:

```vast
{{#include ../../examples/reject/packages/dimension-dx2-dt2/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/dimension-dx2-dt2.stderr}}
```

The following entry does not give the Gram matrix of `G`:

```vast
{{#include ../../examples/reject/packages/dimension-gram-magnitude/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/dimension-gram-magnitude.stderr}}
```

The following declared value differs from the dimension of the terms:

```vast
{{#include ../../examples/reject/packages/dimension-declared-value/main.vast:declaration}}
```

```text
{{#include ../../examples/reject/packages/dimension-declared-value.stderr}}
```

`normalized` compares kinds, and `Wavelength` is not `Length`:

```vast
{{#include ../../examples/reject/packages/dimension-wrong-kind/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/dimension-wrong-kind.stderr}}
```

## The library nature::dimension

The package `nature` holds physical interpretations of the objects of the
standard library. It depends on the standard library, and no package of the
standard library depends on it. Its module `nature::dimension` declares:

| Name | Declaration |
| --- | --- |
| `Reading`, `PhysicalMetric` | The families of readings and of physical interpretations of the smooth affine objects of `CInfAffine` |
| `L`, `T`, `M` | The base dimensions of length, time and mass |
| `Length`, `Time`, `Mass` | The quantity kinds of the dimensions L, T and M |
| `Speed` | The quantity kind of the dimension L · T⁻¹ |
| `Wavelength` | A quantity kind of the dimension L, other than `Length` |
| `Energy`, `Torque` | Two quantity kinds of the dimension M · L² · T⁻² |

A program declares its own readings, scales and interpretations, and it may
declare further base dimensions and quantity kinds. A manifest names the
package by path, next to the standard library, as
[Manifests](../packages.md#manifests) says.

A program imports the declarations of the module one by one, as in
`use nature::dimension::Length;`, names them by full paths, as in
`nature::dimension::Mass`, or binds the module under another name, as in
`use nature::dimension as dim;`. `dimension` is a
[reserved name](lexical-structure.md#reserved-names) for the name that a
`use` declaration binds, so a plain `use nature::dimension;` is an error
(`E_RESERVED`). A `use` declaration imports one path, as
[`use` declarations](modules.md#use-declarations) says, so a grouped import
such as `use nature::dimension::{Length, Time};` is an error (`E_PARSE`).

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/physical-dimensions/main.vast:imports}}
```

```vast
{{#include ../../examples/reject/packages/dimension-module-import/main.vast:import}}
```

```text
{{#include ../../examples/reject/packages/dimension-module-import.stderr}}
```

## Scope of physical dimensions

Physical dimensions cover the coordinates of smooth affine objects and the
constant metrics on them. Exponents are integers. A scale is a magnitude,
and the language has no unit system and no conversion between units, such as
100 cm = 1 m. A reading gives kinds to the coordinates of an object and to
nothing else: frames, fibers, arrays and gradients have no physical
dimension. A program that declares no nature declaration has the same
checking and the same generated code as with them.
