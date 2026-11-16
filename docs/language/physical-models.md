# Physical models

This chapter defines the source forms of the declarations of
[`nature::model`](https://github.com/MGYamada/Vastitas/blob/main/nature/docs/model.md)
and
[`nature::errorbar`](https://github.com/MGYamada/Vastitas/blob/main/nature/docs/errorbar.md):
conventions, models, calibrations, datasets and comparisons. A model on a
smooth affine object `X` names a symmetric endomorphism field of
[Spectral observations](spectral-observations.md), a reading of
[Physical dimensions](physical-dimensions.md), a convention, a prepared and
an observed basis vector, the
[transition average](spectral-observations.md#transition-averages) that it
predicts and its regime. A calibration gives measured values to coordinates
of `X`. A dataset holds measured values of the prediction of a model at
points of `X`, and a comparison records the verdict of a dataset against its
model. The general rules of `indexed` declarations are in
[Indexed declarations](../indexed-source.md). [Notation](notation.md)
explains the Syntax blocks.

These declarations compute nothing. They change no value, no validity and
no generated code of a declaration of the other chapters. The kernel checks
their references (`E_MODEL`), their data and verdicts (`E_ERRORBAR`) and the
fingerprint that a comparison records (`E_STALE`), as the pages of the two
modules and [Appendix B](../appendix/diagnostics.md) state. This chapter
gives their syntax and the rules of their syntax.

The declarations of this chapter are the forms of
`PhysicalModelDeclaration`:

> **Syntax**
>
> ```text
> PhysicalModelDeclaration -> ModelFamily | ConventionDeclaration
>     | ModelDeclaration | CalibrationDeclaration | DatasetDeclaration
>     | ComparisonDeclaration
> ```

Each declaration of this chapter is an [item](items.md):
`PhysicalModelDeclaration` is one form of
[`IndexedDeclaration`](../indexed-source.md). `pub` before a declaration
makes it visible outside its module.

## Recorded texts

A recorded text is a string literal at one of the four places of this
chapter that take one: the regime of a model, the reference and the revision
of a calibration and the fingerprint of a comparison. No other construct of
the language accepts a string literal. The production
[`STRING_LITERAL`](lexical-structure.md#other-literals) gives its form:
printable ASCII characters, from the space to `~`, other than `\` and `"`,
between double quotes. No escape sequence is decoded, and the wire carries
the text as written.

Rules:

- A recorded text that `STRING_LITERAL` does not derive, such as a literal
  with `\`, with a character that is not printable ASCII or without a
  closing quote, is an error (`E_PARSE`) at the literal.
- A recorded text must hold at most `recordTextBytes` = 256 bytes between
  its quotes ([limits](../appendix/limits.md#physical-models-and-data)).
  Otherwise it is an error (`E_LIMIT`) at the literal.
- The kernel checks the characters and the length of each recorded text of
  a request again. A request with another text is an error (`E_PROTOCOL`).

## The model profile

> **Syntax**
>
> ```text
> ModelFamily -> `indexed` `family` IDENTIFIER `(` Parameters? `)`
>     `=` ModelRepresentation `constraints` `(` Constraints? `)` `;`
> ModelRepresentation -> `model` | `calibration` | `dataset` | `comparison`
> ```

[Families](../indexed-source.md#families) gives the productions
`Parameters` and `Constraints`. In the table, `X` is a smooth affine object.

| Representation | Indexed type | The declarations that name it |
| --- | --- | --- |
| `model` | `Model<X>` | The [models](#models) on `X` |
| `calibration` | `Calibration<X>` | The [calibrations](#calibrations) of coordinates of `X` |
| `dataset` | `Dataset<X>` | The [datasets](#datasets) of the models on `X` |
| `comparison` | `Comparison<X>` | The [comparisons](#comparisons) of the datasets on `X` |

`nature::model` declares the family `Model`, and `nature::errorbar` the
families `Calibration`, `Dataset` and `Comparison`, over the classification
`CInfAffine` of `std::geometry::smooth::affine`. None of the types has a
value.

## Conventions

> **Syntax**
>
> ```text
> ConventionDeclaration -> `indexed` `convention` IDENTIFIER `=` `hbar_one` `;`
> ```

`hbar_one` is the one convention of the profile: it writes energies as
angular frequencies (ħ = 1). A convention has no family.

Rules:

- A word other than `hbar_one` after `=` is an error (`E_TYPE`).

## Models

> **Syntax**
>
> ```text
> ModelDeclaration -> `indexed` `model` IDENTIFIER `:` Path
>     `<` Path ( `,` Path )* `>` `=` `model` `(` `hamiltonian` `=` Path
>     `,` `reading` `=` Path `,` `convention` `=` Path
>     `,` `prepare` `=` IDENTIFIER `,` `observe` `=` IDENTIFIER
>     `,` `predicts` `=` Path `,` `regime` `=` `assume` `(` STRING_LITERAL `)` `)` `;`
> ```

The regime, such as the rotating-wave approximation, is a recorded
assumption. No check reads or proves its text.

Rules:

- The fields must be `hamiltonian =`, `reading =`, `convention =`,
  `prepare =`, `observe =`, `predicts =` and `regime =`, in this order. A
  missing or a misplaced field is an error (`E_PARSE`).
- The prepared and the observed vector must be identifiers. Otherwise it is
  an error (`E_PARSE`).
- The regime must be `assume` applied to a recorded text. Another regime is
  an error (`E_PARSE`).
- The reading must be a reading of the object of the model, and the
  prepared and the observed vector must be basis vectors of the free module
  of the hamiltonian. Otherwise it is an error (`E_MODEL`).

A prepared vector of another free module of the same object is an error:

```vast
{{#include ../../examples/reject/packages/two-level-other-basis/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/two-level-other-basis.stderr}}
```

So is a reading of another object, even one with the same coordinates:

```vast
{{#include ../../examples/reject/packages/two-level-other-reading/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/two-level-other-reading.stderr}}
```

## Calibrations

> **Syntax**
>
> ```text
> CalibrationDeclaration -> `indexed` `calibration` IDENTIFIER `:` Path
>     `<` Path ( `,` Path )* `>` `=` `calibrate` `(`
>     ( CoordinateName `=` Measured `,` )*
>     `method` `=` CalibrationMethod `,` `reference` `=` STRING_LITERAL
>     `,` `revision` `=` STRING_LITERAL `)` `;`
> CalibrationMethod -> `type_a` | `type_b`
> Measured -> `measured` `(` Rational `,` `u` `=` Rational `)`
> Rational -> `-`? ( Fraction | INTEGER_LITERAL )
> ```

A measured value `measured(v, u = w)` is the exact value v with the standard
uncertainty w. [Polynomial expressions](smooth-declarations.md#polynomial-expressions)
gives the production `Fraction`: a rational number is an integer literal or a
fraction, with an optional `-`. [Smooth affine declarations](smooth-declarations.md) gives the production
`CoordinateName`. The
calibrated coordinates come first, each followed by `,`, and `method` ends
them. The method is the type of evaluation of the uncertainties: `type_a`
by statistics, `type_b` by other means.

Rules:

- The fields after the coordinates must be `method =`, `reference =` and
  `revision =`, in this order. A missing or a misplaced field is an error
  (`E_PARSE`).
- A method other than `type_a` and `type_b` is an error (`E_TYPE`).
- The reference and the revision must be recorded texts.
- The rules of the literals of
  [polynomial expressions](smooth-declarations.md#polynomial-expressions)
  apply to each rational number.

## Datasets

> **Syntax**
>
> ```text
> DatasetDeclaration -> `indexed` `dataset` IDENTIFIER `:` Path
>     `<` Path ( `,` Path )* `>` `=` `measure` `(` `model` `=` Path
>     `,` `calibration` `=` Path `,` `coverage` `=` Rational
>     `,` `points` `=` DataPoints `)` `;`
> DataPoints -> `[` ( DataPoint ( `,` DataPoint )* `,`? )? `]`
> DataPoint -> `(` ( CoordinateName `=` Rational `,` )* `value` `=` Measured `)`
> ```

The coverage factor k scales the uncertainties of every point. A point
gives values to coordinates of `X` and ends with the measured value of the
observable. `value = measured(…)` ends the coordinates, so a coordinate may
be named `value`.

Rules:

- The fields must be `model =`, `calibration =`, `coverage =` and
  `points =`, in this order. A missing or a misplaced field is an error
  (`E_PARSE`).
- A point must be a parenthesized tuple that ends with
  `value = measured(v, u = w)`, without a trailing comma. Otherwise it is an
  error (`E_PARSE`).
- A dataset must have at most `datasetPoints` = 64 points
  ([limits](../appendix/limits.md#physical-models-and-data)). Otherwise it
  is an error (`E_LIMIT`) at the list of points, before the kernel reads a
  point.
- With the calibrated values, every point must lie on the chart D(g) of the
  branch of the average that the model predicts, whatever the closed form of
  the average. Otherwise it is an error (`E_ERRORBAR`).

A point where the eigenvalues of the field meet lies off every chart:

```vast
{{#include ../../examples/reject/packages/two-level-off-chart/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/two-level-off-chart.stderr}}
```

## Comparisons

> **Syntax**
>
> ```text
> ComparisonDeclaration -> `indexed` `comparison` IDENTIFIER `:` Path
>     `<` Path ( `,` Path )* `>` `=` `compare` `(` Path
>     `,` `calibration` `=` Path `,` `fingerprint` `=` STRING_LITERAL
>     `,` `verdict` `=` Verdict `)` `;`
> Verdict -> `consistent` | `inconsistent`
> ```

A comparison names a dataset and its calibration, and records the
fingerprint of the calibration and a verdict. The fingerprint is `fnv1a64:`
and 16 hexadecimal digits, which the kernel computes from the content of the
calibration. A comparison whose recorded fingerprint is not the current one
is stale (`E_STALE`), and the message names the current fingerprint.

Rules:

- The first argument of `compare` is the dataset. The fields must be
  `calibration =`, `fingerprint =` and `verdict =`, in this order. A missing
  or a misplaced field is an error (`E_PARSE`).
- The fingerprint must be a recorded text.
- A verdict other than `consistent` and `inconsistent` is an error
  (`E_TYPE`).
- The recorded fingerprint must be the current fingerprint of the
  calibration. Otherwise it is an error (`E_STALE`), whose message names the
  current fingerprint.
- The recorded verdict must be the verdict that the kernel computes from
  the dataset. Otherwise it is an error (`E_ERRORBAR`).

A calibration evaluated again after the comparison was recorded makes the
comparison stale:

```vast
{{#include ../../examples/reject/packages/two-level-stale/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/two-level-stale.stderr}}
```

A verdict that the data do not support is an error, with the first
inconsistent point or the statement that every point is consistent:

```vast
{{#include ../../examples/reject/packages/two-level-wrong-verdict/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/two-level-wrong-verdict.stderr}}
```
