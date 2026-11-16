# Physical models

This chapter defines the declarations of
[`nature::model`](https://github.com/MGYamada/Vastitas/blob/main/nature/docs/model.md)
and
[`nature::errorbar`](https://github.com/MGYamada/Vastitas/blob/main/nature/docs/errorbar.md):
conventions, models, calibrations, datasets and comparisons. A model says
what a symmetric endomorphism field of
[Spectral observations](spectral-observations.md) means physically: which
reading of [Physical dimensions](physical-dimensions.md) its coordinates
have, which state is prepared and which is observed, which
[transition average](spectral-observations.md#transition-averages) it
predicts, and in which regime it holds. A calibration gives measured values
to some coordinates. A dataset holds measured values of the prediction at
points, and a comparison records whether the data agree with the
prediction. The general rules of `indexed` declarations are in
[Indexed declarations](../indexed-source.md). [Notation](notation.md)
explains the Syntax blocks, and the [glossary](../appendix/glossary.md)
defines the terms.

These declarations compute nothing. They change no value, no validity and
no generated code of a declaration of the other chapters, and a program
without them generates the same code. The kernel checks their references
(`E_MODEL`), their data and verdicts (`E_ERRORBAR`) and the fingerprint that
a comparison records (`E_STALE`). Every value is an exact rational number,
and every check is an identity or an inequality of rational numbers.

A path in a declaration of this chapter that resolves to nothing is an
error of [resolution](names-and-paths.md#resolution) (`E_NAME`), before the
rules of this chapter apply. The kernel checks the transition averages
before the models, and the models before the calibrations, datasets and
comparisons, so a program reports the first error in that order.

The examples quote the tested package
[`examples/packages/two-level/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/two-level),
a two-level system on the chart `P = Affine(2)[delta, omega]` of the
detuning and the Rabi frequency, with the field
H = (δ/2)σ_z + (Ω/2)σ_x on the basis `g`, `e` and the transition average
Ω²/(2(δ² + Ω²)) from `g` to `e`. Its executable shows the prediction at five
points and exits with status 0. Each rejected program is a package on the
profiles of the standard library and of `nature`. It appears with the
diagnostic that the compiler prints for it.

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

A **recorded text** is a string literal at one of the four places of this
chapter that take one: the regime of a model, the reference and the revision
of a calibration and the fingerprint of a comparison. No other construct of
the language accepts a string literal. The production
[`STRING_LITERAL`](lexical-structure.md#other-literals) gives its form:
printable ASCII characters, from the space to `~`, other than `\` and `"`,
between double quotes. No escape sequence is decoded. The text is recorded
as written, and no check reads its meaning.

Rules:

- A recorded text that `STRING_LITERAL` does not derive, such as a literal
  with `\`, with a character that is not printable ASCII or without a
  closing quote, is an error (`E_PARSE`) at the literal.
- A recorded text must hold at most `recordTextBytes` = 256 bytes between
  its quotes ([limits](../appendix/limits.md#physical-models-and-data)).
  Otherwise it is an error (`E_LIMIT`) at the literal.

> **Implementation note.** The kernel checks the characters and the length
> of each recorded text of a request again, and a request with another text
> is an error (`E_PROTOCOL`), so that the kernel and the frontend accept the
> same texts.

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

Rules:

- A family with one of these representations must have exactly one
  parameter, of the form `object(K)`, and exactly the constraint
  `canonical(0)`. Otherwise it is an error (`E_TYPE`).
- A declaration of this chapter must name exactly one smooth affine object,
  and its family must have the representation of its kind and accept the
  object. Otherwise it is an error (`E_MODEL` for a model, `E_ERRORBAR` for
  a calibration, a dataset or a comparison).

## Conventions

> **Syntax**
>
> ```text
> ConventionDeclaration -> `indexed` `convention` IDENTIFIER `=` `hbar_one` `;`
> ```

A **convention** records how a model writes its physical quantities.
`hbar_one` is the one convention of the profile: it writes energies as
angular frequencies (ħ = 1), so that the eigenvalues of a field are
frequencies. A convention has no family, changes no value and makes no
unit of an eigenvalue.

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

A **model** on `X` names its field, `hamiltonian = H`, the reading of the
coordinates of `X`, its convention, the prepared and the observed basis
vector of the module of H, the transition average that it predicts and its
regime. The regime, such as the rotating-wave approximation, is a recorded
assumption: no check reads or proves it.

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/two-level/src/main.vast:model}}
```

Rules:

- The fields must be `hamiltonian =`, `reading =`, `convention =`,
  `prepare =`, `observe =`, `predicts =` and `regime =`, in this order. A
  missing or a misplaced field is an error (`E_PARSE`).
- The prepared and the observed vector must be identifiers. Otherwise it is
  an error (`E_PARSE`).
- The regime must be `assume` applied to a recorded text. Another regime is
  an error (`E_PARSE`).
- The path after `hamiltonian =` must name an endomorphism field of the
  object of the model, after `reading =` a reading of that object and after
  `convention =` a convention. Otherwise it is an error (`E_MODEL`).
- The prepared and the observed vector must be basis vectors of the free
  module of the hamiltonian. Otherwise it is an error (`E_MODEL`), whose
  message lists the basis.
- The path after `predicts =` must name a transition average of the object
  of the model, of a branch of a spectrum of the hamiltonian, from the
  prepared to the observed vector. Otherwise it is an error (`E_MODEL`).

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

A **measured value** `measured(v, u = w)` is the exact rational value v with
the standard uncertainty w. [Polynomial expressions](smooth-declarations.md#polynomial-expressions)
gives the production `Fraction`: a rational number is an integer literal or a
fraction, with an optional `-`.
[Smooth affine declarations](smooth-declarations.md) gives the production
`CoordinateName`.

A **calibration** of `X` gives measured values to some coordinates of `X`,
which the points of a dataset then do not give. The calibrated coordinates
come first, each followed by `,`, and `method` ends them. The method is the
type of evaluation of the uncertainties: `type_a` by statistics, `type_b`
by other means. The reference and the revision record where the values come
from and which evaluation of them this is.

The **fingerprint** of a calibration is `fnv1a64:` and 16 lowercase
hexadecimal digits: the FNV-1a digest of its canonical content. The
canonical content lists the calibrated coordinates in the order of the
coordinates of the object, each with its name, value and uncertainty, then
the method, the reference and the revision. A value or an uncertainty is
written as a reduced fraction, and a name or a text with its length in
bytes, so that no text can stand for another. A change to a value, an
uncertainty, the method, the reference or the revision changes the
canonical content, and so the fingerprint, unless the 64-bit digest
collides. The fingerprint does not depend on the order in which the source
lists the coordinates.

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/two-level/src/main.vast:calibration}}
```

Rules:

- The fields after the coordinates must be `method =`, `reference =` and
  `revision =`, in this order. A missing or a misplaced field is an error
  (`E_PARSE`).
- A method other than `type_a` and `type_b` is an error (`E_TYPE`).
- The reference and the revision must be recorded texts.
- The rules of the literals of
  [polynomial expressions](smooth-declarations.md#polynomial-expressions)
  apply to each rational number.
- A calibration must calibrate at least one coordinate, each a coordinate of
  its object and at most once. Otherwise it is an error (`E_ERRORBAR`).
- Every standard uncertainty must be positive. Otherwise it is an error
  (`E_ERRORBAR`).

> **Implementation note.** The canonical content is the text
> `vastitas-calibration 1`, one line `coordinate` per calibrated coordinate,
> and the lines `method`, `reference` and `revision`, each ended by a line
> feed (`NatureErrorbar.canonicalContent`). The digest is the 64-bit FNV-1a
> hash that the build identity of the kernel uses (`BuildIdentity.fnv1a`),
> over the UTF-8 bytes of that text. The fingerprint is no cryptographic commitment: it detects a
> changed calibration, and it does not authenticate one.

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

A **dataset** of a model under a calibration holds points of the object of
the model. A point gives exact values to the coordinates that the
calibration does not give, and ends with the measured value of the
observable of the model there. `value = measured(…)` ends the coordinates,
so a coordinate may be named `value`. The **coverage factor** k of the
dataset scales every uncertainty when the kernel decides whether a point
agrees with the prediction, as [Comparisons](#comparisons) says.

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/two-level/src/main.vast:dataset}}
```

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
- The path after `model =` must name a model, and the path after
  `calibration =` a calibration, both of the object of the dataset.
  Otherwise it is an error (`E_ERRORBAR`).
- A dataset must have at least one point. The coverage factor and every
  standard uncertainty must be positive. Otherwise it is an error
  (`E_ERRORBAR`).
- Each point must give each coordinate that the calibration does not give
  exactly once, and no coordinate that it gives. Otherwise it is an error
  (`E_ERRORBAR`).
- With the calibrated values, every point must lie on the chart D(g) of the
  branch of the average that the model predicts, whatever the closed form of
  the average. Otherwise it is an error (`E_ERRORBAR`), whose message names
  the point.

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

A **comparison** names a dataset and its calibration, and records the
fingerprint of the calibration and a **verdict**, `consistent` or
`inconsistent`. The kernel computes the verdict again and compares it with
the recorded one. Let A = N/D be the closed form of the average that the
model predicts. At a point p of the dataset, with the measured value v, the
standard uncertainty u and the calibrated coordinates c with their
uncertainties u_c, the kernel computes A(p) and each partial derivative
∂A/∂c = (∂_c N · D − N · ∂_c D)/D² at p. The point is consistent when

$$
(A(p) - v)^2 \le k^2 \Bigl( u^2 + \sum_c \Bigl(\frac{\partial A}{\partial c}(p)\Bigr)^2 u_c^2 \Bigr) ,
$$

an inequality of rational numbers without a square root. The verdict is
`consistent` when every point is consistent and `inconsistent` otherwise.
The inequality propagates the uncertainties of the calibration to first
order and treats all uncertainties as uncorrelated. Both are assumptions of
the comparison, not facts that the kernel establishes.

A comparison is **stale** when the fingerprint that it records is not the
current fingerprint of its calibration: the calibration changed after the
comparison was recorded. The message names the current fingerprint, so
that the comparison can be recorded again after a review of the data.
Staleness concerns the comparison alone: the declarations of the standard
library and the model are checked and accepted as before, and so are the
calibration and the dataset when they satisfy their own rules. The program
without the comparison is then accepted.

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/two-level/src/main.vast:comparison}}
```

At Ω = 5/2 the prediction at δ is 25/(8δ² + 50). Each of the five values of
the dataset lies within 2 × 1/50 of the prediction at its point, so the
kernel computes the verdict `consistent`.

Rules:

- The first argument of `compare` is the dataset. The fields must be
  `calibration =`, `fingerprint =` and `verdict =`, in this order. A missing
  or a misplaced field is an error (`E_PARSE`).
- The fingerprint must be a recorded text.
- A verdict other than `consistent` and `inconsistent` is an error
  (`E_TYPE`).
- The first argument must name a dataset of the object of the comparison,
  and the path after `calibration =` the calibration of that dataset.
  Otherwise it is an error (`E_ERRORBAR`).
- The recorded fingerprint must be the current fingerprint of the
  calibration. Otherwise it is an error (`E_STALE`), whose message names the
  current fingerprint. The kernel reports it before it computes the verdict.
- The recorded verdict must be the verdict that the kernel computes.
  Otherwise it is an error (`E_ERRORBAR`), whose message names the first
  inconsistent point with both sides of its inequality, or says that every
  point is consistent.

A calibration evaluated again after the comparison was recorded makes the
comparison stale:

```vast
{{#include ../../examples/reject/packages/two-level-stale/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/two-level-stale.stderr}}
```

A verdict that the data do not support is an error:

```vast
{{#include ../../examples/reject/packages/two-level-wrong-verdict/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/two-level-wrong-verdict.stderr}}
```

> **Implementation note.** `NatureModel.checkModel` and
> `NatureErrorbar.checkCalibration`, `checkDataset` and `checkComparison`
> are the checks of the declaration audit; `IndexedModelSource.lean` and
> `IndexedErrorbarSource.lean` elaborate the declarations and give the
> messages. The verdict reads the closed form of the average that the
> kernel has checked against the trace form of its branch
> ([Transition averages](spectral-observations.md#transition-averages)), and
> no value of a dataset reaches generated code.

## Scope of physical models

The profile has one convention, `hbar_one`, models of a symmetric field with
a transition average between two basis vectors, calibrations, datasets of
at most 64 points and recorded comparisons. Every value is an exact rational
number. Outside the profile are the numerical realization of a model under
a named solver with an error bound, time evolution, Hermitian fields over
the Gaussian rationals, correlated uncertainties and statistics beyond the
pointwise test, physical units of eigenvalues and ħ as a dimension, and data
read from files. The regime of a model, the agreement of the model with the
experiment, the reading of the average as a long-time average of the
dynamics and the first-order propagation of uncertainties are assumptions
that the program records; no check establishes them.
