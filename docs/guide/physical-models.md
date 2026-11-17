# A physical model and its data

This chapter follows one physical model from its assumptions to a
comparison with measured data. A two-level system, such as an atom with a
ground state and an excited state, is driven by a field near the frequency
of its transition. Two numbers describe the drive: the detuning δ, the
distance of the drive from the transition frequency, and the Rabi frequency
Ω, the strength of the drive. Prepared in the ground state g, the system is
found in the excited state e with a probability that oscillates in time. Its
average over a long time is Ω²/(2(δ² + Ω²)), which is 1/2 on resonance and
falls off as the drive moves away from it.

The program states that model, lets the compiler check the closed form
Ω²/(2(δ² + Ω²)) against the matrix of the model, records a calibration of Ω
and five measured points, and records that the data agree with the
prediction. The compiler checks the agreement again from the numbers. When
the calibration changes, the recorded agreement is no longer accepted until
it is recorded again, while everything that the model computes still
checks. Every number is a rational number. The program shows the prediction
at each data point and exits with status 0.

The program is the package
[`examples/packages/nature/two-level/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/nature/two-level).
Run it from the repository root:

```sh
python3 scripts/build_stdlib_package.py
target/debug/vastitas build --manifest-path examples/packages/nature/two-level/Vastitas.toml -o target/two-level
./target/two-level
```

## The package

The package depends on the standard library and on `nature`, as the
programs of the [previous chapters](spectral-observations.md) do:

```toml
{{#include ../../examples/packages/nature/two-level/Vastitas.toml}}
```

It imports the smooth profile, the spectral families of the standard
library, and the families of three modules of `nature`: `nature::dimension`
for the units of the coordinates, `nature::model` for the meaning of the
model and `nature::errorbar` for the data:

```vast
{{#include ../../examples/packages/nature/two-level/src/main.vast:imports}}
```

The standard library holds the mathematics: the matrix, its eigenvalues and
the average. `nature` holds what the mathematics means for an experiment,
and none of its declarations changes a value or the generated code of the
standard library.

## The field and its average

The chart `P` has the coordinates `delta` and `omega`. In a frame that
rotates with the drive, and with energies written as frequencies, the
Hamiltonian of the system is the symmetric matrix
H = (δ/2)σ_z + (Ω/2)σ_x on the basis `g`, `e`:

```vast
{{#include ../../examples/packages/nature/two-level/src/main.vast:field}}
```

Its eigenvalues ±√(δ² + Ω²)/2 meet only where δ = Ω = 0. The program
declares the spectrum of H and a branch on the region where δ² + Ω² ≠ 0,
which a gap witness certifies, as
[Matrix fields and their spectra](spectral-observations.md#simple-eigenvalues-on-a-chart)
explains:

```vast
{{#include ../../examples/packages/nature/two-level/src/main.vast:branch}}
```

The long-time average of the probability to find e after preparing g is the
sum over the two eigenprojectors P₁ and P₂ of P_k[e, g]². The program states
it as a closed form, `ratio(N, D)` with N = Ω²/2 and D = δ² + Ω²:

```vast
{{#include ../../examples/packages/nature/two-level/src/main.vast:average}}
```

The compiler checks the closed form without computing an eigenvalue. From
the characteristic polynomial and the gap witness it computes a polynomial
T, the sum over the eigenvalues written through the trace, and accepts the
average only when N·(δ² + Ω²)² = D·T. It also checks that D does not vanish
on the region, so that the closed form has a value at every point of it. A
closed form without the factor 1/2 is rejected, with a term of the
difference:

```vast
{{#include ../../examples/reject/packages/two-level-wrong-average/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/two-level-wrong-average.stderr}}
```

## What the model means

So far the program is mathematics. The model says what it means. Both
coordinates are frequencies, the inverse of a time. The convention
`hbar_one` writes energies as angular frequencies. The model names the
matrix, the reading of the coordinates, the convention, the prepared state
`g`, the observed state `e`, the average that it predicts and the regime in
which it holds:

```vast
{{#include ../../examples/packages/nature/two-level/src/main.vast:model}}
```

The compiler checks that the pieces fit: the reading reads the chart of the
matrix, `g` and `e` are basis vectors of the module of the matrix, and the
average is the one from `g` to `e` of a branch of that matrix. A state of
another module, or a reading of another chart with the same coordinates,
is rejected. The regime is recorded as written. The rotating-wave
approximation behind the matrix, and the reading of the average as a
long-time average, are assumptions that the program states and that no
check proves.

## A calibration

The Rabi frequency comes from a measurement of the drive power, with an
uncertainty. The program records it as a calibration: Ω = 5/2 with the
standard uncertainty 1/20, evaluated by other means than statistics
(`type_b`), with a reference and a revision:

```vast
{{#include ../../examples/packages/nature/two-level/src/main.vast:calibration}}
```

The compiler computes a fingerprint of the calibration from its values,
uncertainties, method, reference and revision. A change to one of them gives
another fingerprint, unless the 64-bit digest happens to collide.

## Measured points

The dataset holds five measurements of the probability of e, at five
detunings, each with the standard uncertainty 1/50, and the coverage factor
2. A point gives the detuning; the calibration gives Ω:

```vast
{{#include ../../examples/packages/nature/two-level/src/main.vast:dataset}}
```

The compiler checks that each point gives exactly the coordinates that the
calibration leaves open, and that with Ω = 5/2 it lies on the region of the
branch, where the eigenvalues stay apart. A point at δ = Ω = 0 would be
rejected, whatever the closed form says there.

## The comparison

The comparison records the fingerprint of the calibration that it was
reviewed against and a verdict:

```vast
{{#include ../../examples/packages/nature/two-level/src/main.vast:comparison}}
```

The compiler computes the verdict again. At each point it evaluates the
prediction A exactly, here 25/(8δ² + 50) at Ω = 5/2, and the derivative of A
with respect to Ω, which carries the uncertainty of the calibration to the
prediction. A point agrees when the square of the difference between A and
the measured value is at most k² times the sum of the squared uncertainty
of the point and the squared contribution of the calibration. No square root
is taken. All five points agree, so the verdict is `consistent`, and
recording `inconsistent` is an error:

```vast
{{#include ../../examples/reject/packages/two-level-wrong-verdict/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/two-level-wrong-verdict.stderr}}
```

Moving the measured value at resonance from 1/2 to 3/5 makes that point
disagree, and then `consistent` is the error and `inconsistent` is
accepted. The test carries the calibration to first order and treats the
uncertainties as uncorrelated; both are assumptions of the comparison.

## The predictions

`main` shows the prediction at each point of the dataset. Ω = 5/2 is no
integer, so `at(n, m)` builds the point (n/2, m/2) from a point with integer
coordinates and the map that halves both:

```vast
{{#include ../../examples/packages/nature/two-level/src/main.vast:observation}}
```

```vast
{{#include ../../examples/packages/nature/two-level/src/main.vast:main}}
```

The program shows:

```text
avg(at(0, 5)) = (1, 2)
avg(at(2, 5)) = (25, 58)
avg(at(4, 5)) = (25, 82)
avg(at(-2, 5)) = (25, 58)
avg(at(5, 5)) = (1, 4)
```

and exits with status 0. Each pair is a reduced fraction: 1/2 on resonance,
25/58 at δ = ±1, 25/82 at δ = 2 and 1/4 at δ = 5/2. Off the region of the
branch the observation gives `(0, 0)`.

## When the calibration changes

Suppose the calibration of Ω is evaluated again, and its uncertainty
becomes 1/25. The data and the model stay as they are. The comparison still
records the fingerprint of the old calibration, so the compiler rejects it,
and the message names the fingerprint of the calibration as it is:

```vast
{{#include ../../examples/reject/packages/two-level-stale/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/two-level-stale.stderr}}
```

Only the comparison is rejected. The matrix, its eigenvalues, the average,
the model, the calibration and the dataset are checked as before, and a
program without the comparison is accepted and generates the same code.
After a review of the data under the changed calibration, recording the
fingerprint from the message makes the comparison accepted again, with the
verdict that the compiler computes.

> **What is checked.** The checker checks each closed form against the
> matrix of its model by identities of polynomials, checks the references of
> each model, each point against the region of its branch, each verdict from
> the numbers and each fingerprint against its calibration, before the
> compiler generates code. The [proofs](../verification.md#physical-models)
> cover what an accepted average, model and comparison satisfy: the closed
> form is the trace form and gives the observed values, the verdict is the
> one that the inequality decides, a comparison records the fingerprint of
> its calibration, and the model and its data change no value of the
> standard library. They also show that an accepted average is the sum of
> the squared entries of the eigenprojectors of the real matrix. Tests cover
> the predictions that the program shows, the rejected programs of this
> chapter, the changed calibration, and the program without its comparison
> and without every declaration of `nature`, which generates the same code.
> The meaning of the model, its regime, the long-time reading of the average
> and the first-order propagation of uncertainties are assumptions that the
> program records.

## See also

- [Physical models](../language/physical-models.md): conventions, models,
  calibrations, datasets, comparisons, recorded texts and their rules.
- [Transition averages](../language/spectral-observations.md#transition-averages)
  and [Average observations](../language/spectral-observations.md#average-observations):
  `transition_average(…) = ratio(N, D)` and `average_at`.
- [Physical dimensions](../language/physical-dimensions.md): quantities and
  readings.
- [Spectral observations](../language/spectral-observations.md): free
  modules, fields, spectra and branches.
