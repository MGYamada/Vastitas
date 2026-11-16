# Physical-dimension admission

This chapter is ADR 0002, the architecture decision record "Admission of
`nature::dimension` and the boundary between `std` and `nature`". It admits
the first module of the `nature` library family, `nature::dimension`, for the
finite profile of historical Stage 4. It records the boundary between the
mathematical standard library `std` and the physical interpretations of
`nature` as that boundary applies to this module. The record governs
admission. It does not claim that an admitted contract is implemented or
proved.

It writes its requirements with MUST and MUST NOT. What the compiler and the
libraries hold of it:

- Implemented, for the profile of the Stage 4 tracker: the `nature` package
  and the module `nature::dimension` (§3). The
  [Stage 4 acceptance record](../stage4-acceptance.md) states what is Tested
  and what is Proved.
- Tested: the dependency rule of §1. No `std` manifest depends on `nature`,
  and `scripts/check_boundaries.py` checks it in the continuous integration.
- Planned: the modules `nature::model` (§4) and `nature::errorbar` (§5) of
  historical Stage 6, admitted in the amendments of 2026-11-16; every other
  `nature` module, among them `nature::symmetry`; and the parts of
  `nature::dimension` that §3 leaves outside.

## Record

- **Status:** Adopted with the Stage 4 tracker
  [#759](https://github.com/MGYamada/Vastitas/issues/759), in pull request
  [#760](https://github.com/MGYamada/Vastitas/pull/760), which added this
  chapter.
- **Date:** 2026-11-13; amended on 2026-11-16 (§4 and §5) for the Stage 6
  tracker [#841](https://github.com/MGYamada/Vastitas/issues/841).
- **Scope:** the admission of `nature::dimension` for one finite profile, and
  the dependency rule between `std` and `nature` that it needs. It is **not** a
  claim of implemented or proved functionality.
- **Decision issues:** [#300](https://github.com/MGYamada/Vastitas/issues/300)
  (`nature::dimension`) and [#304](https://github.com/MGYamada/Vastitas/issues/304)
  (the responsibilities of `std`, `monad` and `nature`).
- **Relation to ADR 0001.** [ADR 0001](0001-mathematics-first-stdlib.md)
  governs the admission of `std`; its §1 names `nature` as the owner of
  physical interpretations. This record follows ADR 0001 §8 for the parts of
  an admission and adds the test that a `nature` module must pass. The
  proposal of a five-role architecture in pull request
  [#370](https://github.com/MGYamada/Vastitas/pull/370) is not adopted or
  required by this record.

## Context

Historical Stage 4 asks the compiler to reject `dx² + dt²` on a chart whose
coordinate `x` is a length and whose coordinate `t` is a time, and to accept
the sum when a declared metric uses compatible scales. That `x` is a length is
a statement about the physical world, not about `ℝ²`: the smooth affine object
and its metrics of ADR 0001 §10 are the same whether `x` measures a length, a
time or nothing. The maintainer decided that the physical part belongs to
`nature::dimension` and that the boundary with `std` is recorded first.

## Decision

### 1. Responsibility boundary

1. **`std`** owns mathematical objects, maps, laws and exact operations. It
   MUST NOT import `nature` or `monad`, and its validity MUST NOT depend on a
   `nature` declaration.
2. **`nature`** owns physical interpretations: declared identifications,
   conventions, hypotheses and provenance that give a `std` object its meaning
   in the world. It MAY import `std`. It owns no mathematical denotation: it
   MUST NOT define a map, a law or an algorithm that a `std` object lacks.
3. **`monad`** owns computational policies and effects. `nature` and `monad`
   do not import each other.
4. A *dimension* in this record is a physical dimension, such as length or
   time. It is not the dimension of a vector space or of a manifold.

### 2. Admission test for a `nature` module

A `nature` module MUST document the five parts of ADR 0001 §8, with this test
in place of A–D:

- **World identification.** The module's declarations state an
  identification, convention or hypothesis about the physical world, with an
  identity of its own. A mathematical tool that physicists use does not
  qualify; it belongs to `std`.
- **No competing mathematics.** Every value and law that the module uses is
  that of a `std` object. A check that the module adds is a consistency check
  of the interpretation, not a mathematical result.
- **Separate claims.** A mathematical proof does not establish a physical
  identification, and a passing dimension check does not establish a physical
  law.

### 3. `nature::dimension` (finite profile)

#### Terms

- A *base dimension* is a declared nominal generator, such as length `L` or
  time `T`. The base dimensions of a program generate the dimension group
  `D ≅ ℤᵏ`. A *dimension* is an element of `D`, written as a product of base
  dimensions with integer exponents.
- A *quantity kind* is a declared nominal kind with a dimension, such as
  `Length` with dimension `L`. Two kinds with the same dimension are different
  kinds: `Wavelength` is not `Length`, and `Torque` is not `Energy`.
- A *reading* of a smooth affine object `X` assigns a quantity kind to each
  coordinate of `X`. It is the physical interpretation of the chart.
- A *scale* is a positive rational magnitude of a quantity kind, in the unit of
  the coordinates of that kind.
- A *physical interpretation of a metric* names a `std` metric `G` of `X`, a
  reading of `X`, and the entries of `G` written as rationals times products of
  scales with integer exponents.

#### Contract and jurisdiction

- **Declarations.** Base dimensions, quantity kinds, readings and scales are
  declarations. Each declaration introduces one identity.
- **Readings.** A reading names each coordinate of its object exactly once.
  It changes nothing about the object, its maps or its metrics.
- **Physical interpretation of a metric.**
  - The entries, evaluated with the magnitudes of their scales, MUST equal the
    Gram matrix of the named metric exactly.
  - Under the reading, the term `g_ij dxⁱ dxʲ` has the dimension of `g_ij`
    times the dimensions of `xⁱ` and `xʲ`. Every term with a nonzero entry MUST
    have the same dimension, the *value* of the metric. A declared value MUST
    equal it.
  - `normalized(x₁: s₁, …)` denotes `Σ dxᵢ² / sᵢ²`. Each scale MUST have the
    kind of its coordinate exactly; equal dimensions are not enough.
  - The interpretation of the Euclidean metric on a chart with a length
    coordinate and a time coordinate is rejected: `dx²` has dimension `L²` and
    `dt²` has dimension `T²`.
- **Independence of `std`.** A `nature` declaration never changes the validity
  or the generated code of a `std` declaration or of any binding, except
  through program-wide limits (such as the number of declarations) and name
  clashes. The `std` metric stays valid mathematics whatever reading a
  program declares.
- **Split between Core, `std` and `nature`.** The exponent arithmetic is a
  declaration rule of the executable kernel, like the check of metric
  evidence. It is not a domain checker and not a `std` module. `nature`
  declares the families `Reading<X>` and `PhysicalMetric<X>` over `std` smooth
  affine objects.

#### Laws

- The dimension of a product of scales is the sum of their dimensions, each
  multiplied by its exponent.
- The value of an interpreted metric does not depend on the order of its
  terms, and a zero entry constrains nothing.
- Changing the magnitude of a scale changes the Gram matrix that the
  interpretation denotes, and therefore the gradient (ADR 0001 §10). The
  dependence of the gradient on units is explicit.

#### Admission argument

- **World identification.** That `x` is a length, that `t` is a time and that
  `ℓ₀` is a length of magnitude 3 in the unit of `x` are physical conventions
  with identities. No theorem proves them.
- **No competing mathematics.** The metric, its evidence, `flat` and `sharp`
  are those of `std::geometry::metric`. The interpretation adds a consistency
  check and computes no value that a program uses.
- **Separate claims.** The check is syntactic dimension checking, the first of
  the three levels that #300 distinguishes. Dimensionless invariants and
  physical laws are outside this admission.

#### Execution and evidence profile

- **Executable profile.** Integer exponents; positive rational magnitudes;
  smooth affine objects of dimension at most 16; the bounds that the limits
  appendix lists for the declarations.
- **Wire.** Protocol 9 only. Protocols 7 and 8 are an error (`E_PROTOCOL`).
- **Evidence.** The executable kernel checks every interpretation again in its
  audit. The oracle must prove that an accepted interpretation is consistent
  and that `nature` declarations change no `std` validity and no binding.
- **Trust.** Native tests are evidence, not proofs.

#### Outside this admission

- Unit systems and conversions between units, such as 100 cm = 1 m.
- Rational exponents, quotients of the dimension group and natural units such
  as `c = ħ = 1`.
- Buckingham π invariants and dimensionless combinations.
- Affine readings such as Celsius temperatures.
- Quantities as values: dimensions of vectors, covectors, frame arrays and
  gradients.
- Angle kinds and the dimensionless arguments of transcendental functions.
- `nature::errorbar`, `nature::symmetry` and the facades of #304.

#### Negative tests

The Stage 4 profile must reject each of the following with its own diagnostic.
The Stage 4 acceptance map records the test that runs each case; a case
without a test there remains proposed.

- **Declarations:** a rational exponent; an exponent past its bound; a reading
  that misses or repeats a coordinate; a reading of an object that is not a
  smooth affine object; a scale that is not positive.
- **Interpretations:** the Euclidean metric under a reading with a length and
  a time coordinate; an entry whose magnitude differs from the metric; a scale
  of the wrong dimension; a declared value that differs from the inferred one;
  `normalized` with a scale of the right dimension and the wrong kind; an
  interpretation of a metric of another object (`E_DIMENSION`).
- **Boundary:** a `std` manifest that depends on a package outside `stdlib/`.
- **Inputs and transport:** protocols 7 and 8, and tampered Core.

#### Compatibility and public-name audit

- **Names.** `base_dimension`, `quantity`, `Reading`, `scale … of …`,
  `PhysicalMetric`, `interpret` and `normalized`; the diagnostic code
  `E_DIMENSION`. The declaration is not named `dimension`, which was a Stage 1
  primitive and capability that counts coordinates. (14 November 2026: #778
  renamed that operation and capability `dim`; `dimension` is an ordinary name,
  and `nature::dimension` the module of this record.)
- **Package.** `vastitas_nature` at `nature/` in the repository, whose root
  `nature/lib.vast` re-exports the package `vastitas_dimension` of
  `nature/src/dimension/` as `nature::dimension`. It depends on
  the standard library; no standard-library manifest depends on a path
  outside `stdlib/`, and `scripts/check_boundaries.py` checks it.
- **Versions and migration.** The profile adds no wire protocol version.
  Existing programs keep their meaning.

### 4. `nature::model` (amendment, 2026-11-16)

This amendment admits the module `nature::model` for the finite profile of
historical Stage 6, through the test of §2. It does not claim that the
contract is implemented or proved.

#### Terms

- A *convention* is a declared statement of how physical quantities are
  written, with an identity of its own. The profile admits one: `hbar_one`,
  which writes energies as angular frequencies.
- A *model* names a `std` endomorphism field `H` on a smooth affine object
  `X` (ADR 0001 §12), a reading of `X` (§3), a convention, a prepared basis
  vector and an observed basis vector of the free module of `H`, the
  transition average that it predicts (ADR 0001 §13), and its regime.
- The *regime* is a recorded text, such as the rotating-wave approximation
  and a drive far below the transition frequency. It is an assumption.

#### Contract and jurisdiction

- **Declarations.** Conventions and models are declarations; each introduces
  one identity.
- **Checks.** The executable kernel checks that the reading is a reading of
  the object of `H`, that both basis vectors belong to the module of `H`, and
  that the predicted average is the average of a branch of `H` from the
  prepared to the observed vector. A failed check is `E_MODEL`.
- **No values.** A model and a convention compute nothing. They change no
  value, no validity and no generated code of a `std` declaration.
- **Package.** `vastitas_model`, a package of its own under `nature/src/`,
  re-exported as `nature::model` by `nature/lib.vast`, as §3 does for
  `nature::dimension`.
- **Versions and migration.** The profile adds no wire protocol version.

#### Laws

- Removing a model or a convention leaves every `std` declaration and every
  value of the program unchanged.

#### Admission argument

- **World identification.** That `H` describes a two-level atom driven near
  resonance, that the atom is prepared in the vector `g`, that the population
  of `e` is observed and that the rotating-wave approximation holds are
  statements about the world. No theorem proves them.
- **No competing mathematics.** The field, its spectrum and its average are
  `std` objects; the model only names them.
- **Separate claims.** A checked model establishes that its references fit
  together, not that the model describes an experiment.

#### Execution and evidence profile

- The profile of historical Stage 6, protocol 9 only. The acceptance map
  records the regime with the status Assumed.

#### Outside this admission

- Conventions other than `hbar_one`, and natural units as a quotient of the
  dimension group (§3).
- Mixed states, time-dependent preparations and measurements other than the
  population of a basis vector.

#### Negative tests

- A reading of another object; a basis vector of another module; a predicted
  average of another field or between other vectors; protocols 7 and 8.

#### Compatibility and public-name audit

- **Names.** The declaration kind `convention` with its one value
  `hbar_one`, which has no family, the family `Model`, and
  `model(hamiltonian =, reading =, convention =, prepare =, observe =,
  predicts =, regime = assume(…))`. The code is `E_MODEL`. The names are
  provisional until the module is delivered.

### 5. `nature::errorbar` (amendment, 2026-11-16)

This amendment admits the module `nature::errorbar` for the finite profile of
historical Stage 6, through the test of §2. It does not claim that the
contract is implemented or proved.

#### Terms

- A *measured value* is a rational value with a positive rational standard
  uncertainty.
- A *calibration* of a model gives measured values to some of its
  parameters, with the method of evaluation (type A or type B in the sense of
  the guide to the expression of uncertainty in measurement), a reference and
  a revision. Its *fingerprint* is the kernel's digest of its canonical
  content.
- A *dataset* of a model under a calibration is a list of points: values of
  the remaining parameters and a measured value of the observable, with one
  coverage factor `k`.
- A *comparison* records a dataset, the fingerprint of its calibration, and a
  verdict: consistent or inconsistent.

#### Contract and jurisdiction

- **Verdict.** Every point, with the calibrated parameter values, lies on the
  chart of the predicted average (ADR 0001 §13). The executable kernel
  evaluates the prediction of the model exactly at each point, and the
  derivative of the prediction in each calibrated parameter. A point is
  consistent when `(prediction − value)² ≤ k²·(u² + Σ (∂prediction)²·u_c²)`,
  with `u` the uncertainty of the point and `u_c` those of the calibration.
  The verdict is consistent when every point is. A wrong recorded verdict is
  `E_ERRORBAR`.
- **Staleness.** A comparison whose recorded fingerprint differs from the
  fingerprint of its calibration is `E_STALE`; the diagnostic names the
  current fingerprint, so that the comparison can be recorded again after a
  review. `std` declarations and the model stay accepted.
- **Assumptions.** The propagation is first order, and the uncertainties of
  the points and of the calibration are uncorrelated. Both are recorded as
  assumptions of the comparison.
- **No values.** Calibrations, datasets and comparisons change no value, no
  validity and no generated code of a `std` declaration.
- **Package.** `vastitas_errorbar`, a package of its own under `nature/src/`,
  re-exported as `nature::errorbar` by `nature/lib.vast`.
- **Versions and migration.** The profile adds no wire protocol version.

#### Laws

- The verdict depends only on the model's prediction, the dataset and the
  calibration; changing the calibration changes the fingerprint, unless the
  64-bit digest collides.
- Removing a calibration, a dataset or a comparison leaves every `std`
  declaration and every value unchanged.

#### Admission argument

- **World identification.** That a value was measured, with that uncertainty,
  method and revision, is a statement about the world and its provenance.
- **No competing mathematics.** The prediction and its derivatives are those
  of the `std` average; the comparison adds an exact inequality of rationals.
- **Separate claims.** A consistent verdict states that the data do not
  contradict the model at the stated coverage under the recorded
  assumptions. It is not a proof of the model, and the uncertainty of a
  measurement is not the error bound of a numerical method.

#### Execution and evidence profile

- The profile of historical Stage 6, protocol 9 only, with at most 64 points
  and the digit limits of exact algebraic literals.

#### Outside this admission

- Correlated uncertainties, covariance matrices, global statistics such as
  χ² tests, and propagation beyond first order.
- Numerical error bounds of solvers, which belong to the planned computational
  library family `monad`.
- Datasets read from files.

#### Negative tests

- A changed calibration under an old comparison (`E_STALE`); a wrong verdict;
  a point off the chart of the predicted average (ADR 0001 §13), even where
  the denominator of its closed form does not vanish; a nonpositive uncertainty or
  coverage factor; a calibration of a parameter that the model does not
  have (`E_ERRORBAR`); more points than the limit (`E_LIMIT`); protocols 7
  and 8.

#### Compatibility and public-name audit

- **Names.** `Calibration`, `calibrate(…, method =, reference =, revision =)`,
  `measured(v, u =)`, `Dataset`, `measure(model =, calibration =, coverage =,
  points = […])`, `Comparison`, `compare(D, calibration = K, fingerprint =
  "…", verdict = …)`. The codes are `E_ERRORBAR` and `E_STALE`. The names
  are provisional until the module is delivered.
- **Other meanings.** `errorbar` is physical uncertainty. It never means the
  rounding error or the enclosure of a numerical algorithm.

## History

This record was written for the Stage 4 tracker
[#759](https://github.com/MGYamada/Vastitas/issues/759) on 2026-11-13, after
the maintainer chose to build `nature::dimension` before the metric check that
uses it. Its references are:

- **Ownership.** [#300](https://github.com/MGYamada/Vastitas/issues/300) keeps
  the full `nature::dimension` design: unit systems, quantity kinds beyond
  this profile, Buckingham π and natural units.
  [#304](https://github.com/MGYamada/Vastitas/issues/304) keeps the
  responsibilities of the three library families and the facades.
- **Related records.** The retired design draft at `cc4922f` stated the
  example of `dx² + dt²` in its sections on differentials and gradients and
  in its acceptance examples.
- **Architecture.** Pull request
  [#370](https://github.com/MGYamada/Vastitas/pull/370) proposes a five-role
  amendment of ADR 0001; it stays the maintainer's decision.

The amendments of 2026-11-16, §4 and §5, were written for the Stage 6 tracker
[#841](https://github.com/MGYamada/Vastitas/issues/841), after the
maintainer chose exact predictions and data without a numerical solver, a
recorded comparison that goes stale, and the two packages `nature::model` and
`nature::errorbar`. Their references are
[#299](https://github.com/MGYamada/Vastitas/issues/299) (`nature::errorbar`),
[#374](https://github.com/MGYamada/Vastitas/issues/374) (physics
conventions) and [#304](https://github.com/MGYamada/Vastitas/issues/304)
(library roles); the named solver and its numerical error bound stay with
[#318](https://github.com/MGYamada/Vastitas/issues/318).
