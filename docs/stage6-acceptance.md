# Stage 6 physical model acceptance

This map links each acceptance condition of historical Stage 6 to its
implementation, positive and negative tests, oracle and bridge theorems, and
native evidence. Stage 6 is a finite, checked profile of one physical model
over QQ: a two-level Hamiltonian from its assumptions to a comparison with a
calibrated dataset, on top of `nature::dimension` (Stage 4) and
`std::linalg::spectral` (Stage 5)
([tracker #841](https://github.com/MGYamada/Vastitas/issues/841)). It does not
include performance (#222), and it does not include the named solver and the
numerical error bound of the roadmap's acceptance example, which stay Planned
with #318.

[ADR 0001 §13](adr/0001-mathematics-first-stdlib.md#13-dephased-transition-averages-of-simple-branch-spectra-amendment-2026-11-16)
admits the dephased transition average, and
[ADR 0002 §4 and §5](adr/0002-nature-dimension.md#4-naturemodel-amendment-2026-11-16)
admit `nature::model` and `nature::errorbar`. The Reference chapters are
[Physical models](language/physical-models.md) and
[Transition averages](language/spectral-observations.md#transition-averages),
the guide chapter is [A physical model and its data](guide/physical-models.md),
and [Verification boundaries](verification.md#physical-models) states the
proof boundary. The specifications of
[`nature::model` and `nature::errorbar`](spec/nature-physical-model.md) and
[`std::linalg::spectral`](spec/std-linalg-spectral.md#spectral.transition-average)
record the claims.

Conditions C1–C13 and C16 have their tested evidence below. The oracle and
bridge theorems of C14 and C15 are Planned, and so are the claims that cite
them; the rows say what each is to state. C17 stays Planned with #318, and
C18 and C19 are Planned until continuous integration and the independent
whole-stage review run.

## Scope and decisions

The conditions are the checklist C1–C19 of #841, which turns the Stage 6
example of the [historical roadmap](guide/historical-roadmap.md#stage-6-a-first-physical-model)
into executable checks.

Decisions taken with the user (16 November 2026):

1. Scope "exact prediction and data". No `monad` package in this stage; the
   named solver and the numerical error bound stay Planned with #318.
2. Staleness is a recorded comparison: the kernel recomputes its verdict and
   rejects a comparison whose calibration changed (`E_STALE`), while the
   `std` declarations still check.
3. The model and the data live in two `nature` packages, `nature::model` and
   `nature::errorbar`; the average lives in `std::linalg::spectral`.
4. The wire work of #533 advances in stages alongside this stage.

### Roadmap sentences

| Roadmap sentence | Conditions |
| --- | --- |
| Declare what the parameters mean, their units, the state preparation, the observable and the regime | C1, C4, C5 |
| Record the model's exact prediction | C2, C3 |
| The result obtained under a named solver and approximation policy | C17 (Planned, #318) |
| A comparison against a calibrated dataset with stated uncertainty | C6, C7, C8 |
| Change the calibration. The comparison depending on it becomes stale | C9 |
| A mathematical derivation whose assumptions are unchanged can still be checked | C9, C10 |
| The numerical error bound and physical measurement uncertainty each need their own evidence | C8, C17 |

### Steps

| Step | Pull request | Merge |
| --- | --- | --- |
| S0: the tracker, ADR 0001 §13, ADR 0002 §4 and §5, the skeleton of this map, the status of the roadmap | [#842](https://github.com/MGYamada/Vastitas/pull/842) | `7187ddd` |
| Batch 2: the skeleton of every Stage 6 form; the kernel checks, the runtime of `average_at` and the regressions; the Rust parser and wire; round 1 of #533 merged in | [#854](https://github.com/MGYamada/Vastitas/pull/854) | `52a0297` |
| Batch 3: the acceptance program and its rejected packages, the specifications, the library pages and the book | This change | — |
| O+B: the oracle and bridge theorems of [C14](#c14) and [C15](#c15) | — | — |

### Status terms

- **Proved (oracle)** is a theorem in `lean/VastitasOracle/`, mathlib-free,
  about the kernel's definitions.
- **Proved (bridge)** is a mathlib theorem in `lean-bridge/`.
- **Tested** is a regression or integration test, including native execution.
- **Assumed** is a physical assumption or a trusted component, listed under
  [proof boundary](#proof-boundary).
- **Not claimed** is outside this profile.
- **Planned** has no evidence yet.

## Evidence key

Kernel files are in `lean-kernel/VastitasKernel/`, and kernel regressions run
from `scripts/check_kernel_regressions.sh`. The examples of the Reference and
guide chapters are tested evidence too: `tests/examples.rs` builds and runs
`examples/packages/two-level/` (`book_programs_print_their_output`: it shows
five predictions and exits with status 0) and checks the six rejected
packages `examples/reject/packages/two-level-*` against their `.stderr` files
(`book_rejected_packages_print_their_diagnostics`). The rows below cite them
as "book reject".

| Key | Implementation | Tests | Theorems |
| --- | --- | --- | --- |
| **A — averages** | `SpectralDeclarations.lean` (`averageIntegrand`, `traceForm`, `averageTrace`, `unitBound`, `unitCertificate`, `averageCertificate`, `checkAverage`, `checkTransitionAverage`), `IndexedSpectralSource.lean` (`elaborateAverages`), `Indexed.lean` (`transitionAverageData?`) | `AverageRegression`; `tests/physical_models.rs` | Planned ([C14](#c14), [C15](#c15)) |
| **O — observation** | `SpectralRuntime.lean` (`averageAt`), `IndexedPrimitiveBinding.lean` (`PrimitiveBinding.averageAt`, `AverageRef`), `IndexedSpectralContracts.lean`, `IndexedSpectralRegistry.lean`, `IndexedPrimitiveFamilies.lean` (`average_at`) | `AverageRegression`; `tests/emit_golden.rs` (the package `spectral-primitives`); the native fixture `spectral_average_programs` of `scripts/check_indexed_native.sh` | Planned ([C14](#c14)) |
| **M — models** | `NatureModel.lean` (`checkConvention`, `checkModel`, `predictsAverage`), `IndexedModelSource.lean` (`elaborateModels`) | `NatureModelRegression`; `ModelDeclarationRegression` | Planned ([C14](#c14)) |
| **E — errorbar** | `NatureErrorbar.lean` (`checkCalibration`, `canonicalContent`, `calibrationFingerprint`, `checkDataset`, `verdict?`, `checkComparison`), `IndexedErrorbarSource.lean` (`elaborateErrorbars`), `Limits.lean` (`datasetPoints`, `recordTextBytes`) | `NatureModelRegression`; `tests/two_level.rs` | Planned ([C14](#c14)) |
| **V — wire** | `IndexedDeclarationProtocol.lean` (`declarationBody`, `recordText`, `Feature.physicalModels` and `admits`), `src/frontend/indexed_parser.rs`, `src/indexed.rs` | `ModelDeclarationRegression`; `tests/physical_models.rs`; the unit tests of the parser and `every_stage6_form_serializes_to_its_wire_shape` (`src/indexed.rs`) | Tested only |
| **L — libraries** | `stdlib/src/linalg/spectral/mod.vast` (`TransitionAverage`), `nature/src/model/` and `nature/src/errorbar/` (`Model`, `Calibration`, `Dataset`, `Comparison`), `nature/lib.vast` | `tests/nature_dimension.rs` (`model_and_errorbar_modules_export_exactly_their_families`); `tests/physical_models.rs` (`the_model_uses_the_families_of_the_libraries`); `scripts/library_docs.py`; `scripts/check_boundaries.py` | — |
| **X — acceptance program** | `examples/packages/two-level/` and the six rejected packages | `tests/two_level.rs`; `tests/examples.rs` | — |

<a id="acceptance-conditions"></a>

## Acceptance conditions

The acceptance program declares, on the chart `P = Affine(2)[delta, omega]`
read as two frequencies, H = (δ/2)σ_z + (Ω/2)σ_x on V = basis(g, e), its
spectrum S, the branch B = simple(S, localize = δ² + Ω², witness = 2t,
exponent = 1) and the transition average A from g to e with the closed form
`ratio(frac(1, 2) * omega^2, delta^2 + omega^2)`; the convention `hbar_one`
and the model M; the calibration K of Ω = 5/2 ± 1/20 (`type_b`), whose
fingerprint is `fnv1a64:fd1f7edd812db49f`; the dataset D of five points at
δ = 0, 1, 2, −1 and 5/2 with the coverage factor 2; and the comparison C with
the verdict `consistent`. It shows `avg(at(0, 5)) = (1, 2)`,
`avg(at(2, 5)) = (25, 58)`, `avg(at(4, 5)) = (25, 82)`,
`avg(at(-2, 5)) = (25, 58)` and `avg(at(5, 5)) = (1, 4)`, the prediction
25/(8δ² + 50) at each point, and exits with status 0.

| Condition | Status and evidence |
| --- | --- |
| <a id="c1"></a>C1. Two-level field: chart, reading, symmetric H, spectrum and branch | **Tested** (X): the acceptance program declares the chart, the quantity `Frequency = T^-1` and the reading `(delta: Frequency, omega: Frequency)`, H declared `symmetric`, its spectrum and the branch on D(δ² + Ω²) with the witness 2t; it checks, builds and runs (`the_acceptance_program_checks_builds_and_shows_the_exact_predictions` in `tests/two_level.rs`; `book_programs_print_their_output`). The symmetry, the spectral pair and the gap witness are the checks of the spectral profile, with the evidence of the [Stage 5 map](stage5-acceptance.md); the reading is a reading of `nature::dimension`, with that of the [Stage 4 map](stage4-acceptance.md) |
| <a id="c2"></a>C2. Transition average: closed form checked against the trace form | **Tested** (A, V): `AverageRegression` ("the two-level average: g to e, ω²/2 over δ² + ω², T = ω²(δ² + ω²)/2, D·1 = g", "the cancelled average: u1 to u2, 1/2 over 1, T = x⁴/2, D·1 = g⁰", "a wrong closed form is rejected, naming the residual", "a denominator that is not a unit on D(g) is rejected, although N·g^(2e) = D·T", "a field that is not declared symmetric is rejected", "a basis vector of another module is rejected", "a zero denominator is rejected", "a branch of another object, or no branch, is rejected", "a tampered closed form, trace, unit certificate or basis index is rejected", "the swapped direction of a symmetric field gives the same average and is accepted"); book reject `two-level-wrong-average`; a forged numerator is `E_SPECTRAL` (`forged_stage6_records_are_rejected_by_the_kernel` in `tests/physical_models.rs`); no certificate or trace on the wire (`ModelDeclarationRegression`). **Proved**: Planned ([C14](#c14), [C15](#c15)) |
| <a id="c3"></a>C3. Observation of the average at rational points | **Tested** (O, X): `AverageRegression` ("the runtime gives N(p)/D(p) on the chart and (0, 0) off it", "average_at embeds the average, its branch and its closed form", "a point of another object is rejected", "average_at erases to its runtime evaluator, on and off the chart", "average_at lowers to the spectral runtime and imports it", "average_at has no derivative rule"); the emit corpus `spectral-primitives` reads 8/25 at (3, 4), 0 at (1, 0) and `(0, 0)` at the origin (`tests/emit_golden.rs`); the native fixture `spectral_average_programs` exits with 42; the acceptance program shows the five predictions, and each changed expected value makes it exit with status 1 (`each_mutation_of_an_expected_value_or_the_verdict_is_caught`). **Proved**: Planned ([C14](#c14)) |
| <a id="c4"></a>C4. Model: references checked, regime recorded | **Tested** (M): `NatureModelRegression` ("the model records its references, the basis indices and the regime", "a reading of another object is E_MODEL", "a basis vector of another module is E_MODEL", "a predicted average of another field is E_MODEL", "a predicted average between other vectors is E_MODEL", "a predicted average of another object, or no average, is E_MODEL", "a convention that is no convention, and a field that is no endomorphism, are E_MODEL", "a model at another family is E_MODEL"); book rejects `two-level-other-basis` and `two-level-other-reading`; a forged prepared vector is `E_MODEL` (`tests/physical_models.rs`). The regime is a recorded text, checked only for its characters and length. **Proved**: Planned ([C14](#c14)). **Assumed**: the regime and the meaning of the model ([proof boundary](#proof-boundary)) |
| <a id="c5"></a>C5. Convention `hbar_one` recorded, no value changed | **Tested** (M, V): `ModelDeclarationRegression` ("a convention, a method and a verdict are words of a closed list", "a convention names nothing, and the declaration audit accepts it alone"); another word is `E_TYPE` in the frontend (`stage6_syntax_errors_are_reported_at_their_place`); a package with a convention alone is sent as protocol 9 (`the_stage6_forms_select_protocol_nine_and_serialize_to_their_records`); the program without its `nature` declarations, the convention included, generates byte-identical code (`a_changed_calibration_is_stale_and_changes_no_std_code`). **Proved**: Planned ([C14](#c14)) |
| <a id="c6"></a>C6. Calibration with uncertainty, method, reference, revision and fingerprint | **Tested** (E, V): `NatureModelRegression` ("the calibration records omega = 5/2 ± 1/20 as coordinate 1", "a fingerprint is fnv1a64: and 16 lowercase hexadecimal digits", "the fingerprint changes with each part of the content", "the fingerprint does not depend on the order of the calibrated coordinates", "the canonical content writes reduced rationals and length-prefixed texts", "a nonpositive uncertainty is E_ERRORBAR", "a calibration of a coordinate that the model's object does not have is E_ERRORBAR"); another method is `E_TYPE` and a reference or revision that is no recorded text is `E_PARSE` (the unit tests of the parser); the acceptance program's calibration and fingerprint. **Proved**: Planned ([C14](#c14)) |
| <a id="c7"></a>C7. Dataset with points, uncertainties and a coverage factor | **Tested** (E): `NatureModelRegression` ("the dataset records k = 2 and its points", "a point gives exactly the coordinates that the calibration does not give", "a point off the chart of the prediction is E_ERRORBAR", "a point off the chart of the cancelled average is E_ERRORBAR, though 1/2 has no pole there", "a nonpositive coverage factor is E_ERRORBAR", "a dataset of another model's object or of no model is E_ERRORBAR", "a dataset without points is E_ERRORBAR"); book reject `two-level-off-chart`; a forged coverage factor 0 is `E_ERRORBAR` (`tests/physical_models.rs`) |
| <a id="c8"></a>C8. Comparison verdict recomputed exactly | **Tested** (E, X): `NatureModelRegression` ("a consistent dataset recorded as inconsistent is E_ERRORBAR", "an inconsistent point recorded as consistent is E_ERRORBAR, naming it", "an inconsistent dataset recorded as inconsistent is accepted", "the calibration's uncertainty counts: a wide one makes the point consistent", "the coverage factor counts: k = 10 makes the point consistent", "the exact test: A(p) = 25/58 and ∂A/∂Ω = 40/841, with no square root", "a comparison under another calibration than its dataset's is E_ERRORBAR"); book reject `two-level-wrong-verdict`; `a_wrong_verdict_is_rejected` (`tests/physical_models.rs`); in `tests/two_level.rs` the flipped verdict is `E_ERRORBAR`, and a measured value moved outside its interval makes `consistent` the error and `inconsistent` accepted. **Proved**: Planned ([C14](#c14)). **Assumed**: first-order propagation and uncorrelated uncertainties |
| <a id="c9"></a>C9. Staleness after a changed calibration; the derivation still checks | **Tested** (E, X): `NatureModelRegression` ("a changed calibration makes the recorded comparison E_STALE, naming the current fingerprint", "a changed revision alone makes the comparison stale too", "the staleness is reported before the verdict", "without the stale comparison the program is accepted, and its std declarations are unchanged", "the comparison recorded again with the current fingerprint is accepted", "a changed calibration under an unchanged comparison fails the audit (C9)"); end to end on the acceptance program, `a_changed_calibration_is_stale_and_changes_no_std_code` (`tests/two_level.rs`): the calibration at ± 1/25 is `E_STALE` naming the current fingerprint, the program without the comparison is accepted with byte-identical generated code, and the comparison recorded with the current fingerprint builds and shows the same predictions; `a_changed_calibration_makes_the_comparison_stale` (`tests/physical_models.rs`); book reject `two-level-stale`; a forged fingerprint is `E_STALE`. **Proved**: Planned ([C14](#c14)) |
| <a id="c10"></a>C10. Weakening: model and data change no `std` validity, value or code | **Tested** (M, E, X): `NatureModelRegression` ("the std declarations are those of the program without nature (C10)"); the acceptance program without its comparison, and without every declaration and import of `nature`, generates byte-identical Lean and shows the same predictions (`tests/two_level.rs`); the emitted Lean of `tests/physical_models.rs` is identical without the `nature` declarations. **Proved**: Planned ([C14](#c14)) |
| <a id="c11"></a>C11. Wire: protocol-9 optional fields, forged data rejected | **Tested** (V): `ModelDeclarationRegression` ("protocol 9 decodes each Stage 6 declaration shape", "protocols 7 and 8 reject each Stage 6 declaration with E_PROTOCOL", "the nature forms are the feature physicalModels, which only protocol 9 admits", "the transition average and average_at are the feature algebraic", "a Stage 6 declaration takes exactly its fields, and no certificate", "a recorded text has at most recordTextBytes bytes of printable ASCII without a backslash or a quote", "a forged recorded text is E_PROTOCOL"); `the_stage6_forms_select_protocol_nine_and_serialize_to_their_records` and `forged_stage6_records_are_rejected_by_the_kernel` (`tests/physical_models.rs`: a forged fingerprint, verdict, closed form, prepared vector, coverage factor or recorded text, and a certificate, a trace or an embedded declaration as an unknown field); the wire-shape unit tests of the parser and of `src/indexed.rs`; `scripts/check_wire_parity.sh` shows no divergence class beyond those of #533 round 1 |
| <a id="c12"></a>C12. Limits | **Tested** (E, V): `datasetPoints` = 64 is `E_LIMIT` in the frontend at the list of points and in the kernel before any point is read (`the_points_of_a_dataset_are_bounded`; "more points than datasetPoints is E_LIMIT, before any point is read"); `recordTextBytes` = 256 is `E_LIMIT` in the frontend and `E_PROTOCOL` on the wire (`stage6_syntax_errors_are_reported_at_their_place`, `forged_stage6_records_are_rejected_by_the_kernel`, `ModelDeclarationRegression`); the values of calibrations and datasets have the digit bound of polynomial literals ("the values of a calibration and a dataset have the digit bound of polynomial literals"); an average keeps `spectralRank`, `spectralPower` and the budgets of exact affine algebra. [Appendix D](appendix/limits.md#physical-models-and-data) lists the limits |
| <a id="c13"></a>C13. Libraries and pages | **Tested** (L): `std::linalg::spectral` declares `TransitionAverage`, and the packages `vastitas_model` and `vastitas_errorbar` of `nature`, re-exported as `nature::model` and `nature::errorbar`, declare `Model`, `Calibration`, `Dataset` and `Comparison` (`model_and_errorbar_modules_export_exactly_their_families`); an application takes the families from copies of the libraries (`the_model_uses_the_families_of_the_libraries`); `scripts/library_docs.py` checks the pages of the three modules, which show the declarations of the acceptance program, and `scripts/check_boundaries.py` the dependencies of the packages. The specifications [`nature::model` and `nature::errorbar`](spec/nature-physical-model.md) and [`spectral.transition-average`](spec/std-linalg-spectral.md#spectral.transition-average) record the claims |
| <a id="c14"></a>C14. Oracle theorems | **Planned** (O+B lane). The theorems are to state, about the kernel's definitions: that an accepted transition average satisfies N·g²ᵉ = D·T and D·Q = gᵐ, and that `average_at` gives N(p)/D(p) = T(p)/g(p)²ᵉ on the chart and the failure value off it; that an accepted model has valid references; that an accepted comparison records the fingerprint of its calibration and its verdict is `consistent` exactly when every point satisfies the inequality of [Comparisons](language/physical-models.md#comparisons); and that the declarations of `nature::model` and `nature::errorbar` weaken, changing no `std` validity, value or generated code. <!-- O+B: oracle theorem names --> |
| <a id="c15"></a>C15. Bridge theorem: the average is Σ_k (P_k)²_{eg} | **Planned** (O+B lane). The theorem is to state that for a real symmetric field with a simple spectrum, at a real point of D(g), the trace-form value of an accepted transition average equals Σₖ Pₖ[j, i]² with Mathlib's eigenprojectors. <!-- O+B: bridge theorem name --> |
| <a id="c16"></a>C16. Native acceptance program and rejected packages | **Tested** (X): `examples/packages/two-level/` checks, builds and runs natively, shows the five predictions and exits with status 0 (`book_programs_print_their_output`; `the_acceptance_program_checks_builds_and_shows_the_exact_predictions`); each of the five expected values changed makes it exit with status 1 with the same lines (`each_mutation_of_an_expected_value_or_the_verdict_is_caught`); the six book rejects give `E_STALE`, `E_SPECTRAL`, `E_ERRORBAR` twice and `E_MODEL` twice (`book_rejected_packages_print_their_diagnostics`); the native fixture `spectral_average_programs` |
| <a id="c17"></a>C17. Named solver and numerical error bound | Planned (#318). Not part of this stage |
| <a id="c18"></a>C18. Continuous integration | Planned |
| <a id="c19"></a>C19. Independent whole-stage review | Planned |

## Proof boundary

Assumed, by the contract of ADR 0002 §4 and §5, and listed in
[Verification boundaries](verification.md#assumed-in-physical-models):

- that the declared Hamiltonian, preparation, observable and regime describe
  the experiment;
- that the transition average is the long-time average of the transition
  probability under the dynamics of the Hamiltonian;
- first-order propagation of uncertainty, and uncorrelated uncertainties.

The oracle and bridge theorems of [C14](#c14) and [C15](#c15) are Planned.
Until they land, every claim about accepted averages, models and comparisons
rests on the kernel's checks and their tests, not on a theorem. The
fingerprint detects a changed calibration; it is a 64-bit FNV-1a digest and
authenticates nothing.

## Not claimed

- The named solver and the numerical error bound (#318).
- Time evolution and transcendental functions (#244).
- Hermitian fields over QQ(i) (#816).
- Correlated uncertainties and global statistics (#299).
- Physical dimensions of eigenvalues and ħ as a dimension (#776, #300).
- Datasets read from files (#802).

## Validation

Run on `claude/gallant-ellis-309ff2` at `a3b9949`, with the acceptance
program, the specifications and the pages of batch 3, through the lock of the
lanes:

- `cargo fmt --check`, `cargo clippy --locked --all-targets -- -D warnings`
  and `cargo test --locked --all-targets --no-fail-fast`: 789 passed, 0
  failed, 16 ignored (the tests that need the pinned OpenBLAS or a request of
  more than 1 GiB).
- `lake -d lean-kernel build`, `bash scripts/check_kernel_regressions.sh`,
  `bash scripts/check_indexed_native.sh` and
  `bash scripts/check_storage_native.sh`: passed.
- `lake -d lean build` and `lake -d lean env lean scripts/audit_axioms.lean`:
  passed, the audit of 52,621 declarations.
- `python3 scripts/check_spec.py`, `python3 scripts/check_docs.py`,
  `mdbook build`, `python3 scripts/check_book.py`,
  `python3 scripts/library_docs.py`, `python3 scripts/check_boundaries.py`,
  `python3 scripts/check_resource_cleanup.py` and
  `python3 -m unittest discover -s scripts -p 'test_*.py'` (1,136 tests):
  passed.
- `python3 scripts/check_grammar_derivations.py --compiler target/debug/vastitas`
  with the seeds 746, 1, 2 and 3, and `bash scripts/check_wire_parity.sh`, on
  batch 2: no derived text gives a parse diagnostic that no rule allows, and
  the parity reports equal those of #533 round 1.
- After the book of batch 3: `python3 scripts/check_docs.py`, `mdbook build`,
  `python3 scripts/check_book.py`, `python3 scripts/check_spec.py`,
  `python3 scripts/library_docs.py` and `cargo test --locked --test examples`
  (17 passed, 2 ignored for the pinned OpenBLAS): passed.
