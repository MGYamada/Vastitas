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
admit `nature::model` and `nature::errorbar`. Every condition below is
Planned until its step lands.

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
| S0: the tracker, ADR 0001 §13, ADR 0002 §4 and §5, the skeleton of this map, the status of the roadmap | This change | — |

### Status terms

- **Proved (oracle)** is a theorem in `lean/VastitasOracle/`, mathlib-free,
  about the kernel's definitions.
- **Proved (bridge)** is a mathlib theorem in `lean-bridge/`.
- **Tested** is a regression or integration test, including native execution.
- **Assumed** is a physical assumption or a trusted component, listed under
  [proof boundary](#proof-boundary).
- **Not claimed** is outside this profile.
- **Planned** has no evidence yet.

## Acceptance conditions

| Condition | Status | Evidence |
| --- | --- | --- |
| <a id="c1"></a>C1. Two-level field: chart, reading, symmetric H, spectrum and branch | Planned | — |
| <a id="c2"></a>C2. Transition average: closed form checked against the trace form | Planned | — |
| <a id="c3"></a>C3. Observation of the average at rational points | Planned | — |
| <a id="c4"></a>C4. Model: references checked, regime recorded | Planned | — |
| <a id="c5"></a>C5. Convention `hbar_one` recorded, no value changed | Planned | — |
| <a id="c6"></a>C6. Calibration with uncertainty, method, reference, revision and fingerprint | Planned | — |
| <a id="c7"></a>C7. Dataset with points, uncertainties and a coverage factor | Planned | — |
| <a id="c8"></a>C8. Comparison verdict recomputed exactly | Planned | — |
| <a id="c9"></a>C9. Staleness after a changed calibration; the derivation still checks | Planned | — |
| <a id="c10"></a>C10. Weakening: model and data change no `std` validity, value or code | Planned | — |
| <a id="c11"></a>C11. Wire: protocol-9 optional fields, forged data rejected | Planned | — |
| <a id="c12"></a>C12. Limits | Planned | — |
| <a id="c13"></a>C13. Libraries and pages | Planned | — |
| <a id="c14"></a>C14. Oracle theorems | Planned | — |
| <a id="c15"></a>C15. Bridge theorem: the average is Σ_k (P_k)²_{eg} | Planned | — |
| <a id="c16"></a>C16. Native acceptance program and rejected packages | Planned | — |
| <a id="c17"></a>C17. Named solver and numerical error bound | Planned (#318) | Not part of this stage |
| <a id="c18"></a>C18. Continuous integration | Planned | — |
| <a id="c19"></a>C19. Independent whole-stage review | Planned | — |

## Proof boundary

Assumed, by the contract of ADR 0002 §4 and §5:

- that the declared Hamiltonian, preparation, observable and regime describe
  the experiment;
- that the transition average is the long-time average of the transition
  probability under the dynamics of the Hamiltonian;
- first-order propagation of uncertainty, and uncorrelated uncertainties.

## Not claimed

- The named solver and the numerical error bound (#318).
- Time evolution and transcendental functions (#244).
- Hermitian fields over QQ(i) (#816).
- Correlated uncertainties and global statistics (#299).
- Physical dimensions of eigenvalues and ħ as a dimension (#776, #300).
- Datasets read from files (#802).

## Validation

Recorded when the conditions have evidence.
