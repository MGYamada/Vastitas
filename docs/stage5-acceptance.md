# Stage 5 spectral observations acceptance

This map links each acceptance condition of historical Stage 5 to its
implementation, positive and negative tests, oracle and bridge theorems, and
native evidence. Stage 5 is a finite, checked profile of exact spectral
observations of polynomial matrix fields over QQ, on top of the smooth affine
profile of Stage 3 and the polynomial matrices of Stage 4
([tracker #806](https://github.com/MGYamada/Vastitas/issues/806)). It does not
include performance: the Fast like C verdict stays with #222.

The Reference chapter is
[Spectral observations](language/spectral-observations.md), the guide
chapter is [Matrix fields and their spectra](guide/spectral-observations.md),
and [Verification boundaries](verification.md#spectral-observations) states
the theorems with their premises. The
[specification of `std::linalg::spectral`](spec/std-linalg-spectral.md)
records the claims of the module.

Conditions C1–C18 have their evidence below. C7 is Proved (bridge) for steps
1 and 2 of #471 and Planned for its agreement with emitted reverse Core,
which the bridge integration step of the stage states; so are the real-point
halves of C5 and C10. C19 (CI) and C20 (the independent whole-stage review)
stay Planned until the stage closes.

## Scope and decisions

The conditions are the checklist C1–C20 of #806, which turns the Stage 5
example of the [historical roadmap](guide/historical-roadmap.md#stage-5-spectral-observations)
into executable checks.

Decisions taken with the user (15 November 2026):

- **Core and branches.** The profile has polynomial matrix fields, the exact
  spectral pair, trace-power and characteristic-coefficient invariants with
  the gradients of Stage 3, and simple eigenvalue branches on a finite chart
  certified by a unit witness, with the branch differential and the
  eigenprojector. Numerical eigensolvers (#324) and the covers, image opens
  and cluster splits of #765 are outside it.
- **Daleckii–Krein.** The mathlib bridge proves steps 1 and 2 of #471, the
  typed Hermitian lift and the cotangent action with the pairing Re tr(KX),
  and that the emitted reverse Core of an accepted trace-power invariant
  computes the Daleckii–Krein cotangent composed with the derivative of the
  field. The C∞ comparison (#361), the general correspondence of #290 and
  pass preservation (#164) stay open.
- **Public home.** The vocabulary lives in `std::linalg::spectral`, as #337
  names it.

Design decisions of the plan that the user approved:

- **Field.** QQ only, as in Stages 3 and 4. Exact `Rat` stays inside the
  runtime.
- **Certificates.** The kernel computes the characteristic polynomial and the
  adjugate by the Faddeev–LeVerrier recursion and checks them by cofactor
  expansion. Every identity modulo χ is checked against a quotient that the
  kernel computes, so no theorem depends on a division routine. No
  certificate comes from the wire.
- **Fiber coordinate.** `eigen(H, t)` names the coordinate of the
  characteristic polynomial; it is the last variable of every polynomial in
  `A[t]`.
- **Symmetry.** `symmetric` is explicit and checked. It selects the pairing
  that the eigenprojector and the Daleckii–Krein statements use.
- **Invariants.** A trace power or a coefficient is an ordinary smooth map
  into the line. Its differential, its gradient and its compiled reverse pass
  are those of Stage 3.
- **Branches.** A branch observation takes the eigenvalue as an input. No
  primitive computes, orders or chooses an eigenvalue.

Approved provisional names: the families `FreeModule`, `Endomorphism`,
`Spectrum` and `Branch`; the declarations `free_module … = basis(…)`,
`endomorphism … = rows(…) of V [symmetric]`, `spectrum … = eigen(H, t)` and
`branch … = simple(S, localize = …, witness = …, exponent = …)`; the
morphisms `trace_power` and `char_coefficient`; the primitives `annihilates`,
`action_entry`, `on_branch`, `branch_differential` and `branch_projector`; the
code `E_SPECTRAL`; the limits `spectralRank` (4) and `spectralPower` (8).
[ADR 0001 §12](adr/0001-mathematics-first-stdlib.md#12-exact-spectral-pairs-and-simple-branches-of-polynomial-matrix-fields-amendment-2026-11-15)
admits the module.

### Roadmap sentences

| Roadmap sentence | How this profile meets it | Rows |
| --- | --- | --- |
| For an exact finite endomorphism H, retain its characteristic scheme and the module on which the coordinate acts as H | `eigen(H, t)` derives χ_H in `A[t]` and keeps H as the action of t; Σ_H is never replaced by a reduced or annihilator locus | C2, C3 |
| A scalar matrix and a nontrivial Jordan block can have the same characteristic polynomial and different module actions | 2I against the Jordan block with eigenvalue 2, and 0 against the nilpotent block: equal χ and invariants, different module observations | C3 |
| A numerical adapter must identify the observation it computes | No numerical adapter; every observation is exact and named. Numerical eigensolvers stay with #324 | — |
| For the symmetric matrix with rows (x, y) and (y, −x), the eigenvalues ±√(x² + y²) meet at the origin | The branch chart D(x² + y²) excludes the origin | C9 |
| tr(H²) = 2(x² + y²) has gradient (4x, 4y) everywhere for the declared dimensionless Euclidean chart | `trace_power(H, 2)` is a smooth map; its gradient through a Euclidean metric with a dimensionless reading is (4x, 4y) | C4, C5 |
| A cluster derivative additionally needs a gap to the rest of the spectrum | A branch needs a checked unit witness on D(g); its observations read ⊥ off the chart | C8–C11 |
| The typed Hermitian lift, cotangent action and agreement with emitted reverse Core remain open | Steps 1 and 2 of #471, and the agreement for trace powers | C7 |

### Steps

| Step | Pull request | Merge |
| --- | --- | --- |
| S0: the tracker, ADR 0001 §12, the skeleton of this map, the status of the roadmap | [#807](https://github.com/MGYamada/Vastitas/pull/807) | `0a2b83c` |
| S1: the shared skeleton: every spectral form exists and is rejected until it is implemented | [#809](https://github.com/MGYamada/Vastitas/pull/809), with batch 2 | `317fd2b` |
| B-prereq: the Daleckii–Krein steps 1 and 2 and the algebra prerequisites in the bridge | [#809](https://github.com/MGYamada/Vastitas/pull/809), with batch 2 | `317fd2b` |
| Batch 2: spectral declarations, certificates and runtime; the Rust parser; the reference fixture | [#809](https://github.com/MGYamada/Vastitas/pull/809) | `317fd2b` |
| Batch 3: primitives, code generation and native code; oracle soundness of the checks; the bridge algebra | [#810](https://github.com/MGYamada/Vastitas/pull/810), open | — |
| Batch 4: oracle acceptance, bridge integration, `std::linalg::spectral`, the acceptance program, the book | Planned | — |
| Review: the independent whole-stage review | Planned | — |

### Status terms

- **Proved (oracle)** is a theorem about kernel data and runtime definitions in
  `lean/VastitasOracle/`, mathlib-free, about the checker that accepts the
  input.
- **Proved (bridge)** is a mathlib theorem in `lean-bridge/`.
- **Tested** is a regression or integration test, including native execution.
  Testing is not a proof of all inputs.
- **Assumed** is a trusted component listed under
  [proof boundary](#proof-boundary).
- **Not claimed** is outside this profile; the
  [not-claimed list](#not-claimed) records it.
- **Planned** has no evidence yet.

## Evidence key

Kernel files are in `lean-kernel/VastitasKernel/`, and kernel regressions run
from `scripts/check_kernel_regressions.sh`. Oracle files are in
`lean/VastitasOracle/`, and bridge files in `lean-bridge/VastitasBridge/`.
The examples of the Reference and guide chapters are tested evidence too:
`tests/examples.rs` builds and runs `examples/packages/spectral-observations/`
(`book_programs_print_their_output`, it prints `42`), and checks the six
rejected packages `examples/reject/packages/spectral-*` against their
`.stderr` files (`book_rejected_packages_print_their_diagnostics`). The rows
below cite them as "book reject".

| Key | Implementation | Tests | Theorems |
| --- | --- | --- | --- |
| **D — declarations** | `SpectralDeclarations.lean` (`checkModule`, `checkRows`, `checkCertificate`, `checkWitness`, the producer `faddeevLeVerrier` and `certify`, `witnessQuotient`, `tracePowerImage`, `charCoefficientImage`, and the declaration checks `checkFreeModule`, `checkEndomorphism`, `checkSpectrum`, `checkBranch`), `IndexedSpectralSource.lean` (`elaborateSpectral`), `IndexedValidity.lean` (`Entry.Valid` calls the four checks), `Indexed.lean` (`freeModuleData?`, `endomorphismData?`, `spectrumData?`, `branchData?`), `Limits.lean` (`spectralRank`, `spectralPower`) | `SpectralDeclarationRegression`; `tests/spectral_declarations.rs`; `tests/spectral_limits.rs`; `src/frontend/indexed_parser.rs` and `src/indexed.rs` (`every_spectral_form_serializes_to_its_wire_shape_and_is_algebraic`) | Oracle `SpectralAlgebra`, `SpectralDeclarations`; bridge `Spectral/Algebra.lean` (`toMv_charPoly`, `toMv_tracePower`, `toMv_tCoefficient`, `charPoly_eval_real`, `branch_mem_spectrum`, `unit_witness_localization`), `Spectral/Prerequisites.lean` (`laplace_det_eq`, `charpoly_eval₂`) |
| **R — runtime** | `SpectralRuntime.lean` (`evalMatrixPoly`, `annihilates`, `actionEntry`, `onBranch`, `slopeAt`, `branchDifferential`, `projectorMatrix`, `projectorEntry`) on `FrameRuntime` and `SmoothRuntime` | `SpectralRuntimeRegression` | Oracle `SpectralRuntime` |
| **P — primitives** | `IndexedPrimitiveBinding.lean` (the six constructors, `EndoRef`, `SpectrumRef`, `BranchRef`, `SpectralInvariant`), `IndexedSpectralContracts.lean`, `IndexedSpectralRegistry.lean`, `IndexedPrimitiveFamilies.lean` (the five families), `IndexedDeclarationRules.lean` (the messages of the declaration audit), `IndexedPrimitiveDescriptors.lean` (`SharedLiteral.poly`, `SharedLiteral.rows`) | `SpectralRegression`; `tests/spectral_primitives.rs`; `tests/emit_golden.rs` (the package `spectral-primitives`); the native fixture `spectral_programs` of `scripts/check_indexed_native.sh` | Oracle `SpectralPrimitives`, `SpectralCore`, `SmoothJacobian.spectralInvariant_reverse` |
| **W — weakening** | `IndexedSpectralContracts.lean` (no contract reads a metric, a frame or a physical dimension), `IndexedSpectralRegistry.lean` (the evaluators read the embedded data only) | `SpectralRegression` ("the profile without observations or invariants is accepted on its own", "declaration order independent") | Oracle `SpectralWeakening` |
| **X — reference model** | `scripts/spectral_fixture.py`, `tests/fixtures/spectral.json`, from `scripts/etale_reference.py` and `scripts/finite_spectral_reference.py` | `VastitasAlgebraTest.SpectralReferenceRegression`; `scripts/test_spectral_fixture.py`; `python3 scripts/spectral_fixture.py --check` | Tested only |
| **V — wire** | `IndexedDeclarationProtocol.lean` (`declarationBody`, `polyRows`, `certificateExponent`, `morphismDefinition`, `familyRepresentation`, `naturalField`), the families of `IndexedPrimitiveFamilies.lean`, `src/indexed.rs`, `src/frontend/indexed_parser.rs` | `tests/spectral_declarations.rs`, `tests/spectral_primitives.rs`, `tests/spectral_observations.rs` (protocol and raw-wire tests); `SpectralDeclarationRegression`, `SpectralRegression` | Tested only |
| **L — library** | `stdlib/src/linalg/Vastitas.toml`, `stdlib/src/linalg/mod.vast`, `stdlib/src/linalg/spectral/mod.vast` (`std::linalg::spectral`), `stdlib/Vastitas.toml`, `scripts/build_stdlib_package.py`, `scripts/check_boundaries.py` (`std::linalg` depends on the geometry package alone) | `tests/stdlib_spectral.rs`; `scripts/test_check_boundaries.py` (`RepositoryBoundaryTests`) | — |
| **E — acceptance program** | `examples/packages/spectral-observations/` (`src/profile.vast` declares the plane, its field, spectrum and branch, the invariants, the dimensionless Euclidean chart and the four fields of the point; `src/main.vast` observes them with the failure codes 1–31); the six rejected packages | `tests/spectral_observations.rs`; `tests/examples.rs` | Oracle `SpectralAcceptance` |
| **B — Daleckii–Krein** | `Analysis/DaleckiiKreinTyped.lean`, `Spectral/Prerequisites.lean` | `lean-bridge/Audit.lean` | Bridge, see [C7](#c7) |

<a id="acceptance-conditions"></a>

## Acceptance conditions

The oracle states one corollary per condition that it covers, about accepted
programs, in `SpectralAcceptance.lean` (`c1_fields_and_modules` …
`c13_weakening`, and `s4_trace_square_gradient`); each composes a
declaration or Core theorem with a runtime or algebra theorem. There is no
oracle row for C7, which is a bridge statement. The acceptance program
checks, builds and prints `42`. On the plane `Plane = Affine(2)[x, y]` it
declares H = rows((x, y), (y, −x)) on V = basis(e1, e2), its spectrum
S = eigen(H, t) with χ = t² − x² − y² and adj(tI − H) = tI + H, and the
branch B = simple(S, localize = x² + y², witness = t/2, exponent = 1). On the
point it declares 0, N = [[0, 1], [0, 0]], 2I and J = [[2, 1], [0, 2]] on
W = basis(f1, f2). Observation k adds 2^(k − 1) to 42 when it fails, so a
wrong result changes the output
(`mutated_observations_change_the_native_result` falsifies each of the 31
observations). "Code k" below is observation k.

| Condition | Status and evidence |
| --- | --- |
| <a id="c1"></a>C1. Fields and modules: basis names, at most four basis vectors, one object, `symmetric` checked, presented objects rejected, `E_SPECTRAL` cases, `E_LIMIT` | **Tested** (D): `SpectralDeclarationRegression` (the rejections "rank 5", "no basis", "a repeated basis vector", "another family", "a presented object", "not symmetric", "too few rows", "a short row", "a module of another object", "no module" and "an unknown coordinate", each at its declaration with its message; "a spectral declaration names one object"; "a free module of rank 5 is beyond the limit before any endomorphism is read"; "a 4 × 4 symmetric endomorphism, at the rank limit, has a checked spectrum"); `the_frontend_leaves_spectral_rules_to_the_kernel` and `malformed_spectral_sources_are_rejected_at_their_place` (`tests/spectral_declarations.rs`); `tampered_spectral_declarations_are_rejected_by_the_kernel` (`tests/spectral_observations.rs`: a field that is not symmetric, a spectrum of a field of another object); `a_free_module_of_an_object_outside_cinf_affine_is_rejected` (`tests/stdlib_spectral.rs`); `the_rank_is_bounded_at_the_free_module` (`tests/spectral_limits.rs`); book rejects `spectral-not-symmetric`, `spectral-other-object` and `spectral-rank-limit`. **Proved (oracle)**: `SpectralAcceptance.c1_fields_and_modules`: in a valid environment a free module has 1 to 4 distinct basis names over a smooth object, a field has n rows of n canonical entries for the rank n of its free module on the same object, with Hᵢⱼ = Hⱼᵢ when declared `symmetric`, and the fiber coordinate of a spectrum is no coordinate of its object; from `SpectralDeclarations.checkModule_sound`, `checkRows_sound`, `endomorphism_sound` and `spectrum_sound` |
| <a id="c2"></a>C2. Spectral pair: Faddeev–LeVerrier producer, cofactor checker, the adjugate identity, the Jacobi trace, Cayley–Hamilton, idempotence and Jacobi's formula against kernel-computed quotients; no certificate on the wire | **Tested** (D, V): `SpectralDeclarationRegression` ("the spectrum has the kernel's certificate: χ = t² − x² − y², adj = tI + H, Q = −I", "a spectral declaration takes exactly its fields, and no certificate", "the audit accepts the elaborated example and rejects each tampered declaration"); `SpectralRegression` ("a tampered embedded χ or adjugate is rejected"); `raw_wire_rejects_certificates_and_forged_spectral_fields` (`tests/spectral_declarations.rs`) and `raw_wire_rejects_spectral_certificates_and_forged_maps` (`tests/spectral_observations.rs`): a field `characteristic`, `adjugate`, `idempotence`, `quotient` or `certificate` is `E_PROTOCOL`; the two routes on 256 endomorphisms of the reference model (C15). **Proved (oracle)**: `SpectralDeclarations.checkCertificate_sound` (an accepted certificate satisfies the six identities exactly) and the readings `SpectralValid.characteristic_eq_det`, `adjugate_eq`, `adjugateTrace_at`, `cayleyHamilton_at`, `idempotence_at`, `jacobi_at`, at every point of every commutative ring that receives the rationals; `SpectralAcceptance.c2_spectral_pair` for the spectra of a valid environment; `SpectralAlgebra.identities_ok` (the budgeted products are the plain ones). **Proved (bridge)**: `Spectral.toMv_charPoly` (χ is `Matrix.charpoly` of the field, with t the last variable), `toMv_tCoefficient`, `ringDet_eq_det` and `laplace_det_eq` (the cofactor recursion is `Matrix.det`). That the producer passes the checks for every field is Tested only |
| <a id="c3"></a>C3. Scalar against Jordan: equal χ and invariants, different module action; Σ_H never reduced | **Tested** (R, E): codes 18–31: t annihilates H(0, 0) and not H(3, 4), χ annihilates H at (1, 2) and (3, 4); t − 2 annihilates 2I and not J, the entry (f1, f2) of (t − 2)(H) is 0 for 2I and 1 for J, and every invariant of 2I equals that of J; the same for 0 and N with t; (t − 2)² annihilates J and t² annihilates N. `SpectralRegression` (the Core module of `spectralFixture`, "the module action reads exact entries"); `SpectralReferenceRegression` (`modules`: f(H) for 0, N, 2I and J against the reference). **Proved (oracle)**: `SpectralRuntime.Examples.scalar_jordan_regression` and `SpectralAcceptance.c3_scalar_jordan`: 2I and J, and 0 and N, have valid certificates with equal χ and equal trace powers for every power, both are annihilated by their χ, which is not t − 2, and t − 2, or t, annihilates one and not the other; `SpectralRuntime.annihilates_char` (χ annihilates every fiber of an accepted spectrum); `SpectralCore.core_spectral_annihilates`, `core_spectral_action_entry` (an accepted call evaluates to the runtime action on the declared rows) |
| <a id="c4"></a>C4. Invariants as smooth maps: equal to a declared reference map; Newton's identity; a zero differential is not ⊥ | **Tested** (D, P, E): code 1 (`same_smooth(tr2, ref2)`), code 2 (the differential of tr(H) is the zero covector over (3, 4), not ⊥), code 3 (the gradient of c0 is −1/2 that of tr2 at (1, 2) and (3, 4)); `SpectralDeclarationRegression` ("an invariant is a smooth map with its exact image and its provenance", "Newton's identity: c0 = −½ tr2 for the trace-free H"); `SpectralRegression` ("a forged invariant map, power, index or source is rejected"); `tests/stdlib_spectral.rs` (tr(D³) and the constant coefficient of a field of rank 4 against declared maps). **Proved (oracle)**: `SpectralDeclarations.invariant_sound`, `tracePowerImage_at`, `SpectralValid.charCoefficient_at`; `SpectralCore.spectralInvariant_valid_sound`, `spectralInvariant_tracePower_at`, `spectralInvariant_charCoefficient_at`, `core_spectral_invariant`; `SpectralAcceptance.c4_invariants` (an accepted trace power is tr(H(x)ᵏ) with 1 ≤ k ≤ 8 at every point of every ring, an accepted coefficient the coefficient of its χ) and `c4_stage5_invariants` (for the example, tr2 = 2x² + 2y², c0 = −x² − y² = −½ tr2, tr1 = 0, and the gradient of c0 is (−2p₀, −2p₁)). **Proved (bridge)**: `Spectral.toMv_tracePower` and `realPoly_tracePower` (an accepted trace power is the trace of the power of the field in Mathlib) |
| <a id="c5"></a>C5. Roadmap gradient: (4x, 4y) on the dimensionless Euclidean chart, the origin included | **Tested** (E): codes 4–6: the gradient of `tr2` under `Euclid`, with the reading (x: Ratio, y: Ratio) and the interpretation of `Euclid` as dimensionless, is (4, 8) at (1, 2), (12, 16) at (3, 4) and (0, 0) at the origin. **Proved (oracle)**: `SpectralAcceptance.s4_trace_square_gradient`: for an accepted `trace_power(H, 2)` of the field of the example, the differential at every rational point (p₀, p₁) is (4p₀, 4p₁), and so is its `sharp` under the Euclidean metric; `c5_roadmap_gradient`: an accepted `differential` node of it computes that covector. **Planned (bridge)**: (4x, 4y) at every real point, for the bridge integration step |
| <a id="c6"></a>C6. The reverse Core of an invariant is the reverse pass of Stage 3; no reverse rule of its own | **Tested** (P): `SpectralRegression` ("an invariant pulls back along its map, an observation is opaque to a reverse pass", "the reverse compilation of the spectral module compiles every differential and evaluates to 42", "the compiled backward steps pull back along the maps of tr2 and c0"); the generated backward functions of `spectral-primitives`, byte for byte (`tests/emit_golden.rs`). **Proved (oracle)**: `SpectralCore.spectralInvariant_rule` (the derivative rule of an invariant is `morphism` with its map) and `compiled_invariant_step` (a compiled reverse step along it is the `cotangentJacobian` of that map); `SmoothJacobian.spectralInvariant_reverse` and its case of `registry_reverse_sound`; `SpectralAcceptance.c6_reverse_core_invariant` |
| <a id="c7"></a>C7. Daleckii–Krein: typed Hermitian lift, cotangent action with the pairing Re tr(KX), a noncommuting order regression, and emitted reverse Core of a trace power equal to the Daleckii–Krein cotangent composed with the derivative of the field | **Proved (bridge)** (B), in `VastitasBridge.Analysis.DaleckiiKrein`: step 1, `dslope_comm`, `fderivCandidate_isSelfAdjoint`, `hermCfc`, `hermDerivative`, `hasFDerivAt_cfc_selfAdjoint`, `matrix_hasFDerivAt_cfc_selfAdjoint`; step 2, `trPairing` (X ↦ Re tr(KX), with no star on K), `dkCotangent`, `dkCotangent_trPairing` (the representative Σ f^[s, r] P_s K P_r, equal to the order of the derivative only through `dslope_comm`), `dkCotangent_trPairing_eq`, `dkCotangent_trace`, `dkCotangent_trace_pow`; the order regression `dk_cotangent_two_point` and `dk_cotangent_two_point_example` (at diag(0, 1), f = t³ and K = [[0, 1], [1, 0]] the representative is K, where a commuting formula gives 0). In `VastitasBridge.Spectral`: `hermAt`, `hasFDerivAt_hermAt`, `fderiv_trace_pow_field` and `fderiv_trace_pow_field_apply` (the derivative of z ↦ tr(M(z)ᵏ) for a symmetric real polynomial field is the Daleckii–Krein cotangent composed with the derivative of the field, with no hypothesis left), and `toMv_tracePower` for the kernel's trace power. Repeated eigenvalues are included: the theorems need no simple spectrum. **Planned (bridge)**: that the emitted reverse Core of an accepted trace-power invariant, through the public resource and pure entries, equals that cotangent composed with DH, for the bridge integration step. Steps 3–5 of #471 are not claimed |
| <a id="c8"></a>C8. Gap certificate: finite charts only, a reduced witness, the checked identity; the localizer 1 for the Stage 5 matrix has no witness; a Jordan block and a perturbed witness are rejected | **Tested** (D): `SpectralDeclarationRegression` ("a localization with t", "a zero localization", "an unreduced witness", "a wrong witness", "a witness perturbed by 10⁻²⁰", "a wrong exponent", "the gap at the origin", "an exponent beyond the limit", "the Jordan block", "the Jordan block with a shifted witness"; "the branch has its localization in the base and the kernel's quotient 1"; "the squared gap (2t·g, 4g²) is a valid chart too"); `tampered_spectral_declarations_are_rejected_by_the_kernel` (g = 1, the perturbed witness, g = t, g = 0, W = t²/2); `the_frontend_leaves_spectral_rules_to_the_kernel`; `powers_and_exponents_are_bounded`; book rejects `spectral-gap-at-origin`, `spectral-jordan-branch` and `spectral-wrong-witness`; the charts of `tests/fixtures/spectral.json` (C15). **Proved (oracle)**: `SpectralDeclarations.checkWitness_sound`, `WitnessValid.gap_at`, `SpectralValid.unit_at` (where χ vanishes and g has an inverse u, χ′ has the inverse W·uᵉ), `SpectralValid.derivative_ne_zero`, `branch_sound`; `Examples.unit_gap_no_witness` (g = 1 has no witness, exponent and quotient at all: at (0, 0, ε) in the dual numbers χ′ = 2ε would be a unit) and `Examples.origin_off_chart` (every accepted localization vanishes at the origin); `SpectralAcceptance.c8_gap_certificate`, which adds that the Jordan block has no gap certificate at all and that the perturbed witness fails with every quotient. **Proved (bridge)**: `Spectral.unit_witness_localization` (∂ₜχ is a unit in the localization away from g of ℚ[x, t]/(χ)) |
| <a id="c9"></a>C9. Branch points and ⊥: on and off the chart, the origin | **Tested** (R, E): codes 7–12: ((3, 4), ±5) and ((1, 0), ±1) are branch points, ((3, 4), 4) is not, and ((0, 0), 0) is not although χ(0, 0, 0) = 0; `SpectralRuntimeRegression` ("((3, 4), 5) and ((3, 4), -5) are branch points", "4 is no eigenvalue at (3, 4)", "the origin is off the chart although χ(0, 0) = 0", "the branch differential is the failure value off the branch", "the projector is the failure value off the branch"); `SpectralRegression` ("off the branch the differential is the failure value"); the branch points of `tests/fixtures/spectral.json`. **Proved (oracle)**: `SpectralRuntime.onBranch_iff`, `branch_some_iff` (the differential and the eigenprojector are defined exactly where g(p) ≠ 0 and χ(p, t) = 0), `off_chart_bottom` (off the chart ⊥ and `(0, 0)`), `projectorEntry_ne_failure_iff`; `SpectralCore.core_spectral_on_branch`; `SpectralAcceptance.c9_branch_points`, with the six points of the example decided. **Proved (bridge)**: `Spectral.charPoly_eval_real` and `branch_mem_spectrum` (a real zero of χ is an eigenvalue of H(x)) |
| <a id="c10"></a>C10. Branch derivative: −∂ᵢχ/∂ₜχ and tr(P ∂ᵢH); (3/5, 4/5) at ((3, 4), 5) | **Tested** (R, E): codes 13–15: dλ = (3/5, 4/5) at ((3, 4), 5) and (−3/5, −4/5) at ((3, 4), −5), both unit covectors under the Euclidean metric; `SpectralRuntimeRegression` ("the branch differential is ±(3/5, 4/5) at (3, 4)", "the branch differential is ±(1, 0) at (1, 0)", "the branch differential at (3, 4) is a unit covector"); `SpectralRegression` ("the branch differential at ((3, 4), 5) is the covector (3/5, 4/5) at (3, 4)"). **Proved (oracle)**: `SpectralRuntime.branchDifferential_implicit` (cᵢ·χ′(p, t) = −∂ᵢχ(p, t), from the evaluated partial derivatives, never `cot`), `branchDifferential_hellmann_feynman` (cᵢ = tr(P·∂ᵢH(p)), from Jacobi's formula), `branchDifferential_fits`; `SpectralCore.core_spectral_branch_differential`; `SpectralAcceptance.c10_branch_derivative` and `Stage5.branch_differentials`. **Proved (bridge)**, conditional: `Spectral.implicit_branch_fderiv` and `implicit_branch_fderiv_eval` (Dλ(p) = −(∂ₜχ)⁻¹·∇ₓχ when λ exists and is differentiable). **Planned (bridge)**: the implicit-function form for an accepted branch differential, for the bridge integration step |
| <a id="c11"></a>C11. Eigenprojector: P² = P, tr P = 1, HP = tP, a symmetric P, P₊ + P₋ = I | **Tested** (R, E): codes 16 and 17: P₊ = (1/5)[[4, 2], [2, 1]] and P₋ = (1/5)[[1, −2], [−2, 4]] at (3, 4), symmetric; `SpectralRuntimeRegression` ("P₊ = (1/5)[[4, 2], [2, 1]] and P₋ = (1/5)[[1, -2], [-2, 4]]", "P² = P", "tr P = 1", "H P = t P", "P is symmetric", "P₊ + P₋ = I", "5 P₊ − 5 P₋ = H(p)"); the eigenprojectors of `tests/fixtures/spectral.json`. **Proved (oracle)**: `SpectralRuntime.projector_idempotent` (from identity 5 at χ = 0), `projector_trace_one` (identity 3), `adjugate_eigen` and `projector_eigen` (identity 2), `eigenvector_exists` (a column with Pⱼⱼ ≠ 0 is an eigenvector, without determinants); `SpectralCore.core_spectral_branch_projector`; `SpectralAcceptance.c11_eigenprojector` and `Stage5.projectors`. That P is symmetric for a symmetric field and that P₊ + P₋ = I are Tested only: the first is not stated, and the second is a property of the example, not a law of every field |
| <a id="c12"></a>C12. Degenerate cases: H = 0, rank 1, the origin, four basis vectors at the limit | **Tested** (D, L): `SpectralDeclarationRegression` ("the zero endomorphism has the spectrum t² and no chart at all", "a rank-1 endomorphism has the chart g = 1, W = 1, e = 0", "a 4 × 4 symmetric endomorphism, at the rank limit, has a checked spectrum"); `tests/stdlib_spectral.rs` (a field of rank 1 whose chart is the plane with the witness 1, a field of rank 4, and the zero field, whose trace square has the zero differential); code 12 (the origin). **Proved (oracle)**: `SpectralAcceptance.c12_degenerate` (H = 0 on the point has a valid certificate, the rank-1 field has the gap certificate g = 1, W = 1, every chart of the example misses the origin, rank 4 is accepted and rank 5 is not) |
| <a id="c13"></a>C13. Weakening: no binding of Stages 3 and 4 changes; spectral bindings are environment-free and metric-free | **Tested** (W): `SpectralRegression` ("the profile without observations or invariants is accepted on its own", "declaration order independent"); `SpectralDeclarationRegression` ("the source checker accepts the Stage 5 example in any order"). **Proved (oracle)**: `SpectralWeakening.spectral_weakening_binding`, `spectral_weakening_entry`, their `_of_valid` forms, `stage4_bindings_spectral_free`, `spectral_bindings_metric_free`, `spectral_bindings_frame_free`, `spectral_bindings_nature_free`; `SpectralCore.spectral_bindings_environment_free`; `SpectralAcceptance.c13_weakening`. The declaration statements hold for every table of class ranks; see [gaps](#gaps) |
| <a id="c14"></a>C14. Wire: protocol 9 only; protocols 7 and 8 give `E_PROTOCOL`; forged invariants and tampered embedded data are rejected | **Tested** (V): `spectral_forms_select_protocol_nine_only`, `the_kernel_decodes_the_spectral_program_only_in_protocol_nine`, `raw_wire_rejects_certificates_and_forged_spectral_fields`, `natural_digits_are_bounded_as_the_decoder_bounds_them` (`tests/spectral_declarations.rs`); `spectral_primitives_select_protocol_nine_and_decode_only_there`, `raw_wire_rejects_embedded_spectral_data`, `raw_wire_forgeries_of_references_are_rejected_by_the_kernel` (`tests/spectral_primitives.rs`); `the_example_selects_protocol_nine_and_older_envelopes_reject_it`, `raw_wire_rejects_spectral_certificates_and_forged_maps`, `tampered_spectral_declarations_are_rejected_by_the_kernel`, `tampered_spectral_bindings_and_bodies_are_rejected_by_the_kernel` (`tests/spectral_observations.rs`); `SpectralDeclarationRegression` and `SpectralRegression` (protocols 7 and 8 reject every spectral family, declaration, invariant and observation; "a forged invariant map, power, index or source is rejected", "a tampered embedded endomorphism is rejected", "a tampered embedded g, W or exponent is rejected", "a stale reference is rejected: another spectrum's data, or another declaration's name"). Not proved: the decoder and the frontend are tested only |
| <a id="c15"></a>C15. Independent reference: a fixture from the étale and finite spectral reference models agrees with the kernel | **Tested** (X): `VastitasAlgebraTest.SpectralReferenceRegression` compares the kernel's certificates (and their check, a second route), its trace powers up to k = 5 and its coefficients for the eight subjects of `tests/fixtures/spectral.json` (the example, a cubic, a symmetric 3 × 3, a quartic companion matrix, 0, N, 2I and J), its gap checks with the verdicts of eleven charts, and its branch observations at the branch points of the reference; `scripts/test_spectral_fixture.py` (`test_fixture_is_fresh` and the checks of the example, the Jordan contrast, the charts and the branch points); `python3 scripts/spectral_fixture.py --check`. The étale model's own tests run both routes on 256 endomorphisms of A². Tested only |
| <a id="c16"></a>C16. Limits: rank, power, terms and work give `E_LIMIT` before any comparison, within seconds | **Tested** (D): `tests/spectral_limits.rs` (`the_rank_is_bounded_at_the_free_module`, `powers_and_exponents_are_bounded`, `terms_are_bounded_before_any_comparison`, `the_spectral_pair_is_bounded_by_the_work_budget`): each limit is the only diagnostic of its package, reported before the comparison it guards, and each check ends within 30 seconds; the declarations at the limits are accepted. `SpectralDeclarationRegression` ("a long exponent is a limit, before any product"). **Proved (oracle)**, the soundness half: an accepted declaration is within `spectralRank` and `spectralPower` (`c1_fields_and_modules`, `invariant_sound`, `checkWitness_sound`), and the budgeted products are the plain ones (`SpectralAlgebra.identities_ok`, `tracePower_ok`). That the limits bound the work is Tested only |
| <a id="c17"></a>C17. Library: `std::linalg::spectral` is usable from a path package; name audit; boundary rule | **Tested** (L): `spectral_families_from_the_library_check_build_and_run_from_a_path_package`, `mutated_spectral_observations_change_the_native_result`, `linalg_exports_exactly_the_spectral_module_and_its_four_families` (the package `vastitas_linalg` depends on the geometry package alone, its root exports `spectral` alone, `spectral` exports the four families, and no other name resolves), `a_free_module_of_an_object_outside_cinf_affine_is_rejected` (`tests/stdlib_spectral.rs`); `RepositoryBoundaryTests.test_std_packages_depend_only_on_the_listed_packages` (`scripts/test_check_boundaries.py`) and `python3 scripts/check_boundaries.py`. [ADR 0001 §12](adr/0001-mathematics-first-stdlib.md#12-exact-spectral-pairs-and-simple-branches-of-polynomial-matrix-fields-amendment-2026-11-15) admits the module |
| <a id="c18"></a>C18. Native: the program checks, builds and prints 42; mutations flip every code; the rejected packages print their recorded diagnostics | **Tested** (E): `the_example_checks_builds_and_prints_42_in_place`, `each_observation_adds_its_own_bit`, `mutated_observations_change_the_native_result` (three groups of mutations falsify every one of the 31 codes, and the output is 42 plus exactly their bits), `rejected_stage5_packages_print_their_diagnostics` (`tests/spectral_observations.rs`); `spectral_program_checks_builds_and_prints_42` (`tests/spectral_primitives.rs`); `book_programs_print_their_output` and `book_rejected_packages_print_their_diagnostics` (`tests/examples.rs`); the native fixture `spectral_programs` of `scripts/check_indexed_native.sh`. Native refinement is not claimed |
| <a id="c19"></a>C19. CI: green, with the operating systems of each job | **Planned**: recorded when the stage closes |
| <a id="c20"></a>C20. Independent whole-stage review, with each finding fixed or filed | **Planned**: recorded when the stage closes |

## Premises of the accepted-program theorems

The theorems of `SpectralAcceptance.lean` are about the declarations of a
valid environment, about one accepted node, or about the values that the
kernel decides for the example. *Accepted* means, as for frames, that the
Core term type-checks against the module's declarations (`Typing.HasType`,
which for a primitive node includes the validity of its binding and the
types of its operands) and that the module's environment is valid
(`module.declarations.indexed.Valid`). Nothing is assumed about the
embedded data: a valid binding embeds its field, spectrum and branch as
declared (`SpectralCore.DeclaredEndo`, `DeclaredSpectrum`, `DeclaredBranch`,
from the binding's validity), and the valid environment makes that data pass
the kernel's checks (`DeclaredSpectrum.checked`: `SpectralValid`;
`DeclaredBranch.checked`: `WitnessValid`). The lengths of points come from
their checked types.

Two premises stay, as in the oracle's `core_*` theorems of Stages 3 and 4:

- **operand evaluation**: each leaf operand evaluates, at some fuel, to a
  value (`eval module fuel values t = some v`);
- **operand typing**: those values have the operand types
  (`PrimitiveValuesHaveTypes`).

The rows C5 (`s4_trace_square_gradient`) and C4 (`c4_stage5_invariants`)
also assume that the field has the rows of the example. These theorems are
not composed with whole-term preservation,
`IndexedEvaluationSafety.evaluation_total_and_typed`.

## Per-issue ledger

| Issue | Met by this profile | Open |
| --- | --- | --- |
| [#337](https://github.com/MGYamada/Vastitas/issues/337) exact spectral pair | The characteristic scheme with the module action, kept apart from the reduced spectrum; the scalar matrix against the Jordan block and 0 against N (C2, C3) | Similarity and base change of spectral pairs, cyclic evidence that the module is locally free of rank one, the band-crossing consumer (#247) |
| [#765](https://github.com/MGYamada/Vastitas/issues/765) standard étale charts | One finite chart of a spectral pair with a unit witness, its branch points and its eigenprojector (C8–C11); its first regression as a kernel fixture (C15) | Covers by several charts, image opens, cluster splits by Bézout identities, charts whose localizer is not in the base, function descent and the standard étale algebra (§B) |
| [#471](https://github.com/MGYamada/Vastitas/issues/471) spectral AD | Steps 1 and 2: the typed Hermitian lift and the cotangent action with Re tr(KX), the order regression and the trace powers of fields (C7) | The agreement with emitted reverse Core (Planned for the bridge integration step); steps 3–5: the C∞ comparison (#361), the general correspondence (#290) and pass preservation (#164) |
| [#261](https://github.com/MGYamada/Vastitas/issues/261), [#160](https://github.com/MGYamada/Vastitas/issues/160) modules and `std::linalg` | Free modules with a named basis and their endomorphism fields in `std::linalg::spectral` (C1, C17) | The reconciliation of `FreeModule` and `Endomorphism` with the module theory of the algebra family and the bundles, which ADR 0001 §12 records |
| [#606](https://github.com/MGYamada/Vastitas/issues/606) opens | — | The branch as a smooth function on an open, and Σ_H as a presented object |
| [#324](https://github.com/MGYamada/Vastitas/issues/324) checked extraction adapters | — | Numerical eigensolvers and their adapters, outside the profile |

<a id="gaps"></a>

## Gaps

- **Emitted reverse Core of a trace power.** That it computes the
  Daleckii–Krein cotangent composed with the derivative of the field, the
  gradient at every real point and the implicit-function form of an accepted
  branch differential are Planned for the bridge integration step of the
  stage.
- **Completeness of the producer.** That the Faddeev–LeVerrier producer gives
  a certificate that passes the checks for every field of an admitted size
  is tested, not proved. Soundness does not depend on it; an incomplete
  producer would reject a valid spectrum with `E_SPECTRAL`.
- **Symmetric eigenprojectors.** That P is symmetric for a field declared
  `symmetric` is observed, not stated, and P is not identified with
  Mathlib's `spectralProjection`; the resolution identities are not stated.
- **Class ranks under weakening.** `spectral_weakening_entry` holds for every
  table of class ranks. That `classRanks` computes the same table with and
  without the added declarations is not proved, as for frames.
- **Exact rationals in the observations.** The rationals of the branch
  observations and of the module action are not bounded at run time; their
  growth is not measured.
- **Reference coverage.** The fixture covers eight fields of rank 2 to 4 over
  at most two coordinates, and eleven charts.
- **Composition with whole-term preservation** is not proved; see
  [premises](#premises-of-the-accepted-program-theorems).
- **Rust parsing** is Assumed. The kernel re-checks every declaration, but
  parser fidelity is tested only.
- **Performance** is not claimed (#222).

<a id="proof-boundary"></a>

## Proof boundary

- **Proved (oracle).**
  - An accepted certificate satisfies the six identities exactly and at every
    point of every commutative ring that receives the rationals; an accepted
    gap witness makes χ′ a unit where g is; the localization 1 of the example
    has no witness at all, and the Jordan block has no gap certificate.
  - An accepted invariant is the trace power or the coefficient of its field;
    the gradient of the trace square of the example is (4p₀, 4p₁) at every
    rational point.
  - The spectral runtime: definedness and ⊥ of the branch observations, the
    laws of the eigenprojector, the implicit-function and Hellmann–Feynman
    forms of the differential, Cayley–Hamilton on every fiber, and the scalar
    field against the Jordan block.
  - Every spectral binding is total and typed, erases to the runtime and
    embeds its declarations as declared; accepted spectral nodes evaluate to
    the runtime operations on the declared data, and a compiled reverse step
    along an invariant is the `cotangentJacobian` of its map.
  - Spectral declarations at any position leave every unrelated binding and
    every declaration of another kind unchanged, for every table of class
    ranks; no spectral binding reads a metric, a frame or a physical
    dimension.
- **Proved (bridge).** The checked χ is `Matrix.charpoly` of the field and its
  coefficients are those of the characteristic polynomial; the cofactor
  recursion is `Matrix.det`; an accepted trace power is the trace of the
  power of the field; a real zero of χ is an eigenvalue; ∂ₜχ is a unit in the
  localization away from g. The Daleckii–Krein steps 1 and 2 with the order
  regression, and the derivative of the trace power of a symmetric
  polynomial field as the Daleckii–Krein cotangent composed with the
  derivative of the field. The implicit derivative of a branch, under its
  existence and differentiability.
- **Planned.** The emitted reverse Core of an accepted trace power as the
  Daleckii–Krein cotangent, the gradient at every real point and the
  implicit-function form of an accepted branch differential (the bridge
  integration step); CI (C19) and the review (C20).
- **Tested only.**
  - Raw-wire and tampered-Core rejection, and protocols 7 and 8.
  - Parser fidelity and diagnostic messages.
  - The completeness of the producer, and that the limits come before the
    comparisons and bound the work.
  - Agreement with the Python references.
  - Symmetric eigenprojectors and P₊ + P₋ = I for the example.
  - Native execution of the compiled programs and their mutations.
  - The boundary of `std::linalg`.
- **Assumed.**
  - The Rust frontend's parsing.
  - The Lean-to-C toolchain and the C compiler.
  - Lean core `Rat` and GMP.
  - mathlib itself.

<a id="not-claimed"></a>

## Not claimed

Each gets a follow-up issue when Stage 5 closes, unless an issue already owns
it:

- covers by several charts, image opens and cluster splits by Bézout
  identities, and charts whose localizer is not in the base (#765);
- Σ_H as a presented affine object, and the branch as a smooth function on an
  open (#606);
- derivatives of eigenprojectors and eigenvectors, and higher derivatives;
- similarity and base change of spectral pairs, evidence that the module is
  locally free of rank one, and the band-crossing consumer (#337, #247);
- Hermitian fields over QQ(i), physical units of eigenvalues and
  floating-point realizations;
- numerical eigensolvers and checked extraction adapters (#324);
- steps 3 to 5 of #471;
- performance (#222).

## Validation

The batches run these commands, one heavy check at a time, and the results
of the whole stage are recorded when it closes:

- `cargo fmt --check`, `cargo clippy --locked --all-targets -- -D warnings`
  and `cargo test --locked --all-targets --no-fail-fast`.
- `lake -d lean-kernel build` with every library, executable and regression
  library; `bash scripts/check_kernel_regressions.sh`;
  `bash scripts/check_indexed_native.sh`.
- `lake -d lean build` and `lake -d lean env lean scripts/audit_axioms.lean`.
- `(cd lean-bridge && lake build)` and `(cd lean-bridge && lake env lean Audit.lean)`;
  from the repository root,
  `VASTITAS_REPLAY_THREADS=1 bash scripts/replay_lean.sh lean-bridge -v VastitasBridge`.
- `python3 scripts/check_spec.py`, with the statement pins of the cited
  oracle and bridge theorems, and the resolver of each environment;
  `python3 scripts/check_primitive_table.py`;
  `python3 scripts/spectral_fixture.py --check`.
- `python3 scripts/check_boundaries.py` and
  `python3 -m unittest discover -s scripts -p 'test_*.py'`.
- `python3 scripts/check_docs.py`, `mdbook build`, `python3 scripts/check_book.py`
  and `python3 scripts/check_grammar_derivations.py --compiler target/debug/vastitas`.

The documentation step of batch 4, on the integration branch of batches 3
and 4 at `e9863e5`, ran `python3 scripts/check_docs.py`, `mdbook build` and
`python3 scripts/check_book.py` after each of its commits;
`python3 scripts/check_spec.py --update-statements oracle`, which added 59
oracle pins and changed none, then `--write` and the plain check (43
properties, 112 claims, 157 oracle and 37 bridge pins); the oracle resolver
`(cd lean && VASTITAS_SPEC_INPUT=../docs/spec/pins/oracle.json lake env lean -DwarningAsError=true ../scripts/spec_resolve.lean)`
(154 theorems and 3 kernel definitions resolved);
`python3 scripts/check_grammar_derivations.py --compiler target/debug/vastitas`
(500 derived texts, no parse diagnostic that no rule allows); and
`python3 -m unittest discover -s scripts -p 'test_*.py'` (1134 tests, OK).
Each passed. The other commands belong to the code and proof lanes, whose
pull requests record their results.
