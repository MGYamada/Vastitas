# Historical Stage 3 smooth affine geometry acceptance map

This map links each acceptance condition of historical Stage 3 to its
implementation, positive and negative tests, oracle and bridge theorems, and
native evidence. Stage 3 is a finite, checked profile of smooth real affine
geometry and of the metric-free reverse cotangent pullback over exact QQ
polynomial maps ([tracker #604](https://github.com/MGYamada/Vastitas/issues/604)).
It does not include performance: the Fast like C verdict stays with #222. The
reference chapter is [smooth affine declarations](language/smooth-declarations.md).

## Scope and revision ledger

The conditions are the checklist C1–C19 of #604, which turns the Stage 3
examples of the [historical roadmap](guide/historical-roadmap.md#stage-3-smooth-affine-geometry-and-reverse-ad)
into executable checks. The decisions behind the profile are:

- **Field.** QQ only. Exact `Rat` lives inside the runtime and surfaces as
  `Int` inputs and `Pair<Int>` observations. Pure Core is unchanged. There are
  no floats.
- **Reverse pass.** It is a verified runtime routine over the program value
  that checked Core builds: `compose` makes a node. The compiler emits no
  reverse Core.
- **Smooth objects.** They have their own declaration constructor and the
  sealed classification `CInfAffine`. They are not an overload of the Stage 2
  `affine` data, so no Stage 2 theorem weakens.
- **Failure semantics.** A wrong basepoint gives the runtime failure value ⊥.
  It is absorbing, equals nothing, and its components read `(0, 0)`. Wrong
  objects, variance and metric selection are static errors.
- **Metrics.** Metrics and evidence are declarations. The kernel computes the
  inverse and `L D Lᵀ` certificates and checks them again; certificates never
  come from the wire. `flat` names its metric with `using =`, and `sharp` also
  names nondegenerate evidence with `evidence =`. There is no gradient
  primitive: a gradient is an ordinary checked function. `MetricForm` stays
  nominally distinct from the protocol-8 diagonal Hermitian `Metric`.
- **Wire.** Protocol 9 only, with no protocol 10 (#533).
- **Admission.** [ADR 0001 §10](adr/0001-mathematics-first-stdlib.md#10-smooth-affine-differentials-and-metrics-amendment-2026-11-04)
  admits `std::differential`, `std::geometry::metric` and
  `std::geometry::smooth::affine`, and records the #360 decision.
- **Dependencies.** The mathlib bridge requires the kernel and the oracle by
  path, one way only. The kernel and the oracle stay mathlib-free.

### Roadmap sentences

| Roadmap sentence | How this profile meets it | Rows |
| --- | --- | --- |
| `Affine(n)` is smooth real affine space; `Affine(K, n)` is algebraic | Separate smooth declarations; `Affine(K, n)[…]` is sugar for the Stage 2 `spec[…] over K` | C1, C2 |
| Pull a covector at g(f(x)) back along g at f(x), then along f at x; it agrees with the pullback along the composite and lies in T*ₓ | Observed by the acceptance example; the chain rule is proved in the oracle and in the bridge | C4, C5 |
| A seed from a different point must fail | The checked failure value ⊥, which never equals a covector | C6 |
| The operation belongs to `std::differential` | `std::differential` owns the pullback | C17 |
| A reverse pass agrees on the actual checked program, including saved or recomputed forward values | A verified runtime routine over the program value that checked Core builds; saved and recomputed modes; a first-class tape | C7, C8 |
| `gradient(f, using = g)` needs a selected metric and nondegeneracy evidence, even in Euclidean coordinates | Named `MetricForm` declarations with checked evidence; the gradient is an ordinary function | C13, C14 |
| The Fréchet and Kähler comparisons are distinct obligations | Two independent bridge theorems | C10, C11 |

### Steps

| Step | Pull request | Merge |
| --- | --- | --- |
| S0a–S0f: a coordinate named `frac` (#599); the oracle exports `checkIso` facts (#598); `E_ENDPOINT` names roles and objects (#602); bridge memory budget (#600); ADR 0001 §10 | [#608](https://github.com/MGYamada/Vastitas/pull/608), [#611](https://github.com/MGYamada/Vastitas/pull/611), [#613](https://github.com/MGYamada/Vastitas/pull/613), [#615](https://github.com/MGYamada/Vastitas/pull/615), [#609](https://github.com/MGYamada/Vastitas/pull/609), bundled by [#616](https://github.com/MGYamada/Vastitas/pull/616) | `main` |
| S1: kernel `SmoothRuntime`, exact `invert?`/`ldl?`, reference fixture, structural oracle theorems | [#610](https://github.com/MGYamada/Vastitas/pull/610) | `02f1e2b` |
| S2: bridge derivative correspondence, kernel chain rule, Fréchet comparison | [#612](https://github.com/MGYamada/Vastitas/pull/612) | into #610 |
| S3: smooth objects and maps end to end | [#614](https://github.com/MGYamada/Vastitas/pull/614) | into #610 |
| S4: fibers, tapes, `cotangent_pullback`, `differential`, `linearize`, `backward` | [#617](https://github.com/MGYamada/Vastitas/pull/617) | batch 2, [#617](https://github.com/MGYamada/Vastitas/pull/617), `d17b699` |
| S5: metrics, evidence, `flat` and `sharp` | [#619](https://github.com/MGYamada/Vastitas/pull/619) | batch 2, [#617](https://github.com/MGYamada/Vastitas/pull/617), `d17b699` |
| S6: mathlib-free oracle chain rule, porting PR #377 | [#620](https://github.com/MGYamada/Vastitas/pull/620) | batch 2, [#617](https://github.com/MGYamada/Vastitas/pull/617), `d17b699` |
| S7a: bridge Kähler comparison and metric meaning | [#618](https://github.com/MGYamada/Vastitas/pull/618) | batch 2, [#617](https://github.com/MGYamada/Vastitas/pull/617), `d17b699` |
| S7b: bridge corollaries for accepted Core | [#624](https://github.com/MGYamada/Vastitas/pull/624) | batch 2, [#617](https://github.com/MGYamada/Vastitas/pull/617), `d17b699` |
| S8: the acceptance example and its native evidence | [#621](https://github.com/MGYamada/Vastitas/pull/621) | batch 2, [#617](https://github.com/MGYamada/Vastitas/pull/617), `d17b699` |
| `E_ENDPOINT` roles for the smooth, fiber and metric primitives | [#625](https://github.com/MGYamada/Vastitas/pull/625) | batch 2, [#617](https://github.com/MGYamada/Vastitas/pull/617), `d17b699` |
| S9: `std::geometry::smooth::affine`, `std::geometry::metric`, `std::differential`; this map, the reference and guide chapters, status pages | this change | — |

Status terms below:

- **Proved (oracle)** is a theorem about kernel data and runtime definitions
  in `lean/VastitasOracle/`, mathlib-free, about the checker that accepts the
  input.
- **Proved (bridge)** is a mathlib theorem in `lean-bridge/`.
- **Tested** is a regression or integration test, including native execution.
  Testing is not a proof of all inputs.
- **Assumed** is a trusted component listed under
  [proof boundary](#proof-boundary).
- **Not claimed** is outside this profile; the
  [not-claimed list](#not-claimed) records it.

## Evidence key

Kernel files are in `lean-kernel/VastitasKernel/`, and kernel regressions run
from `scripts/check_kernel_regressions.sh`. Rust tests are in
`tests/smooth_differential.rs` unless noted. Oracle files are in
`lean/VastitasOracle/`, and bridge files in
`lean-bridge/VastitasBridge/Differential/`.

| Key | Implementation | Tests | Theorems |
| --- | --- | --- | --- |
| **S — objects and maps** | `SmoothDeclarations.lean` (`checkObject`, `checkMap`), `IndexedSmoothSource.lean`, `IndexedSmoothContracts.lean`, `Indexed.lean` (`smoothAffine`, `canonical`), `IndexedPrimitiveBinding.lean`, `SmoothRuntime.lean` (`Program`, `compose`, `same`, `composite`, `intPoint`) | `SmoothObjectRegression`; `objects_example_checks_builds_and_executes`, `mutated_object_observations_change_the_native_result`, `smooth_declarations_reject_mismatched_forms_with_specific_codes`, `smooth_maps_resolve_source_coordinates_and_reject_variance_errors`, `smooth_and_presented_objects_stay_disjoint`, `algebraic_affine_spelling_is_sugar_for_spec_over_a_base` | Oracle `SmoothDeclarations` (`smoothAffine_sound`, `smooth_objects_are_declared`, `sealed_families_exclude_smooth`, `smooth_families_exclude_foreign`, `smoothCompose_reifies`, `core_compose_reifies`), `SmoothPrimitives` (`smoothConstant_total` … `smoothIntPoint_total`), `SmoothCanonical` (`composite_wellTyped`); bridge `Derivative.toMv_compose`, `ChainRule.smoothEqual_iff` |
| **D — reverse pass** | `SmoothRuntime.lean` (`cot`, `Program.reverse`, `Program.forward`, `Tape`, `pullback`, `linearize`, `backward`, `differential`) | `SmoothRuntimeRegression`, `CotangentRegression`; `cotangent_example_checks_builds_and_executes`, `each_pullback_binding_lowers_to_its_own_mode`, `cotangent_programs_lower_to_the_shared_smooth_runtime` | Oracle `SmoothRuntime` (structural), `SmoothCalculus` (chain rule), `SmoothReverse` (accepted Core); bridge `ChainRule`, `Frechet`, `Kaehler`, `Derivative` |
| **F — fibers** | `SmoothRuntime.lean` (`Fiber`, `vector`, `fiberAt`, `fiberEqual`, `component`, `pairing`); the `fiber_*` bindings | `CotangentRegression`; `cotangent_operations_reject_wrong_objects_variances_and_points`, `cotangent_declarations_reject_malformed_contracts_with_specific_codes`, `smooth_endpoint_errors_name_the_failing_role` | Oracle `SmoothFibers` (`fiberVector_total` … `cotangentBackward_total`, `fiberVector_erasure`) |
| **M — metrics** | `SmoothDeclarations.lean` (`invert?`, `ldl?`, `certifyNondegenerate`, `certifyRiemannian`, `checkGram`), `IndexedMetricSource.lean`, `IndexedSmoothContracts.lean` (`metricFlatValid`, `metricSharpValid`) | `MetricFormRegression`; `metric_example_checks_builds_and_executes`, `metric_declarations_reject_malformed_metrics_and_evidence_with_specific_codes`, `metric_selection_is_explicit_and_unambiguous`, `differential_is_unchanged_by_metric_declarations` | Oracle `SmoothMetrics`, `SmoothMetricForms`, `SmoothMetricWeakening`; bridge `Metric`, `Accepted` |
| **R — reference** | `scripts/metric_free_reference.py`, `scripts/metric_reference.py`, `scripts/smooth_differential_reference.py`, `tests/fixtures/smooth-differential.json` | `VastitasAlgebraTest.SmoothReferenceRegression`; `scripts/test_smooth_differential_reference.py`, `scripts/test_metric_reference.py` | Tested only |
| **W — wire** | `IndexedDeclarationProtocol.lean`, `ResourceProtocol.lean` (smooth, fiber, tape and metric forms gated by protocol 9), `src/indexed.rs`, `src/frontend/indexed_parser.rs` | `smooth_forms_select_protocol_nine_and_older_envelopes_reject_them` and the object, cotangent and metric variants; `raw_wire_rejects_forged_smooth_records`, `raw_wire_rejects_forged_fiber_and_tape_records`, `raw_wire_rejects_forged_metric_records`, `tampered_acceptance_bodies_are_rejected_by_the_kernel`; the tampered-Core sections of the three kernel regressions | Tested only: raw-wire rejection is not a theorem |
| **L — standard library** | `stdlib/src/geometry/smooth/affine/mod.vast` (`std::geometry::smooth::affine`), `stdlib/src/geometry/metric/mod.vast` (`std::geometry::metric`), `stdlib/src/differential/` (package `vastitas_differential`, `std::differential`) | `tests/stdlib_differential.rs`: `library_profile_checks_builds_and_runs_from_a_path_package`, `mutated_observations_change_the_native_result`, `gradient_is_ordinary_code_over_the_metric_free_differential`, `a_library_gradient_can_take_neither_the_object_nor_sharp`, `smooth_operations_are_not_ambiguous_with_stage_one_geometry`, `library_objects_keep_their_identity_and_classification`, `geometry_package_does_not_depend_on_differential`, `metric_free_programs_need_no_metric_module`; `tests/examples.rs`: `stdlib_differential_package` (`examples/packages/stdlib/stdlib-differential/`) | Uses the same checker as application code |

The bridge proves what the runtime operations mean in mathlib:

- **Derivative correspondence.** `Derivative.lean` reads the kernel
  definitions. `evalAt_eq_eval` and `evalAt_eq_eval_evalPoint` make evaluation
  `MvPolynomial.eval`; `toMv_partial` makes `partialDerivative j` mathlib's
  `pderiv j`; `toMv_compose` makes `SmoothRuntime.compose` substitution
  (`aeval`); `cot_getD` makes component `j` of `cot map x η` equal to
  `Σᵢ ηᵢ (∂ⱼ fᵢ)(x)`.
- **Chain rule.** `ChainRule.lean`: `cot_compose` (proof: the formal chain
  rule `pderiv_aeval`), `eval_denote`, `backward_eq_cot`,
  `backward_eq_cot_saved`, `pullback_composite`, `pullback_eq_composite`,
  `smoothEqual_iff`, and the typed fragment `pullback_comp` and
  `Cov.reverse_eq_pullback` after PR #377.
- **Fréchet.** `Frechet.lean`: `hasFDerivAt_realProgram` (every program is
  differentiable; the composite node uses `HasFDerivAt.comp`),
  `realProgram_realPoint`, `reverse_covector_eq_comp_fderiv`,
  `pullback_eq_fderiv_adjoint`, `pullback_covector_eq_comp_fderiv` (both
  modes) and `pullback_getD_eq_fderiv_adjoint`. The file imports `Derivative`
  but not `ChainRule`.
- **Kähler.** `Kaehler.lean`: `kaehler_D_subst`, `kaehler_pullback_const`,
  `pullback_eq_kaehler_fiber`, `pullback_eq_pullbackForm_fiber`,
  `pullbackForm_compose` and `cot_compose_kaehler`, with
  `KaehlerPrerequisites.map_eq_pullbackForm` identifying `pullbackForm` with
  `KaehlerDifferential.map`. The file imports neither `ChainRule` nor
  `Frechet`.
- **Metrics.** `Metric.lean`: `isUnit_gram_of_nondegenerate`,
  `inverse_eq_of_nondegenerate`, `sharp_flat`, `flat_sharp`, `gradient_riesz`,
  `posDef_of_riemannian`, and the examples `not_isUnit_diag_one_zero`,
  `checkNondegenerate_diag_one_zero`, `not_posDef_lorentz`,
  `checkRiemannian_lorentz`, `checkNondegenerate_lorentz`.
- **Accepted Core.** `Accepted.lean`: `accepted_pullback_operands`,
  `accepted_differential_operands`, `accepted_sharp_operands`, and the six
  `checked_*` theorems of [bridge hypotheses discharged](#bridge-hypotheses-discharged).

`lean-bridge/Audit.lean` requires each of these names.

<a id="acceptance-conditions"></a>

## Acceptance conditions

The acceptance example is
[`examples/packages/geometry/smooth-differential/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/geometry/smooth-differential).
It checks, builds and prints `42`. Each observation has its own failure code
from 1 to 25, so a wrong result changes the output
(`mutated_observations_change_the_native_result`). "Code k" below is that
observation.

| Condition | Status and evidence |
| --- | --- |
| <a id="c1"></a>C1. Objects: `Affine(n)[c₁,…,cₙ]` declares one canonical smooth object; `Affine(K, n)[…]` is sugar for `spec[…] over K`; `E_SMOOTH` rejects implementation mismatches, a dimension other than the number of coordinates, `spec` under a smooth implementation and smooth globals | **Tested** (S): `smooth_declarations_reject_mismatched_forms_with_specific_codes` (`spec[t]` under `SmoothR`, `Affine(2)[t]`, `Affine(2)[t, t]`, `indexed global G(SmoothR)`, `Affine(1)[t]` under a presented implementation: `E_SMOOTH`; 16 coordinates accepted and 17 rejected, a dimension of 65 digits: `E_LIMIT`; `Affine(t)[t]`: `E_PARSE`); `SmoothObjectRegression` ("Affine(n) under a descriptor implementation", "a principal open under a smooth implementation", "forged smooth global"); `algebraic_affine_spelling_is_sugar_for_spec_over_a_base` (the wire record of `Affine(SpecQQ, 1)[t]` equals that of `spec[t] over SpecQQ`; a count mismatch is `E_AFFINE_COORDINATE`). **Proved (oracle)**: `SmoothDeclarations.smoothAffine_sound` (an accepted object has a smooth implementation and distinct coordinates within the generator limit) and `smooth_objects_are_declared` (in a valid environment every canonical object of a smooth implementation is an `Affine(n)[…]` declaration, so there is no smooth global). |
| <a id="c2"></a>C2. Disjointness and non-regression: smooth objects never index Stage 1 or Stage 2 families, and the reverse; `validAffine_sound`, `presented_not_descriptor` and `sealed_families_exclude_presented` keep their statements; `geometry_compat` still resolves `Affine(QQ, n)` and `Affine(CInfReal, n)` in function bodies | **Proved (oracle)**: `SmoothDeclarations.sealed_families_exclude_smooth` (the Stage 1 point and morphism families and the Stage 2 relative family never range over a smooth implementation), `smooth_families_exclude_foreign` (a smooth family ranges over smooth implementations only), `affineData_smooth_none`, `chainOf_smooth_none`, `smooth_not_presented`, `smooth_not_descriptor`. The three Stage 2 statements in `AffineDeclarations.lean` are unchanged: between `3a74c11` (the Stage 2 map's revision) and `c9a30ce`, the file only gains theorems. **Tested** (S): `smooth_and_presented_objects_stay_disjoint` (a smooth family over presented objects, a relative family over smooth objects, `Smooth<QLine, QLine>`, `Smooth<Line, QLine>` and `Affine(SpecQQ, 1)[t]` under `SmoothR` are rejected); the fiber, tape and metric-form families over presented objects (`E_TYPE`) in the cotangent and metric tests; `SmoothObjectRegression` ("smooth bindings reject the presented relative family", "relative bindings reject the smooth family"); `function_body_affine_spellings_still_use_the_geometry_compatibility_export` (`Affine(QQ, 20)` and `Affine(CInfReal, 22)` next to a smooth profile build and print `42`). With the standard library, `library_objects_keep_their_identity_and_classification` (`tests/stdlib_differential.rs`) rejects the library's smooth `Line` in the Stage 1 `Point` family and the Stage 1 base object in `Smooth` (`E_TYPE`). |
| <a id="c3"></a>C3. Maps: declared QQ-polynomial `Smooth<X, Y>`; `compose` builds a program node; `same` compares exact denotations; the #361 shears at the origin pull dx back to (1, 1) along B∘A and to (2, 1) along A∘B | **Tested** (S): `smooth_maps_resolve_source_coordinates_and_reject_variance_errors` (a foreign coordinate, target coordinates in an image and a missing image: `E_AFFINE_COORDINATE`; `t^17`: `E_LIMIT`; images written in any order are stored in target order); `objects_example_checks_builds_and_executes` and `mutated_object_observations_change_the_native_result`; codes 16 and 17; the reference cases "shear A at the origin" and their composites in `SmoothReferenceRegression`. **Proved (oracle)**: `SmoothDeclarations.smoothCompose_reifies` and `core_compose_reifies` (the value of `compose` is `Program.compose`, never the expanded composite); `SmoothPrimitives.smoothConstant_total`, `smoothCompose_total`, `smoothEqual_total`, `smoothComposite_total`; `SmoothCanonical.composite_wellTyped`; `SmoothCalculus.Regression.shear_correct_order`, `shear_reversed_order`, `shear_orders_differ`. **Proved (bridge)**: `ChainRule.smoothEqual_iff` (`same` is equality of the denoted polynomial maps), `Derivative.toMv_compose`. |
| <a id="c4"></a>C4. Roadmap identity: η = dt at g(f(3)) = 18; the pullback along g at (3, 9), then along f at 3, is 12 dt; it equals the pullback along the composite program, along the composite map as one primitive, and along the declared `gf`; the chain rule is proved | **Tested** (D): codes 1–5 (`smooth_example_checks_builds_and_executes`); the composite cases of `tests/fixtures/smooth-differential.json`. **Proved (oracle)**: `SmoothCalculus.cot_compose`, `eval_denote`, `backward_eq_cot`, `backward_eq_cot_saved`, `pullback_composite`, `pullback_eq_composite`, `Cov.pullback_comp` (mathlib-free, with `Lean.Grind.CommRing` and dual numbers); `SmoothRuntime.pullback_stepwise` and `pullback_stepwise_of_wellTyped` (the pass runs along each factor in reverse order at the intermediate point). **Proved (bridge)**, independently: `ChainRule.cot_compose`, `backward_eq_cot`, `pullback_composite`, `pullback_comp`; and `Kaehler.cot_compose_kaehler` by Kähler functoriality. |
| <a id="c5"></a>C5. Membership: the result lies in T*ₓ | **Tested** (D): codes 6 and 7. **Proved (oracle)**: `SmoothRuntime.pullback_mem` and `pullback_mem_of_wellTyped` (the result lies over x with `dim X` components); `SmoothFibers.cotangentPullback_total`; `SmoothReverse.core_cotangent_pullback` (the node's value has the checked type `Cotangent<X>`). **Proved (bridge)**: `checked_pullback_frechet` (the result lies over x with n components). |
| <a id="c6"></a>C6. Wrong seeds fail: a seed at 17 instead of 18 gives ⊥; a wrong intermediate basepoint propagates ⊥; a seed over the wrong object is a static `E_ENDPOINT` that names the expected and supplied objects | **Tested** (D, F): codes 8–11 (⊥ lies over nothing, survives the identity, and reads `(0, 0)`); `smooth_endpoint_errors_name_the_failing_role` ("pullback requires a seed with object Line (the map's target), but the supplied seed has object Plane", and the role messages of the other smooth, fiber and metric primitives); `acceptance_rejects_wrong_objects_and_a_gradient_primitive_statically`; `cotangent_operations_reject_wrong_objects_variances_and_points`. **Proved (oracle)**: `SmoothRuntime.pullback_wrong_point`, `pullback_none`, `fiberAt_none`, `fiberEqual_none_left`, `fiberEqual_none_right`, `component_none`, `component_ne_failure`. **Proved (bridge)**: `checked_pullback_frechet` (a seed over another point, or ⊥, gives ⊥). The static rejection is tested, not proved. |
| <a id="c7"></a>C7. Saved and recomputed forward values: the saved-tape pass, the recomputing pass and `backward(linearize(F, x), η)` agree; a tape from another point rejects the seed | **Tested** (D): codes 12, 13, 14 and 25 (code 25: the recomputing pass evaluates each outer map at its own forward point); `each_pullback_binding_lowers_to_its_own_mode`. **Proved (oracle)**: `SmoothRuntime.pullback_saved_eq_recomputed`, `backward_forward`, `forward_residual`, `record_output`, `backward_linearize`, `backward_foreign_seed`; `SmoothReverse.core_linearize`, `core_cotangent_backward`, `core_backward_linearize`; `SmoothCalculus.backward_eq_cot_saved`. **Proved (bridge)**: `ChainRule.backward_eq_cot_saved`; `Frechet.pullback_covector_eq_comp_fderiv` for both modes. |
| <a id="c8"></a>C8. The actual checked program: the reverse pass runs on the program value that checked Core builds, not on an expanded composite | **Proved (oracle)**: `SmoothDeclarations.smoothCompose_reifies` and `core_compose_reifies`; `SmoothReverse.core_cotangent_pullback` (an accepted node evaluates to `SmoothRuntime.pullback mode F x η` of its operand values) and `core_pullback_compose` (a pullback whose map operand is a Core `compose` node runs on `Program.compose`); `IndexedSemantics.primitive_runtime_erasure`. **Tested** (S, D): `smooth_programs_lower_to_the_shared_smooth_runtime` and `cotangent_programs_lower_to_the_shared_smooth_runtime` (generated code calls `SmoothRuntime.Program.compose` and `SmoothRuntime.pullback`); the native fixtures `smooth_programs` and `smooth_cotangent_programs` of `scripts/check_indexed_native.sh`. **Not claimed**: native refinement of the generated C. |
| <a id="c9"></a>C9. Identity: pullback along the identity is the identity | **Tested** (D): codes 10 and 15. **Proved (oracle)**: `SmoothRuntime.cot_identity`, `pullback_identity`; `SmoothCalculus.Cov.pullback_id`. |
| <a id="c10"></a>C10. Fréchet comparison: the runtime pullback, in both modes, is the adjoint of `fderiv ℝ` of the program's real function, through `HasFDerivAt.comp` and independently of the kernel chain rule | **Proved (bridge)**: `Frechet.hasFDerivAt_realProgram`, `realProgram_realPoint`, `reverse_covector_eq_comp_fderiv`, `pullback_eq_fderiv_adjoint`, `pullback_covector_eq_comp_fderiv`, `pullback_getD_eq_fderiv_adjoint`; for accepted Core, `Accepted.checked_pullback_frechet` and `checked_differential_frechet`. `Frechet.lean` does not import `ChainRule.lean`. |
| <a id="c11"></a>C11. Kähler comparison: the pullback is the fiber at x of Ω_{ℚ[Y]/ℚ} → Ω_{ℚ[X]/ℚ} in the `mvPolynomialBasis` bases | **Proved (bridge)**: `Kaehler.kaehler_D_subst`, `kaehler_pullback_const`, `pullback_eq_kaehler_fiber`, `pullback_eq_pullbackForm_fiber`, `pullbackForm_compose`, `cot_compose_kaehler`; `KaehlerPrerequisites.map_eq_pullbackForm`; for accepted Core, `Accepted.checked_pullback_kaehler`, which reaches programs through the kernel chain rule `ChainRule.backward_eq_cot`. `Kaehler.lean` imports neither `ChainRule.lean` nor `Frechet.lean`. |
| <a id="c12"></a>C12. Metric-free differential: dg = (2, 1) at (1, 2); adding or removing metric declarations changes neither the validity of any other binding (oracle) nor the generated code of a `differential` caller (byte identity) | **Tested** (M): code 18; `differential_is_unchanged_by_metric_declarations` (byte-identical generated Lean source with and without the metric, evidence, `flat` and `sharp` declarations, and both print `42`); the same check in `MetricFormRegression`. **Proved (oracle)**: `SmoothMetricWeakening.validPrimitiveBinding_metric_insertion_of_valid` and `evalPrimitive_metric_insertion_of_valid` (metric declarations at any position of a valid environment change neither the validity nor the value of any binding other than `flat` and `sharp`), `validPrimitiveBinding_metric_weakening`, `differential_metric_free`, `cotangentPullback_metric_free`; `SmoothReverse.smooth_differential_metric_free` (the semantics of `differential` and `cotangent_pullback` takes no environment). **Proved (bridge)**: `checked_differential_frechet`. Byte identity of generated code is tested, not proved. |
| <a id="c13"></a>C13. Gradient: `sharp_g(df)` needs a named metric and nondegeneracy evidence, even for the Euclidean metric; Euclid gives (2, 1), Skew (1, 0) and Lorentz (2, −1); two metrics give two gradients; sharp∘flat = id and dg(∇g) = g(∇g, ∇g); missing, wrong-kind, foreign and ambiguous evidence are rejected | **Tested** (M): codes 19–24; `metric_declarations_reject_malformed_metrics_and_evidence_with_specific_codes` (`flat` without `using =` and `sharp` without `evidence =`, for `Euclid` too: `E_PARSE`; Riemannian evidence and evidence for another metric: `E_METRIC`); `metric_selection_is_explicit_and_unambiguous` (two imports of `Skew`: `E_DUPLICATE`; a metric named by path is that metric); `acceptance_rejects_wrong_objects_and_a_gradient_primitive_statically` (there is no `gradient` contract); `tampered_acceptance_bodies_are_rejected_by_the_kernel`. **Proved (oracle)**: `SmoothMetricForms.sharp_requires_nondegenerate`, `sharp_rejects_riemannian`, `sharp_inverse_certified`, `flat_uses_declared_gram`, `metricFlat_total`, `metricSharp_total`, `flat_fiberAt`, `sharp_fiberAt`. **Proved (bridge)**: `Metric.gradient_riesz` (`sharp B α` is the unique `v` with `g(v, w) = α(w)` for every `w`; at `w = v` this is dg(∇g) = g(∇g, ∇g)), `sharp_flat`, `flat_sharp`; `Accepted.checked_gradient_riesz`, `checked_flat_sharp`. The gradient is application code in the library profile too: `std::differential` exports no `gradient`, because a library function can take neither the application's object nor its `sharp`. `a_library_gradient_can_take_neither_the_object_nor_sharp` pins the errors (**Tested**): an object-generic signature (`E_TYPE`, `invalid indexed annotation Smooth<X, Line>`), `let s = sharp_skew;` (`E_TYPE`, `expected an ordinary function; generic families are not Fn values`), a gradient wrapper used as a value (`E_TYPE`, `Fn values require scalar/Fn signatures; indexed and Pair functions are direct-call only`), a lambda (`E_TYPE`, `lambda signatures require scalar/Fn types`), and an `Fn` parameter over indexed types (`E_PROTOCOL`, `Fn signatures contain only scalars and recursive Fn types`). The roadmap sentence still holds: `sharp` requires named nondegenerate evidence, in the acceptance example and in the library example. |
| <a id="c14"></a>C14. Evidence: diag(1, 0) as nondegenerate is rejected (`E_METRIC`); diag(1, −1) is accepted as nondegenerate and rejected as Riemannian; asymmetric, wrong-size, non-constant and foreign-object metrics are rejected | **Tested** (M): `metric_declarations_reject_malformed_metrics_and_evidence_with_specific_codes` (asymmetric, three rows, a short row, a non-constant entry, `riemannian(Lorentz)`, evidence naming an object, `diag(1, 0)`, a metric on `QLine`: `E_METRIC`; an unknown coordinate: `E_AFFINE_COORDINATE`); the example's `LorentzInvertible`; `oversized_gram_entries_are_rejected_before_any_certificate` (`E_LIMIT` at `metricEntryBits`); `a_dense_metric_on_sixteen_coordinates_is_certified_within_the_bound`; `MetricFormRegression`; the 2 × 2 reference cases. **Proved (oracle)**: `SmoothMetrics.certifyNondegenerate_sound`, `certifyRiemannian_sound`, `checkGram_sound`, `zero_row_not_nondegenerate`, `diag_one_zero_rejected`; `SmoothMetricForms.metric_sound`, `nondegenerate_evidence_sound`, `riemannian_evidence_sound`. **Proved (bridge)**: `isUnit_gram_of_nondegenerate`, `inverse_eq_of_nondegenerate`, `posDef_of_riemannian`, `not_isUnit_diag_one_zero`, `checkNondegenerate_diag_one_zero`, `not_posDef_lorentz`, `checkRiemannian_lorentz`, `checkNondegenerate_lorentz`; `Accepted.checked_riemannian_posDef`. **Tested, not proved**: that `invert?` and `ldl?` find a certificate for every invertible or positive-definite Gram matrix. |
| <a id="c15"></a>C15. Wire: protocol 9 only; protocols 7 and 8 give `E_PROTOCOL`; forged wire and tampered Core are rejected | **Tested** (W): `smooth_forms_select_protocol_nine_and_older_envelopes_reject_them` (7 and 8: `E_PROTOCOL`; 2–6 rejected) and the object, cotangent and metric variants; `raw_wire_rejects_forged_smooth_records`, `raw_wire_rejects_forged_fiber_and_tape_records`, `raw_wire_rejects_forged_metric_records` (stored maps, tapes, fibers, inverses, factorizations and binding objects on the wire, unknown operations and modes: `E_PROTOCOL`; consistent but wrong data: the checker's own code); `tampered_acceptance_bodies_are_rejected_by_the_kernel`; the tampered-Core sections of `SmoothObjectRegression`, `CotangentRegression` and `MetricFormRegression`. Tested only. |
| <a id="c16"></a>C16. Independent reference: the kernel agrees with a fixture generated from `scripts/metric_free_reference.py` and `scripts/metric_reference.py` | **Tested** (R): `VastitasAlgebraTest.SmoothReferenceRegression` compares `SmoothRuntime` and `SmoothDeclarations` with `tests/fixtures/smooth-differential.json`, which `scripts/smooth_differential_reference.py` writes from the two references; `scripts/test_smooth_differential_reference.py` (`test_fixture_is_current` runs `--check`) and `scripts/test_metric_reference.py`. The references cover the real plane only: maps ℝ² → ℝ², functions ℝ² → ℝ and 2 × 2 Gram matrices. |
| <a id="c17"></a>C17. Library: `std::geometry::smooth::affine`, `std::geometry::metric` and `std::differential` are usable from a path package | **Tested** (L): `examples/packages/stdlib/stdlib-differential/` uses the three modules through the `std` path package and prints `42` natively (`library_profile_checks_builds_and_runs_from_a_path_package`, `stdlib_differential_package`). Its observations are the stepwise pullback 12 dt; the saved, recomputed and tape pullbacks agreeing; ⊥ for a seed at 17; dg = (2, 1); and the Skew gradient (1, 0) with flat(∇g) = dg. `mutated_observations_change_the_native_result` changes its output. The name audit (`smooth_operations_are_not_ambiguous_with_stage_one_geometry`): importing `compose`, `id`, `same`, `apply` or `Morphism` from `std::geometry::smooth::affine` is `E_NAME`, and a smooth map in a Stage 1 operation or the reverse is `E_ENDPOINT`. `library_objects_keep_their_identity_and_classification`: an application's own line is not the library's `Line`, Stage 1 and smooth objects do not index each other's families (`E_TYPE`), and `Metric` and `MetricSpace` are not `std::geometry::metric` names (`E_NAME`). `geometry_package_does_not_depend_on_differential`: the geometry package has no dependencies, and a reverse dependency is `E_CYCLE`. `metric_free_programs_need_no_metric_module`: a metric-free program runs with the metric module deleted. A program that depends on the std geometry package uses protocol 9. The public names: `std::geometry::smooth::affine` declares `SmoothR` (on the `CInfReal` marker of `std::geometry::smooth`), `CInfAffine`, `Smooth`, `Tape`, `Tangent`, `Cotangent`, `Pt = Affine(0)[]`, `Line = Affine(1)[t]`, `compose_smooth`, `composite`, `same_smooth`, `line_at`, `lies_over`, `tangent_over`, `same_covector`, `same_vector` and `pairing`; the smooth identity is the declaration form `= identity`. `std::geometry::metric` declares `MetricForm` only; metrics, evidence, `flat` and `sharp` stay in the application, next to the metric they name. `std::differential` exports `pullback` (saved), `differential`, `linearize` and `backward`; an application binds `cotangent_pullback(Smooth, Cotangent, recomputed)` over the std families. **Deviation from ADR 0001 §10**: `std::differential` does not export `gradient`; see C13 and [gaps](#gaps). `library_bindings_are_the_documented_operations` pins each public binding, including the saved mode of `pullback`; `library_fiber_and_map_operations_work_from_an_application` uses `tangent_over`, `composite`, `same_smooth` and `Tape`. |
| <a id="c18"></a>C18. Native: the example checks, builds and prints `42`; a mutation test flips each of its 25 codes | **Tested**: `smooth_example_checks_builds_and_executes`; `mutated_observations_change_the_native_result` (four groups of source mutations; a bitmask copy of the program maps code k to 2^(k−1), so each output names the failed set exactly; every code 1–25 is flipped by some group); the native fixtures `smooth_programs`, `smooth_cotangent_programs` and `smooth_metric_programs` of `scripts/check_indexed_native.sh`. **Assumed**: the Lean-to-C toolchain and the C compiler. **Not claimed**: performance. |
| <a id="c19"></a>C19. CI: green, with OS coverage recorded per job | The jobs that run the Stage 3 evidence: `ci.yml` "Rust formatting and lint" (ubuntu-latest: `cargo fmt`, `clippy`, `scripts/check_docs.py`, the Python reference tests); "Native compiler (ubuntu-latest, no mathlib)" and "Native compiler (macos-latest, no mathlib)" (kernel build, `check_kernel_regressions.sh`, `check_indexed_native.sh`, `cargo test`); "Lean proofs and axiom audit" (ubuntu-latest: `VastitasOracle`, the axiom audits, leanchecker replay); `lean-bridge.yml` "Daleckii–Krein proof and axiom audit" (ubuntu-latest: the bridge build, `Audit.lean`, leanchecker replay); `documentation.yml` "book" (ubuntu-latest). **Tested** (CI): batch 2 at `aca4ddf`, every job green: [CI](https://github.com/MGYamada/Vastitas/actions/runs/41833154471) (both native compiler jobs, both GEMM adapter jobs, Rust formatting and lint, Lean proofs and axiom audit), [Mathematical bridge](https://github.com/MGYamada/Vastitas/actions/runs/41833154215) and [Documentation book](https://github.com/MGYamada/Vastitas/actions/runs/41833154162). S9's pull request runs the same jobs. macOS bridge and oracle evidence is local only. |

<a id="bridge-hypotheses-discharged"></a>

## Bridge hypotheses discharged

The theorems of `Frechet.lean` are stated for a program well typed as
`ℝⁿ → ℝᵐ`, a point with `n` coordinates and a seed with `m` components. Those
of `Kaehler.lean` are stated for well-formed polynomial maps, one map or a
composable pair, not for programs; for a program, `Accepted.checked_pullback_kaehler` first reduces the reverse pass
to the cotangent map of the composite with `ChainRule.backward_eq_cot`, the
kernel chain rule. Those of `Metric.lean` are stated for a symmetric Gram
matrix and an inverse that nondegenerate evidence certifies. `Accepted.lean`
derives these properties from acceptance and from the operand-typing premise
described below:

- `checked_pullback_frechet`, `checked_pullback_kaehler` and
  `checked_differential_frechet` take an accepted Core node
  `.primitive id [operands…] result`: its binding (`found`), its operand and
  result types (`input`, `outputType`) and the checker's typing of the node
  (`Typing.HasType`). Acceptance fixes the operand types (`Smooth<X, Y>`,
  `Smooth<Pt, X>` and `Cotangent<Y>`), the binding's validity, a 0-dimensional
  point object and a 1-dimensional line. The value-level facts are what
  operand typing (`PrimitiveValuesHaveTypes`) means at those types. From both,
  through `accepted_pullback_operands` and `accepted_differential_operands`,
  the theorems derive that the map operand is a program well typed as
  `ℝⁿ → ℝᵐ`, that the point has `n` coordinates, that the seed is a covector
  with `m` components or ⊥, and that the line of a differential is
  1-dimensional. These hypotheses are therefore discharged up to operand
  typing.
- `checked_gradient_riesz` also takes `env.Valid`
  (`module.declarations.indexed.Valid`). It derives that the binding's metric
  is declared on an `n`-dimensional object, that its Gram matrix is
  symmetric, and that the evidence the binding names certifies the inverse
  that `sharp` applies (`accepted_sharp_operands`,
  `SmoothMetrics.checkNondegenerate_spec`).
- `checked_riemannian_posDef` and `checked_flat_sharp` take only `env.Valid`
  and the lookup of an evidence declaration. They are about declarations, not
  Core nodes.

Two premises stay, exactly as in the oracle's `core_*` theorems
(`SmoothReverse.core_cotangent_pullback` and its siblings):

- **operand evaluation**: each operand term evaluates, at some fuel, to a
  value (`eval module fuel values t = some v`); the conclusion is about the
  node at `fuel + 1`;
- **operand typing**: those values have the operand types
  (`PrimitiveValuesHaveTypes`).

These theorems are about one accepted node. Whole-term preservation,
`IndexedEvaluationSafety.evaluation_total_and_typed`, states that the
subterms of an accepted term evaluate to values of their types. It is not
composed with the theorems above, and it keeps its own premises: `CallReturns`
for every callee of the term, uniqueness of the term's allocated serials
(`unique`), their freshness in the world (`fresh`), a typed context
(`ContextHasType`) and a valid declaration set.

## Per-issue ledger

| Issue | Met by this profile | Open |
| --- | --- | --- |
| [#381](https://github.com/MGYamada/Vastitas/issues/381) `std::differential` | The finite pointwise part: cot(f)ₓ η = Jᵀη for exact QQ polynomial maps at rational points (C4–C9); identity and reversed composition with basepoint transport; ⊥ for a seed over another point and `E_ENDPOINT` for a seed over another object (C6); the Fréchet (C10) and Kähler (C11) comparisons as two distinct bridge theorems, for polynomial maps on ℝⁿ; a metric-dependent gradient and a metric-free differential (C12, C13). Of box 2, wrong basepoints and seeds, invalid map variance and forged wire or Core are rejected; the rule-related items are vacuous because there are no custom rules or non-polynomial primitives. | Box 1's forward-over-reverse HVP example and Weil lifts (#161); obligations 1 and 2 at module level (Ω¹_C∞(U) free on dxᵢ, Ω_{ℚ[x]} ⊗ C∞ ≅ Ω¹_C∞), Hadamard's lemma and Spec_∞; obligation 4 (there is no #285 manifest); custom rules (#163); closure-environment cotangents (#570). |
| [#361](https://github.com/MGYamada/Vastitas/issues/361) compiled pullbacks | The runtime part: a verified reverse pass over the program value that checked Core builds, with saved and recomputed forward values and a first-class tape (C7, C8); the noncommuting shears at the origin (C3); nonlinear composition at the intermediate point (C4); wrong basepoints and seeds (C6); identity (C9); the exact polynomial proof vehicle (C11) and the port of PR #377 (`SmoothCalculus.Cov`). | Compiler-emitted reverse Core, re-checked and translation-validated against cot(⟦f⟧) (#623, after #622); preservation through passes (#164); gluing (#606); the branch cases, which belong to #290 and #163; the universal C∞ differential. |
| [#290](https://github.com/MGYamada/Vastitas/issues/290) proof-carrying differentiation | A runtime analogue of the first required case g(x) = (x, x²), h(u, v) = u² + v, f(x) = 2x²: the stepwise and composite routes agree at every point and seed (`pullback_composite`), and the example observes 12 dt at x = 3 (C4); a residual from another basepoint is rejected (codes 9 and 14); the tape satisfies its residual relation (`forward_residual`), and its Fréchet meaning is proved (C10). | Every box: the theorem over generated `EvalForward`/`EvalBackward` Core, the derivation language, selected-backward and within contracts, the port of PR #287's cases, the mutation suite and the public acceptance-path proof. |
| [#264](https://github.com/MGYamada/Vastitas/issues/264) `std::geometry::metric` | For constant metrics on declared smooth affine objects: a named Euclidean metric with g₀♭, g₀♯ and g₀♯∘g₀♭ = id (code 23); the differential without a metric, unchanged when metrics are added or removed (C12); the gradient only through a selected metric and its evidence, with omitted, ambiguous and wrong-object metrics rejected (C13); diag(1, 0) and diag(1, −1) (C14); two metrics and two gradients of one df (code 22); vector/covector confusion is `E_ENDPOINT`, certificates never come from the wire, and the audit rechecks every metric copy (C15). | Position-dependent metrics and `IsSmoothManifold` bases; `signature`, `causal_kind` and orthogonal complements; the `DiagonalHermitianMetric` rename; a proof that `invert?`/`ldl?` succeed on every invertible or positive-definite form; a library `gradient` (#626). |
| [#103](https://github.com/MGYamada/Vastitas/issues/103) `Affine(n)` | The constructor half: `Affine(n)[…]` declares one canonical smooth real affine space, `Affine(K, n)[…]` is sugar for `spec[…] over K`, and the form selects the meaning (C1). | Box 1 only partly: a declaration still names its implementation (`SmoothR`); the function-body `Affine(n)` builtin is unchanged; reconciling `CInfAffine` with the Stage 1 `CInfScheme` remains. Boxes 2–7 (gluing) moved to #606. |
| [#163](https://github.com/MGYamada/Vastitas/issues/163) custom rules | Only the ambient-derivative contract for admitted QQ polynomial primitives, whose derivative is the formal Jacobian proved equal to `fderiv` (C10). | Every box: rule registration, delegation and revocation, provenance, within and selected-backward contracts. |
| [#360](https://github.com/MGYamada/Vastitas/issues/360) no manifold type | The decision, recorded in ADR 0001 §10: smooth objects are `Affine(n)` declarations with a sealed classification, and there is no `Manifold` type. The issue is closed. | `IsSmoothManifold` evidence and gluing (#606). |

<a id="gaps"></a>

## Gaps

- **Runtime interpretation cost of the reverse pass.** A generated program
  carries a `SmoothRuntime.Program` tree and interprets it with exact `Rat`
  list arithmetic. Each saved-mode pullback runs the forward pass and builds a
  tape; the recomputing mode evaluates every forward value again; partial
  derivatives are formed at run time on every call. No derivative code is
  compiled. `same` and `composite` expand the composite at run time, without a
  budget, and its degree can grow exponentially with the depth of the program.
  None of this is measured.
- **Tape retention.** A `Tape` keeps the input, the output and every step
  (map and input point) as an immutable value for as long as the value lives.
  It records none of the residual metadata of
  [storage ownership §7.10](storage-ownership.md#710-reverse-residual-retention-and-mutation):
  no retention strategy (retain, snapshot or recompute), no value versions and
  no invalidation. Tapes are pure values outside the storage checker.
- **Certificate search.** That `invert?` and `ldl?` find a certificate for
  every invertible or positive-definite Gram matrix is tested, not proved.
  Soundness does not depend on it, because the kernel checks every
  certificate again. An incomplete search would reject a valid metric with
  `E_METRIC`.
- **Rust parsing** is Assumed. The kernel re-checks every declaration, but
  parser fidelity is tested only.
- **Static basepoint rejection** is not done. Points are runtime values of
  `Smooth<P, X>`, so a seed over another point of the right object gives ⊥ at
  run time. Only the object and the variance are checked statically.
- **No compiled reverse Core.** The compiler emits no reverse Core, so nothing
  re-checks or translation-validates a backward program. The follow-up is
  #623, after the primitive descriptors of #622.
- **Performance** is not claimed (#222).
- **No library gradient.** ADR 0001 §10 assigns `gradient` to
  `std::differential`, but the library does not export it (C13, C17). A
  library function cannot be generic over the application's smooth object,
  because the smooth families take declared objects only, and it cannot take
  a metric, evidence or `sharp` as a parameter. Closing the gap needs
  object-polymorphic signatures over canonical objects, and metric, evidence
  or `sharp` parameters ([#626](https://github.com/MGYamada/Vastitas/issues/626)).
- **Reference coverage.** The Python references cover dimension 2 only;
  dimensions 3–16 have no independent reference.
- **Composition with whole-term preservation** is not proved; see
  [bridge hypotheses discharged](#bridge-hypotheses-discharged).

<a id="proof-boundary"></a>

## Proof boundary

- **Proved (oracle).**
  - Each smooth declaration, primitive and evidence checker establishes its
    stated exact facts.
  - The smooth, fiber, tape and metric primitives are total and typed, and
    erase to the runtime.
  - The structural runtime facts: saved and recomputed passes agree, ⊥ is
    absorbing, results lie over the input point, identity and stepwise
    composition.
  - The chain rule for programs, without mathlib (`SmoothCalculus`).
  - The reverse pass on accepted Core runs on the program node.
  - Metric declarations at any position leave every other binding unchanged.
  - Stage 1 and Stage 2 non-regression.
- **Proved (bridge).** The derivative correspondence, the chain rule, the
  Fréchet comparison, the Kähler comparison and the meaning of metric
  evidence. `Accepted.lean` states the Fréchet and Kähler comparisons, the
  gradient (Riesz) for accepted Core nodes, and metric evidence for valid
  declarations.
- **Tested only.**
  - Raw-wire and tampered-Core rejection, and protocols 7 and 8.
  - Parser fidelity and diagnostic messages, including the `E_ENDPOINT`
    roles.
  - Byte identity of generated code with and without metrics.
  - Native execution of the compiled example and its mutations.
  - Agreement with the Python references.
  - Completeness of `invert?` and `ldl?`.
- **Assumed.**
  - The Rust frontend's parsing.
  - The Lean-to-C toolchain and the C compiler.
  - Lean core `Rat` and GMP.
  - mathlib itself.

<a id="not-claimed"></a>

## Not claimed

- Compiled reverse AD: reverse Core emitted, re-checked and
  translation-validated (#361, #290, #164).
- C∞-ring mathematics (#381 obligations 1, 2 and 4 at module level): Ω¹_C∞ as
  a module, Hadamard's lemma and Spec_∞.
- Differentiating Int or Nat arithmetic or branches; pair and fan-out
  combinators.
- Non-polynomial primitives (exp, sin, division), within-derivatives,
  selected-backward rules and custom rules (#163).
- Forward mode, Weil lifts and HVP (#161, #381); checkpointing beyond save-all
  and recompute-all (#544); complex AD (#71); closures (#570).
- Submanifolds, smooth opens, gluing, ℝP¹, `IsSmoothManifold` and the
  `CInfScheme` classification (#103 residual, Stage 7).
- Position-dependent metrics, signature algebra, Levi-Civita, Hodge (#375),
  and the `DiagonalHermitianMetric` rename (#264).
- Irrational points, floats, native refinement and performance (#222).

## Validation

Batch 2 (S4–S8 and the `E_ENDPOINT` roles) and S9 were each validated
locally, one step at a time, on a 16 GiB machine, before their CI runs (C19).
The commands:

- `cargo fmt --check`, `cargo clippy --locked --all-targets -- -D warnings`
  and `cargo test --locked --all-targets --no-fail-fast` (batch 2: 517
  passed; S9: 528 passed; none failed).
- `lake -d lean-kernel build` with every library, executable and regression
  library; `bash scripts/check_kernel_regressions.sh`;
  `bash scripts/check_indexed_native.sh`.
- `lake -d lean build VastitasOracle` and
  `(cd lean && lake env lean -DwarningAsError=true ../scripts/audit_axioms.lean)`.
- `(cd lean-bridge && lake build)` and
  `(cd lean-bridge && lake env lean Audit.lean)` (1054 declarations); from the
  repository root, `bash scripts/replay_lean.sh lean-bridge VastitasBridge`
  (one thread; about 50 s and 2.9 GB).
- `python3 scripts/check_boundaries.py` and
  `python3 -m unittest discover -s scripts -p 'test_*.py'`.
- `python3 scripts/check_docs.py`, `mdbook build` and
  `python3 scripts/check_book.py`.

CI also runs `lake -d lean env python3 scripts/check_axiom_audit.py` and the leanchecker replay
of the oracle and the kernel.
