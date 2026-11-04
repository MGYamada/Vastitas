# Historical Stage 2 finite affine geometry acceptance map

This map links each acceptance condition of historical Stage 2 to its
implementation, positive and negative tests, oracle and bridge theorems, and
native evidence. Stage 2 is a finite, checked profile of ordinary affine
geometry over QQ ([tracker #571](https://github.com/MGYamada/Vastitas/issues/571)).
It does not include performance: the Fast like C verdict stays with #183 and
#222, for Stage 3 or later. The user guide is
[presented affine geometry](affine-geometry.md).

## Scope and revision ledger

The conditions are the acceptance list of #571, which turns the Stage 2 examples
of the [historical roadmap](guide/historical-roadmap.md) into executable checks.
The decisions behind the profile are:

- **Wire.** Algebraic forms are fields of protocol 9 only, the current schema
  epoch of #533. Protocols 7 and 8 reject them, and there is no protocol 10.
- **Identity (#23/#24).** One declaration is one canonical object. Separately
  declared presentations are compared only through a checked isomorphism, and
  `Affine(n)` keeps its generative identity.
- **Non-regression (#385).** The two-index `Morphism`/`same_base` and
  `GeometryProfile` contracts are unchanged. Morphisms over a base are a separate
  three-index `relative` family.
- **Dependencies.** The mathlib bridge requires the kernel and the oracle by
  path, one way only. The kernel and the oracle stay mathlib-free.

| Step | Pull request | Merge into `main` |
| --- | --- | --- |
| S1: exact QQ polynomial core and verified Gröbner bases | [#572](https://github.com/MGYamada/Vastitas/pull/572), landed by [#580](https://github.com/MGYamada/Vastitas/pull/580) | `5d58a65` |
| S2–S6: declarations, protocol-9 surface, morphisms, fiber products, principal opens; budgeted substitution | [#584](https://github.com/MGYamada/Vastitas/pull/584) (with #576, #577), landed by [#589](https://github.com/MGYamada/Vastitas/pull/589) | `55949b8` |
| S7: Buchberger's criterion and canonical normal forms in the bridge | [#587](https://github.com/MGYamada/Vastitas/pull/587), landed by [#589](https://github.com/MGYamada/Vastitas/pull/589) | `55949b8` |
| S8a: kernel polynomials, division and verified bases in mathlib | [#590](https://github.com/MGYamada/Vastitas/pull/590) | `8f0da2c` |
| S8b: presentations, morphisms, dual numbers, fiber products and principal opens in mathlib | [#592](https://github.com/MGYamada/Vastitas/pull/592) | `ae644bb` |
| S9: `std::geometry::scheme::affine`, this map | this change | — |

Status terms below:

- **Proved (oracle)** is a theorem about kernel data and `Poly` operations in
  `lean/VastitasOracle/`, about the exact checker that accepts the input.
- **Proved (bridge)** is a mathlib theorem in `lean-bridge/`.
- **Tested** is a regression or integration test, including native execution.
  Testing is not a proof of all inputs.
- **Assumed** is a trusted component listed in the last section.

## Evidence key

Kernel regressions are in `lean-kernel/VastitasKernel/` unless noted, and run
from `scripts/check_kernel_regressions.sh`. Rust tests are in
`tests/affine_geometry.rs` unless noted. Oracle files are in
`lean/VastitasOracle/`.

| Key | Implementation | Tests | Oracle theorems |
| --- | --- | --- | --- |
| **A — exact algebra** | `AlgebraRuntime.lean` (degLex `Poly`, division, `Map`), `AlgebraBasis.lean` (budgeted Buchberger with cofactors, independent `verify`, budgeted `substitute`/`reduce`/`compose`) | `VastitasAlgebraTest/BasisRegression.lean` against the independent model `scripts/affine_algebra_reference.py` and `tests/fixtures/algebra-bases.json`; `degree_and_digit_boundaries_are_accepted`; budget cases in `AffineMorphismRegression` | `AlgebraBasis.verify_sound`, `certify_sound` (`CertificateValid`); `substitute_ok`, `reduce_ok`, `compose_ok`, `divide_ok` (a successful budgeted run equals the unbudgeted result) |
| **O — objects and bases** | `AlgebraDeclarations.lean`, `Indexed.lean` (`presentedAffine`, `structural`, base chains), `IndexedAlgebraSource.lean` | `AffineDeclarationRegression`; `affine_example_checks_builds_and_executes`, `structural_applications_follow_declared_base_chains`, `affine_source_rejections_are_specific` | `AffineDeclarations.validAffine_sound`, `checkAffine_sound`, `chainOf_spec`, `structural_holds`, `presented_not_descriptor`, `sealed_families_exclude_presented` |
| **M — morphisms over a base** | `IndexedPrimitives.lean` (`relativeConstant`, `relativeCompose`, `relativeView`, `relativeEqual`, `relativeCoefficient`, `relativeIntPoint`), `IndexedSemantics.lean`, `IndexedCodegen.lean` | `AffineMorphismRegression`; `morphism_declarations_reject_relation_variance_base_and_type_errors`, `mutated_observations_change_the_native_result` | `AffineMorphisms.relativeConstant_sound` (`MorphismValid`), `checkRelations_ok`, `checkTriangle_ok`, `compose_images`, `view_requires_chain`, `same_iff`; `IndexedSemantics.relativeConstant_total` … `relativeIntPoint_total`, `primitive_total_and_typed`, `primitive_runtime_erasure` |
| **F — fiber products and evidence** | `Construction.fiber`, `fiberPresentation`, `checkIso`; `relativePair`, `relativeIso`, `relativeCartesian` | `AffineFiberRegression`; `fiber_products_reject_unchosen_bases_non_isomorphisms_and_forged_squares`, `fiber_and_evidence_records_reject_forged_wire` | `AffineFibers.checkConstruction_fiber`, `cartesian_sound`, `composesTo_sound`; `IndexedSemantics.relativePair_total` |
| **P — principal opens** | `Construction.localization`, `localizationPresentation`, `restrict` | `AffineOpenRegression`; `principal_opens_and_restrictions_reject_non_preimages_and_non_isomorphisms` | `AffineFibers.checkConstruction_localization` |
| **W — wire and protocol** | `IndexedDeclarationProtocol.lean`, `ResourceProtocol.lean` (algebraic forms gated by protocol 9), `src/indexed.rs`, `src/frontend/indexed_parser.rs`, `src/packages.rs` | `affine_forms_select_protocol_nine_and_older_envelopes_reject_them`, `raw_wire_rejects_forged_affine_records`, `relative_forms_reject_downgrade_and_forged_wire`, `fiber_and_evidence_records_reject_forged_wire` | Tested only: raw-wire rejection is not a theorem |
| **L — standard library** | `stdlib/src/geometry/scheme/affine/mod.vast` | `tests/stdlib_geometry.rs`: `presented_affine_geometry_is_usable_from_the_library` and the protocol-9 captures | Uses the same checker as application code |

The bridge proves what the kernel's identities mean in mathlib:

- **S7 (proved).** In `VastitasBridge.AlgebraicGeometry.Buchberger`:
  - `isGroebnerBasis_of_sPairReduces`: Buchberger's criterion, over any field and monomial order;
  - `normalForm_unique`, `sub_mem_iff_normalForm_eq`, `mem_iff_normalForm_eq_zero`: canonical normal forms;
  - `span_eq_of_cofactors` and `list_isGroebnerBasis_of_certificate`: the kernel certificate's shape;
  - `degLex_lt_iff_exists`: mathlib's degLex also makes coordinate 0 most significant.
- **S8a (proved).** In `VastitasBridge.AlgebraicGeometry.Kernel`, reading the actual kernel and oracle definitions:
  - `canonicalEquiv`: canonical kernel polynomials of arity `n` correspond to `MvPolynomial (Fin n) ℚ`, with the degLex order (`compare_lt_iff`) and arithmetic (`toMv_add`, `toMv_mul`, `toMv_sPolynomial`);
  - `divide_spec` and `normalForm_spec`: kernel division keeps its quotient identity, its fuel always suffices (`encode_lt`), and normal forms are canonical and fully reduced;
  - `verify_isGroebnerBasis`: a successful `verify` proves that the stored basis is a Gröbner basis of the relation ideal;
  - `verify_normalForm_eq_iff` and `verify_mem_iff`: equal normal forms exactly when two polynomials are congruent modulo the relations, and ideal membership exactly when the normal form is zero.
- **S8b (proved).** About kernel data that `verify`, `checkAffine` and `checkConstruction` accepted:
  - *Presentations:* `toMv_subst` (kernel substitution is `aeval`), `Presented`, `Verified.normalForm_eq_iff`, `verified_of_validAffine`.
  - *Morphisms:* `pullbackHom` (the `AlgHom`), `pullbackHom_compose` and `specMap_compose` (#362), `images_eq_iff` (`same` decides equality of ring maps), `MorphismValid.bridge`, `pullbackHom_triangle`.
  - *Dual numbers:* ε ≠ 0 and ε² = 0 in `ℚ[e]/(e²)` (`relationIdeal_dual`), `p_ne_q`, `closedPoint_comp`, `spec_base_eq`.
  - *Principal opens:* `equivAway` (`Localization.Away f`), `range_comap_toL` (image `D(f)`), `specMap_preimage_basicOpen`.
  - *Fiber products:* `Fiber.isPushout`, `Fiber.isPullback`, `isoTensor` (`A ⊗[R] B`), `specMap_pair` (`pair` is `pullback.lift`).
  - `certificate_of_checkConstruction`: accepted fibers and principal opens have exactly these presentations.

## Acceptance conditions

The acceptance example is
[`examples/packages/affine-geometry/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/affine-geometry).
It checks, builds and prints `42`, and every observation below contributes a
distinct failure code, so a wrong result changes the output
(`mutated_observations_change_the_native_result`).

| Condition | Status and evidence |
| --- | --- |
| 1. In D = QQ[e]/(e²), ε ≠ 0 and ε² = 0 | **Tested** (A): the basis `[e²]` in `BasisRegression` and the example's coefficient observation `eps(p()) = 1`. **Proved (oracle)** that the accepted basis satisfies its certificate. **Proved (bridge)**: ε ≠ 0 and ε² = 0 in `ℚ[e]/(e²)` (`relationIdeal_dual`). |
| 2. `p: t ↦ ε` and `q: t ↦ 0` are different D-valued points, equal after composing with the closed point | **Tested** (M): the example's `!same(p(), q())` and `same(compose(p(), closed()), compose(q(), closed()))`, natively and in `presented_affine_geometry_is_usable_from_the_library`. **Proved (oracle)**: `same_iff` compares exact normal-form images, and `compose_images` fixes the written order. **Proved (bridge)**: `p_ne_q`, `closedPoint_comp`, and `spec_base_eq` (equal underlying continuous maps). |
| 3. Variance: `compose(sq, shift)` is (t + 1)² and `compose(shift, sq)` is t² + 1 | **Tested** (M): slope observations in the example and the `compose` regression in `AffineMorphismRegression`. **Proved (oracle)**: `compose_images` (pullback substitutes `before` into `after`). **Proved (bridge)**: `pullbackHom_compose` and `specMap_compose`. |
| 4. The fiber of X = Spec QQ[t, x]/(x² − t) over t = 0 is isomorphic to Spec D | **Tested** (F): the basis `[x², t]` in `AffineFiberRegression` and the example's `cartesian fiberIsDual`. **Proved (oracle)**: `checkConstruction_fiber` (the stored presentation is derived from the factors) and `cartesian_sound` (the declared inverse composes with `pair` to the identity both ways). **Proved (bridge)**: `Fiber.isPushout`, `Fiber.isPullback` and `isoTensor`. |
| 5. Universal property: the projections of `pair(toX, toOrigin)` recover both arrows | **Tested** (F): the example's `same(compose(prX(), lift(toX(), toOrigin())), toX())` and `fiberX` observations. **Proved (oracle)**: `relativePair_total` and runtime erasure to `Map.pair`. **Proved (bridge)**: `specMap_pair`. |
| 6. The triangle `structure ∘ toX = structure` over S | **Tested** (M): the example's `same(compose(toS(), toX()), dsToS())`; forged triangles rejected in `AffineMorphismRegression`. **Proved (oracle)**: `relativeConstant_sound`, whose `MorphismValid` includes the commuting triangle with both stored structure maps. **Proved (bridge)**: `pullbackHom_triangle`. |
| 7. Principal opens D(f) = Spec A[u]/(uf − 1) and `restrict(φ)` give A_f → B_φ(f) | **Tested** (P): D(t), `restrict(t ↦ t²)` with u ↦ v, the open inclusion, the #104 transition D(x) ≅ D(y) and D(0) as the zero ring, in `AffineOpenRegression` and the example. **Proved (oracle)**: `checkConstruction_localization`. **Proved (bridge)**: `equivAway`, `range_comap_toL` and `specMap_preimage_basicOpen`. |
| 8. Rejections | **Tested**, each with its specific code:<br>• diagrams over separately declared bases, and `fiber(X, Origin2)` without an isomorphism: `E_AFFINE_BASE`;<br>• swapped variance and foreign coordinates: `E_AFFINE_COORDINATE`;<br>• relation violations and forged inverses: `E_AFFINE_RELATION`;<br>• missing structure maps: `E_AFFINE_BASE`;<br>• base mismatches in types: `E_TYPE`;<br>• Stage 1 `Scheme` and `CInfScheme` objects as `Over` indices: `E_TYPE` (`presented_affine_geometry_is_usable_from_the_library`);<br>• algebraic forms in protocol 7 or 8: `E_PROTOCOL`;<br>• forged Core and wire: the tampered cases in every affine regression and the raw-wire tests;<br>• limits: 16/17 generators, degree 16/17 and 32/33 relations, and the work budget, including substitutions whose expansions are huge: `E_LIMIT`. |
| 9. Accepted comparison: `fiber(X, Origin2) via(t -> t) inverse(t -> t)` | **Tested** (F): `Fiber2` in the example and `AffineFiberRegression`, with a non-isomorphic base map rejected. **Proved (oracle)**: `checkConstruction_fiber`, including the composed right structure images. **Proved (bridge)**: `certificate_of_checkConstruction`. |
| 10. Non-regression of the two-index `Morphism`/`same_base` and `GeometryProfile` contracts | **Proved (oracle)**: `presented_not_descriptor` and `sealed_families_exclude_presented`; the `GeometryCompatibility` theorems still hold. **Tested**: every pre-existing test, including the stdlib geometry suite, which now runs on protocol 9. |

## Proof boundary

- **Proved (oracle).**
  - Each declaration, primitive and evidence checker establishes its stated
    exact facts.
  - Chain invariants hold.
  - Successful budgeted operations equal the pure ones.
  - Accepted certificates satisfy their cofactor identities and reduce every
    relation and S-pair to zero.
  - The new primitives are total and typed, and erase to the runtime.
  - Two-index non-regression.
- **Proved (bridge).** S7, S8a and S8b above. The normal forms the kernel
  compares are canonical in `MvPolynomial (Fin n) ℚ`, so exact equality of
  stored images is equality in the presented ring.
- **Stated hypothesis (bridge).** The fiber and principal-open theorems assume
  that the factors' structure images are canonical. The kernel's `checkImage`
  enforces this, but the oracle's `StructureValid` does not record it.
  `structureValid_bridge` derives the relation part.
- **Tested only.**
  - Raw-wire rejection of protocols 7 and 8.
  - Parser fidelity.
  - Native execution of the compiled example.
  - Agreement with the Python reference model.
- **Assumed.**
  - The Rust frontend's parsing.
  - The Lean-to-C toolchain and the C compiler.
  - Lean core `Rat` and GMP.
  - mathlib itself.
- **Not claimed.**
  - Performance.
  - ZZ and F_p coefficients, and the #385 `Spec(F_p) → Spec(Z)` example (#251–#253).
  - Gluing and ℙ¹ (#104, #151).
  - CInfSpec (Stage 3).
  - Modules and Ω (#259, #261, #381).
  - Objects and ring elements created at runtime.
  - Generic functions and existentials over presented objects.

## Validation

Each pull request above records its commands and results:

- Local validation of the S2–S7 integration:
  [#589](https://github.com/MGYamada/Vastitas/pull/589#issuecomment-6620973377).
- The commands are those of [validation](development/validation.md): kernel and
  oracle builds, the axiom audit and its coverage check, leanchecker, kernel
  regressions, indexed native tests, the Python scripts, docs and book checks,
  and `cargo fmt`, `clippy` and `test`.
- The bridge additionally runs its build, `Audit.lean` and leanchecker.
