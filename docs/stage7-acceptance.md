# Stage 7 gluing acceptance

This map links each acceptance condition of historical Stage 7 to its
implementation, positive and negative tests, oracle and bridge theorems, and
native evidence. Stage 7 is a finite, checked profile of gluing two charts:
over QQ in the Zariski site of the presented objects of Stage 2, and over ℝ
in the smooth site of the smooth objects `Affine(n)[…]` of Stage 3
([tracker #878](https://github.com/MGYamada/Vastitas/issues/878)). It is the
first stage under the Fast like C rule of
[#877](https://github.com/MGYamada/Vastitas/issues/877), whose four entries
the section [Fast like C](#fast-like-c) states.

The Reference chapter is [Gluing declarations](language/gluing.md), the
guide chapter is [Gluing charts](guide/gluing.md), and
[Verification boundaries](verification.md#gluing-two-charts) states the
proof boundary. [Gluing forms](protocol.md#gluing-forms) gives the records
of the wire, and the [`E_GLUE` row](appendix/diagnostics.md#e-glue) of
Appendix B the code of the profile.

Conditions C1–C12, C14 and C17 have tested evidence and oracle theorems.
C15 has the bridge theorems of covers and separation witnesses; the glued
scheme and the manifold of real points in Mathlib are Planned (#879). C13 is
tested in part. C16 adds no library module; the library module is the
follow-up #882. C18 records the check time of the acceptance package. C19 and C20,
the continuous integration and the independent whole-stage review, are
Planned and are recorded here when they happen.

## Scope and decisions

The conditions are the checklist C1–C20 of #878, which turns the Stage 7
example of the
[historical roadmap](guide/historical-roadmap.md#stage-7-broader-geometry-and-physics)
into executable checks. The tracker fixed these choices:

1. The implementation of the charts chooses the site: a presented
   implementation the Zariski site, a `smooth_affine` implementation the
   smooth site. Nothing converts between the sites.
2. A cover is certified by a unit-ideal identity Σ aᵢ fᵢ = 1. In the smooth
   site the same identity certifies that the cozero sets cover the real
   points; a cover without such an identity, such as D(x² + 1) of the real
   line, is out of scope (#237).
3. Exactly two charts. Three or more need cocycle conditions on triple
   overlaps (#151).
4. A successful gluing proves neither separation nor the manifold property.
   Each is a separate claim with an exact witness.

The delivered forms depart from the plan of the tracker in three places:

- The tracker planned `glue(X₁, X₂) along e`, with an `indexed iso e`
  between principal opens. The delivered form
  `glue(U1, U2) by(…) inverse(…)` gives the chart transition and its inverse
  in the declaration and checks them as an isomorphism between the two
  opens. A transition that is not invertible is `E_GLUE`, not
  `E_AFFINE_RELATION` through an iso.
- The smooth transitions of C7 are the transitions of `glue` in the smooth
  site, not smooth maps between smooth opens with an `indexed iso`. A smooth
  open is an open of a gluing or a cover and nothing else; elsewhere it has
  the error of the place that names it (`E_SMOOTH` as the source of a smooth
  map, `E_AFFINE_BASE` as a base, `E_TYPE` in a function body).
- A glued object of the smooth site is a declaration of its own kind. It is
  not a `CInfScheme` descriptor object of the core, which the roadmap's
  acceptance example names.

### Roadmap sentences

| Roadmap sentence | Conditions |
| --- | --- |
| Choose the site | C6, C10 |
| Certify a cover | C5 |
| Check that local data agree on overlaps | C1, C7, C8 |
| Glue two algebraic affine lines along their punctured Zariski opens by y = 1/x and exhibit an isomorphism with the projective line over K | C1, C3, C4, with K = QQ |
| Gluing the corresponding smooth opens gives a `CInfScheme` | C6, C8, as a glued object of the smooth site |
| Identifying the real projective line as a smooth manifold requires additional evidence | C9 |
| Swapping the sites or using a map without a certified inverse must fail | C1, C10 |
| A further physics library would have to specify the numerical realization and the physical meaning of any reported observation | Not claimed |

### Steps

| Step | Scope | Status |
| --- | --- | --- |
| S0 | The tracker #878 and the plan #877 | Issues |
| Batches 1 and 2 | The kernel checks and regressions, the Rust parser and wire, the oracle theorems, the acceptance program and its rejected packages, the bridge theorems and the book | This change |
| Review | The independent whole-stage review ([C20](#c20)) and the fixes of its findings | Planned |

### Status terms

- **Proved (oracle)** is a theorem in `lean/VastitasOracle/`, mathlib-free,
  about the kernel's definitions.
- **Proved (bridge)** is a mathlib theorem in `lean-bridge/`.
- **Tested** is a regression or integration test, including native execution.
- **Assumed** is a trusted component, listed under
  [proof boundary](#proof-boundary).
- **Not claimed** is outside this profile.
- **Planned** has no evidence yet.

## Evidence key

Kernel files are in `lean-kernel/VastitasKernel/`, and kernel regressions run
from `scripts/check_kernel_regressions.sh`. Oracle files are in
`lean/VastitasOracle/`, and bridge files in `lean-bridge/VastitasBridge/`;
oracle names are relative to `VastitasOracle`, and the bridge theorems are in
`VastitasBridge.AlgebraicGeometry.Kernel.Gluing`. The Rust tests are in
`tests/gluing.rs` unless a row names another file. The examples of the
Reference and guide chapters are tested evidence too: `tests/examples.rs`
builds and runs `examples/packages/projective-line/`
(`book_programs_print_their_output`: it shows `failures = 0` and exits with
status 0) and checks the seven rejected packages
`examples/reject/packages/gluing-*` against their `.stderr` files
(`book_rejected_packages_print_their_diagnostics`). The rows below cite them
as "book reject".

| Key | Implementation | Tests | Theorems |
| --- | --- | --- | --- |
| **G — gluing checks** | `GluingDeclarations.lean` (`checkTransition`, `checkOverBase`, `checkCover`, `tensorImages`, `checkSeparation`, `homogeneous`, `checkProjectiveChart`, `checkProjectiveOverlap`), `GluingValidity.lean` (`site?`, `openData?`, `chartData?`, `open?`, `checkSmoothOpen`, `baseImages?`, `checkGlued`, `coverObject?`, `checkCover`, `checkSeparated`, `checkManifold`, `baseFree`, `checkProjective`), `IndexedValidity.lean` (`Entry.Valid`) | `GluingRegression`; `tests/gluing.rs` | Oracle `Gluing` |
| **S — elaboration** | `IndexedGluingSource.lean` (`elaborateSmoothOpens`, `requireOpen`, `transitionImages`, `witnessOf`, `requireGlued`, `elaborateGlued`, `elaborateCover`, `elaborateProjectiveChart`, `elaborateGluing`), `IndexedSourceChecker.lean` (two opens), `IndexedFunctionState.lean` (no value) | `stage7_rejections_have_their_codes`, `a_stage7_declaration_is_not_a_value` | — |
| **V — wire** | `IndexedDeclarationProtocol.lean` (`declarationBody`: `glued`, `cover`, `separated`, `manifold`, `projective`, `affine_localization`; `binding`, `smoothDimension`), `src/frontend/indexed_parser.rs` (`indexed_glued`, `indexed_cover`, `indexed_witness`, `indexed_dimension_literal`, `indexed_projective`), `src/indexed.rs` (`DeclarationBody::Glued`, `Cover`, `Separated`, `Manifold`, `Projective`, `ProjectiveChart`) | `the_stage7_forms_serialize_to_their_records`, `stage7_syntax_errors_are_reported`, `forged_stage7_records_are_rejected_by_the_kernel` | Tested only |
| **W — weakening** | — | `stage7_declarations_leave_the_generated_code_unchanged` | Oracle `GluingWeakening` |
| **B — bridge** | — | — | Bridge `AlgebraicGeometry/Kernel/Gluing.lean` |
| **X — acceptance program** | `examples/packages/projective-line/` and the seven rejected packages | `the_projective_line_checks_builds_and_runs`; `tests/examples.rs` | — |

<a id="acceptance-conditions"></a>

## Acceptance conditions

The acceptance program declares the lines `L1 = spec[x]` and `L2 = spec[y]`
over `SpecQQ` with their principal opens `U1 = D(x)` (inverse `xi`) and
`U2 = D(y)` (inverse `yi`); the projective line `P` glued by y = 1/x, with
the separation claim `xi -> L2::y` and the projective claim
`proj(P)[s, t] chart(L1, s, x) inverse(x -> t) chart(L2, t, y) inverse(y -> s)`;
the doubled origin glued by y = x along second opens of the same lines; the
cover of the library's `Line` by D(t) and D(1 − t) with the coefficients
(1, 1); and the real projective line `RP1`, glued from `Affine(1)[x]` and
`Affine(1)[y]` along their smooth opens {x ≠ 0} and {y ≠ 0} by y = 1/x, with
the manifold claim `manifold(RP1, 1) by(u -> M2::y)`. Its `main` composes the
transition of `P` with its inverse, declared as morphisms over `SpecQQ`, both
ways, shows `failures = 0` and exits with status 0.

| Condition | Status and evidence |
| --- | --- |
| <a id="c1"></a>C1. Glue (Zariski) | **Tested** (G, S, X): ℙ¹ is accepted (`GluingRegression` "ℙ¹, the doubled origin, ℝP¹ and the smooth doubled origin are glued objects", "the stored transition of ℙ¹ gives y and its inverse in the ring of U1"; `the_projective_line_checks_builds_and_runs`). Rejected: one chart twice ("two opens of one chart are rejected"; "a gluing needs two charts" in `stage7_rejections_have_their_codes`), an open that is a chart and not a principal open ("a chart is not an open"), a transition that breaks the relations ("a transition that is not invertible is rejected", "a transition that breaks the relations is rejected"; book reject `gluing-not-inverse`), a third chart and a single open ("a third open is rejected", "a single open is rejected"; book reject `gluing-third-chart`), all `E_GLUE`, and a missing image `E_AFFINE_COORDINATE` ("a missing image is a coordinate error"). Charts over different bases ("charts over different bases are rejected"), a transition that respects the relations but is not inverse to its inverse ("a transition that respects the relations but is not inverse to its inverse is rejected", "the not-inverse message says so"), and over a base with a coordinate a transition that moves the base ("a family of lines over a base glues fibrewise", "a transition that moves the base is rejected"), all `E_GLUE`. **Proved (oracle)**: `Gluing.checkTransition_sound` (`TransitionValid`: images in normal form, relations respected both ways with exact quotients, both composites the identity) and `glued_sound` (two opens of distinct charts in the site of the implementation, the transition facts, and over a base with structure images the commuting triangle with both structure maps) |
| <a id="c2"></a>C2. Doubled origin | **Tested** (G, X): the lines glued by y = x along D(x) ≅ D(y) are a glued object (`GluingRegression`, first case; the anchor `doubled` of the acceptance program). **Proved (oracle)**: `glued_sound` |
| <a id="c3"></a>C3. Separated | **Tested** (G, X): ℙ¹ is separated with the witness `xi -> L2::y` ("ℙ¹ is separated with the witness y"); the doubled origin is rejected with the witnesses `L2::y` and `L1::x` ("the doubled origin is not separated", "the doubled origin is not separated with x either"; book reject `gluing-not-separated`), and the identity gluing along D(x² + 1) is rejected ("the identity gluing along D(x² + 1) is not separated"); a witness of another coordinate ("a witness of another coordinate is rejected") and a separation claim of a smooth gluing ("a smooth gluing has no separation claim") are `E_GLUE`; a forged witness and a forged glued object are `E_GLUE` (`forged_stage7_records_are_rejected_by_the_kernel`). The tracker wrote the witness as `L1::xi -> L2::y`; the delivered witness names the inverse coordinate of the first open unqualified. That no witness exists for the doubled origin is a fact of algebra that the tests sample with two witnesses; no theorem states it. **Proved (oracle)**: `Gluing.checkSeparation_sound` and `separated_sound`. **Proved (bridge)**: `separation_surjective` ([C15](#c15)) |
| <a id="c4"></a>C4. Projective line | **Tested** (G, X): ℙ¹ with the charts (1 : x) and (y : 1) is accepted ("ℙ¹ is the projective line"), and chart entries in either order are stored in the order of the opens ("chart entries in either order are accepted and stored in the order of the opens"). Rejected, all `E_GLUE`: two charts on one standard chart ("two charts on one standard chart are rejected"; "different coordinates"), an open that is not the preimage of the overlap ("an open that is not the preimage of the other standard chart is rejected"), homogeneous coordinates that disagree on the overlap ("the doubled origin is not the projective line"; book reject `gluing-wrong-projective`), a chart map without an inverse ("a chart map without an inverse is rejected"), a missing entry and equal homogeneous coordinates ("a missing chart entry is rejected", "equal homogeneous coordinates are rejected"; a forged `homogeneous` record). **Proved (oracle)**: `Gluing.checkProjectiveChart_sound` (`ChartValid`), `checkProjectiveOverlap_sound` (different standard charts and the overlap identity s₁·φ#(t₂) − t₁·φ#(s₂) in the ideal of U1) and `projective_sound` (two distinct homogeneous coordinates, a Zariski gluing over a base without coordinates, one entry for each chart in the order of the opens, each `ChartValid`, at different coordinates, and the overlap identity). That P ≅ Proj QQ[s, t] in Mathlib is Planned ([C15](#c15)) |
| <a id="c5"></a>C5. Cover | **Tested** (G, X): D(t) and D(1 − t) cover `Line` with the coefficients (1, 1) ("D(t) and D(1 − t) cover the line"). Rejected, all `E_GLUE`: D(t² + 1) as a Zariski cover ("D(t² + 1) is no Zariski cover of the line"; book reject `gluing-false-cover`), a wrong coefficient ("a wrong coefficient is rejected"; a forged coefficient), an open of another object ("an open of another object is rejected"; "not of `gluing::Line`"), an open listed twice ("an open listed twice is rejected"). A cover named without an object is `E_PARSE` (`stage7_syntax_errors_are_reported`). **Proved (oracle)**: `Gluing.checkCover_sound` and `cover_sound`. **Proved (bridge)**: `cover_span_eq_top` ([C15](#c15)) |
| <a id="c6"></a>C6. Smooth opens | **Tested** (G, S, V): `localize(M, f) inverse u` under `SmoothR` declares a smooth open, stored with its derived presentation ("a smooth open is stored with its derived presentation") and sent as an `affine_localization` record (`the_stage7_forms_serialize_to_their_records`); under a smooth implementation of a presented object it stays `E_SMOOTH` ("a principal open under a smooth implementation of a presented object stays E_SMOOTH"); in a function body it is `E_TYPE` (`a_stage7_declaration_is_not_a_value`). It is an open of gluings and covers only; [Scope and decisions](#scope-and-decisions) records the departure from the tracker. **Proved (oracle)**: `Gluing.openData_smooth`, `chartData_smooth`, `open_smooth` (an open of the smooth site is a declared smooth open of a smooth object of the gluing's implementation, with the free presentation of its coordinates) |
| <a id="c7"></a>C7. Smooth transitions | **Tested** (G, X): the transition of ℝP¹ and its inverse respect the relations of the smooth opens and compose to the identity both ways; it is accepted, and the checks of [C1](#c1) run in the smooth site with the same actions. The form is the transition of `glue`, not an `indexed iso` of smooth maps ([Scope and decisions](#scope-and-decisions)). **Proved (oracle)**: `Gluing.checkTransition_sound` and `glued_sound`, which cover both sites |
| <a id="c8"></a>C8. Glue (smooth) | **Tested** (G, X): ℝP¹ from two `Affine(1)` lines along {x ≠ 0} ≅ {y ≠ 0} and the smooth doubled origin are glued objects of the smooth site ("ℙ¹, the doubled origin, ℝP¹ and the smooth doubled origin are glued objects"; the anchor `smooth` of the acceptance program; book reject `gluing-not-manifold`, which declares the smooth doubled origin). A glued object of the smooth site is not a `CInfScheme` descriptor object. **Proved (oracle)**: `glued_sound`, `glued_site` |
| <a id="c9"></a>C9. Manifold | **Tested** (G, X): `manifold(RP1, 1) by(u -> M2::y)` is accepted ("ℝP¹ is a manifold of dimension 1"). Rejected, all `E_GLUE`: the smooth doubled origin ("the smooth doubled origin is not a manifold"; book reject `gluing-not-manifold`), a dimension that differs from the charts ("a wrong dimension is rejected"; "dimension 2"; a forged dimension), a manifold claim of a Zariski gluing ("a Zariski gluing has no manifold claim"). A dimension that is no integer is `E_PARSE` (`stage7_syntax_errors_are_reported`) and on the wire `E_PROTOCOL`. The witness is sufficient, not necessary: the identity gluing along {x² + 1 ≠ 0} is Hausdorff and has no witness. **Proved (oracle)**: `Gluing.manifold_sound`. That the glued real points form a Hausdorff, second-countable smooth manifold with a closed graph of the transition is Planned ([C15](#c15)) |
| <a id="c10"></a>C10. Sites | **Tested** (G, S, X): a Zariski gluing of smooth opens and a smooth gluing of principal opens are `E_GLUE` ("a Zariski gluing of smooth opens is rejected", "a smooth gluing of principal opens is rejected", "the site message names the smooth site"; "the smooth site" and "the Zariski site" in `stage7_rejections_have_their_codes`; book reject `gluing-swapped-site`; a forged implementation); a Zariski open in a smooth cover is `E_GLUE` ("a Zariski open in a smooth cover is rejected"); `proj` exists only in the Zariski site ("the smooth gluing has no projective claim"), and `separated` and `manifold` each in one site ([C3](#c3), [C9](#c9)). **Proved (oracle)**: `Gluing.openData_zariski`, `openData_smooth`, `chartData_zariski`, `chartData_smooth`, `open_some`, `open_zariski`, `open_smooth` and `glued_site`: every open that an accepted check reads is a declaration of the site of its implementation |
| <a id="c11"></a>C11. No runtime footprint | **Tested** (W, S): the kernel emits the same code, byte for byte, for the program with and without its Stage 7 declarations (`stage7_declarations_leave_the_generated_code_unchanged`); a function body that names a glued object, a separation claim, a manifold claim, a cover, a projective claim or a smooth open is `E_TYPE` with "names …, which is not a value" (`a_stage7_declaration_is_not_a_value`). **Proved (oracle)**: `GluingWeakening.evalPrimitive_gluing_free` (gluing declarations change the value of no primitive) |
| <a id="c12"></a>C12. Wire | **Tested** (V): the five forms are optional records of epoch 10, and a smooth open the record of a principal open (`the_stage7_forms_serialize_to_their_records`); forged images, opens, implementations, witnesses, glued objects, dimensions, coefficients and homogeneous coordinates are `E_GLUE`, and the fields `transition`, `certificate` and `isomorphism` and a dimension `"one"` are `E_PROTOCOL` (`forged_stage7_records_are_rejected_by_the_kernel`); the witness is one binding and the cover names its object (`stage7_syntax_errors_are_reported`). [Gluing forms](protocol.md#gluing-forms) states the records |
| <a id="c13"></a>C13. Limits | **Tested** in part: a gluing has exactly two opens (`E_GLUE`, [C1](#c1)), and the images, coefficients and witnesses are polynomial expressions with the bounds of exact affine algebra, which the frontend and the wire check as for every polynomial expression (the Stage 2 tests). A cover beyond `algebraRelations` = 32 opens is `E_LIMIT` in `elaborateCover` and `checkCover` ("a cover with more opens than the limit is E_LIMIT"). Implemented without a Stage 7 regression (Planned): a smooth open of an object with 16 coordinates is `E_LIMIT`; a manifold dimension of more than 64 digits is `E_LIMIT` in the frontend (`indexed_dimension_literal`) and `E_PROTOCOL` on the wire (`smoothDimension`); and every check runs within `algebraTerms` and `algebraWork` (`runGlue`), where a budget failure is `E_LIMIT`. [Appendix D](appendix/limits.md#gluing-declarations) lists the limits |
| <a id="c14"></a>C14. Oracle theorems | **Proved (oracle)**: `Gluing` (`checkIdentity_ok`, `checkTransition_sound`, `checkCover_sound`, `checkSeparation_sound`, `checkProjectiveChart_sound`, `checkProjectiveOverlap_sound`, `openData_zariski`, `openData_smooth`, `chartData_zariski`, `chartData_smooth`, `open_some`, `open_zariski`, `open_smooth`, `glued_sound`, `cover_sound`, `separated_sound`, `manifold_sound`, `projective_sound`, `glued_site`) and `GluingWeakening` (`evalPrimitive_gluing_free`, `views_gluing_free`, and `checkSmoothOpen_append`, `checkGlued_append`, `checkCover_append`, `checkSeparated_append`, `checkManifold_append`, `checkProjective_append`, with which `FrameWeakening`, `NatureWeakening` and `SpectralWeakening` cover the Stage 7 entries), with the statements of [Verification boundaries](verification.md#oracle-theorems-of-gluing). `lake -d lean env lean scripts/audit_axioms.lean`: "axiom audit passed for 52053 declarations (13141 private) in 368 modules". That Stage 7 declarations change the validity of no other declaration is **Tested** (the byte-identical generated code and the acceptance of the program without them in `tests/gluing.rs`); its proof is Planned ([#883](https://github.com/MGYamada/Vastitas/issues/883)) |
| <a id="c15"></a>C15. Bridge theorems | **Proved (bridge)**: `cover_sum_eq_one` (for an accepted cover, Σ aᵢ fᵢ = 1 in the presented algebra `Presented x` of its object), `cover_span_eq_top` (the classes of the cover's elements span the unit ideal, `Ideal.span {fᵢ} = ⊤`) and `separation_surjective` (for an accepted separation witness, the algebra map `tensorHom`, from the polynomial ring in the coordinates of both charts to the presented algebra of the first open, is surjective); `lean-bridge/Audit.lean` requires each name. **Planned** ([#879](https://github.com/MGYamada/Vastitas/issues/879)): the Mathlib `Scheme` glued from the charts, its separatedness from an accepted separation claim, P ≅ Proj QQ[s, t] from an accepted projective claim, and, for an accepted manifold claim, the closed graph of the transition in ℝⁿ × ℝⁿ, the Hausdorff property and ℝP¹ as a smooth manifold. The meaning of a manifold claim is the argument of [Manifold claims](language/gluing.md#manifold-claims) (witness, closed graph, Hausdorff), with no Mathlib proof; the bridge states nothing about the smooth site |
| <a id="c16"></a>C16. Library | Not delivered in this stage. No `std` module is added: the profile uses `std::geometry::scheme::affine` (`AffineQQ`, `SpecQQ`, `Line`, `Over`, `compose`, `same`) and `std::geometry::smooth::affine` (`SmoothR`), and every Stage 7 declaration of the acceptance program is the program's own. A standard ℙ¹ over QQ and ℝP¹ with their claims and pages is the follow-up issue [#882](https://github.com/MGYamada/Vastitas/issues/882) |
| <a id="c17"></a>C17. Native acceptance program and rejected packages | **Tested** (X): `examples/packages/projective-line/` checks, builds and runs natively, shows `failures = 0` and exits with status 0 (`book_programs_print_their_output`); the program of `tests/gluing.rs` checks, builds, runs and shows `inverse = 1` (`the_projective_line_checks_builds_and_runs`); the seven book rejects give `E_GLUE` (`book_rejected_packages_print_their_diagnostics`) |
| <a id="c18"></a>C18. Recorded latency | **Tested** (measurement): the check time of the acceptance package, apart from any run time, with a debug frontend (`target/debug/vastitas`) and the kernel as Lake builds it, on macOS, during batch 2 at `4d5df40`. `/usr/bin/time -p ./target/debug/vastitas check --manifest-path examples/packages/projective-line/Vastitas.toml`, five runs: real 0.11, 0.11, 0.10, 0.10 and 0.09 s, median 0.10 s; user 0.06–0.07 s. The same package without its Stage 7 declarations (the gluings, the cover, the claims and the smooth opens), five runs: median 0.09 s real. The difference is within the 0.01 s resolution of `time -p`. The record makes no budget claim; #769 owns the check-time budget |
| <a id="c19"></a>C19. Continuous integration | Planned. The runs of the pull request, with the operating system of each job, are recorded here when they happen |
| <a id="c20"></a>C20. Independent whole-stage review | Planned. The review by a session other than the implementers, with each finding fixed or filed, is recorded here when it happens |

## Fast like C

The plan of #877 gives every stage from Stage 7 on four entries. For
Stage 7:

1. **Runtime footprint: none.** Smooth opens, glued objects, covers and the
   separation, manifold and projective claims are checked evidence with no
   value. No function names them (`E_TYPE`), and the kernel emits the same
   code, byte for byte, with and without them
   (`stage7_declarations_leave_the_generated_code_unchanged`; [C11](#c11)).
2. **Cost contract: none needed.** The stage adds no runtime operation, so
   it adds no reads, writes, allocations, copies, packing, retained bytes or
   data-dependent validation to a generated program.
3. **Comparison: none needed.** With no runtime operation there is nothing
   to compare with equivalent C, and no gap issue is open for the stage.
4. **Check time: bounded and recorded.** Every check runs inside the
   exact-algebra budget (`algebraTerms`, `algebraWork`), and a cover has at
   most `algebraRelations` opens, so a short declaration cannot force a long
   check (`E_LIMIT`; [C13](#c13)). [C18](#c18) records the check time of the
   acceptance package apart from run time, with no budget claim (#769).

## Proof boundary

Assumed: the Lean kernel, the Lean compiler and the C compiler, as for
every stage, and the frontend's serialization of the source, which is
Tested. The theorems of [C14](#c14) and [C15](#c15) take the premises that
[Verification boundaries](verification.md#hypotheses-and-gaps-of-the-gluing-proofs)
lists: an accepted check, or an accepted action with its budget. They state
identities of kernel polynomials and, in the bridge, a unit ideal and a
surjective ring map. The glued scheme, its separatedness, the isomorphism
with Proj and the smooth manifold of real points are Planned (#879). That
the Stage 7 declarations change the validity of no other declaration is
Tested, and its proof is Planned (#883). The Hausdorff meaning of a manifold
claim is the argument of the Reference chapter, with no Mathlib proof
(#879).

## Not claimed

- Three or more charts and their cocycle conditions (#151).
- Gluing of sections of a sheaf (#98).
- General sites and covers (#204), and the structure-sheaf gluing of a
  `Scheme` (#211).
- Smooth covers without a unit-ideal witness, such as D(x² + 1) of the real
  line (#237).
- The transfer theorems between the Zariski and the smooth site (#606).
- Additional monoidal structures (#805, #858) and further domain libraries.

## Validation

Run on `claude/stage7-gluing`:

- `lake -d lean env lean scripts/audit_axioms.lean`: "axiom audit passed for
  52053 declarations (13141 private) in 368 modules".
- The measurement of [C18](#c18).
- The book of batch 2: `python3 scripts/grammar_summary.py --write` (282
  productions), `python3 scripts/check_docs.py`, `mdbook build` (mdBook
  0.5.4), `python3 scripts/check_book.py` (106 chapters, 583 include
  directives, 245 source files parsed with the productions, 1283 repository
  paths) and `python3 -m unittest discover -s scripts -p test_check_book.py`
  (69 tests): passed. `python3 scripts/check_grammar_derivations.py` needs a
  kernel built from the sources of the compiler, and it runs with
  [C19](#c19).

The full Rust, kernel, oracle, bridge and native validation of the stage is
recorded here with [C19](#c19).
