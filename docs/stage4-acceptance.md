# Stage 4 frames and dimensions acceptance

This map links each acceptance condition of historical Stage 4 to its
implementation, positive and negative tests, oracle and bridge theorems, and
native evidence. Stage 4 is a finite, checked profile of ordered frames,
change of frame and physical dimensions over exact QQ, on top of the smooth
affine profile of Stage 3
([tracker #759](https://github.com/MGYamada/Vastitas/issues/759)). It does not
include performance: the Fast like C verdict stays with #222. The Reference
chapters are [Frames](language/frames.md) and
[Physical dimensions](language/physical-dimensions.md), the guide chapter is
[Frames and physical dimensions](guide/frames-and-dimensions.md), and
[Verification boundaries](verification.md#frames-and-physical-dimensions)
states the theorems with their premises.

Conditions C1–C23 have their evidence below. C24 (the independent
whole-stage review) is Planned until the findings of the review are fixed or
filed.

## Scope and decisions

The conditions are the checklist C1–C24 of #759, which turns the Stage 4
example of the [historical roadmap](guide/historical-roadmap.md#stage-4-bundles-and-tensor-diagrams)
into executable checks.

Decisions taken with the user (13 November 2026):

- **Exact profile only.** Frame arrays and their contraction live in the exact
  QQ profile. Buffers exist only in the numerical profile of Stage 1; its
  proved contraction facts are cited for the roadmap's sentence on buffers,
  and realizing exact arrays in F64 storage is a follow-up.
- **`nature::dimension` first.** Physical dimensions get a minimal
  `nature::dimension` (#300) in a package of its own, `nature/`, after
  [ADR 0002](adr/0002-nature-dimension.md) records the boundary between `std`
  and `nature` (#304). The check of a physical metric refers to it.
- **Module names.** The seven geometric operation names (`Affine`, `Base`,
  `origin`, `id`, `compose`, `apply`, `dimension`) may name modules, so that
  `nature::dimension` can be declared. They stay reserved for every other
  declaration and binding: functions, values, `let`, parameters, the name
  that a `use` binds, `use … as` aliases and dependency aliases. A plain
  `use nature::dimension;` binds the reserved name and is `E_RESERVED`; a
  program imports items, writes full paths or uses an alias.
- **No monoidal model.** A certified `⊗` (#201, #387) is outside the
  profile.

Design decisions of the plan that the user approved:

- **Field.** QQ only, as in Stage 3. Exact `Rat` stays inside the runtime and
  surfaces as `Pair<Int>` observations. There are no floats.
- **Frames** are declarations of a family `Frame<X>` over smooth affine
  objects. Arrays name their frame statically through a frame index
  (`Coords<b>`, `CoCoords<b>`, `FrameMap<b, c>`), so a frame mismatch is a
  static error, not a run-time failure.
- **Polynomial frames** carry a declared inverse that the kernel checks as a
  polynomial identity, so they are valid at every point. The kernel computes
  the inverse of a constant frame. Certificates that the kernel can compute
  never come from the wire.
- **Primitives are declared by the application** and embed their frame data,
  as `flat` and `sharp` embed their metric; the declaration audit compares
  each embedded copy with its declaration. `std::geometry::frame` exports the
  families only.
- **No pushforward.** `frame_matrix` takes its rows from the reverse pass of
  Stage 3, so it rests on the Stage 3 reverse pass and its theorems. Forward
  mode stays with #161.
- **No frame binding reads a metric.** The Gram matrix in a frame is a
  composite of `flat` with encoding and decoding.
- **The physical metric is `nature` evidence about a `std` metric.** It never
  produces the `std` metric, so no `std` validity depends on a `nature`
  declaration.
- **Kinds** are nominal and distinct from dimensions; `normalized` requires
  each scale to have exactly the kind of its coordinate.
- **Wire.** Protocol 9 only, with no protocol 10 (#533).
- **Admission.** [ADR 0001 §11](adr/0001-mathematics-first-stdlib.md#11-ordered-frames-of-smooth-affine-objects-amendment-2026-11-13)
  admits `std::geometry::frame`, and [ADR 0002](adr/0002-nature-dimension.md)
  admits `nature::dimension` and records the #304 boundary for it. Pull
  request #370 is not touched.
- **Proofs.** The oracle (mathlib-free) proves frame soundness, adequacy, the
  transition laws, naturality, pairing invariance, Gram transport, frame
  weakening and the soundness of physical metrics. The bridge proves frames
  as Mathlib bases, frame matrices as `LinearMap.toMatrix`, change of basis
  and Gram matrices as `LinearMap.BilinForm.toMatrix`.
- **Performance** is not claimed (#222).

The public names approved with the plan are `Frame`, `Coords`, `CoCoords`,
`FrameMap`, `columns`, `coordinates`, `inverse`; `base_dimension`,
`quantity`, `Reading`, `scale … of …`, `PhysicalMetric`, `interpret`,
`normalized`; and the codes `E_FRAME` and `E_DIMENSION`.

### Roadmap sentences

| Roadmap sentence | How this profile meets it | Rows |
| --- | --- | --- |
| Lower one accepted linear map in two different valid, nonorthogonal ordered bases; the arrays may differ | `frame_matrix` of one accepted smooth map at a point in two nonorthogonal frame pairs; the arrays are observed to differ | C7 |
| Decoding either array must recover the same map between the same spaces | Both arrays decode to the same coordinate-frame array, and in the bridge to the same Fréchet derivative; frames and objects are static | C3, C7 |
| For point-dependent frames, retain the basepoint and fiber | Polynomial frames; arrays and matrices carry their points, and mixed points give the failure value | C9, C10 |
| Contraction must preserve the endpoints and the caller's ownership of buffers | Contraction in frames checks frames statically and points at run time. Buffers exist only in the numerical profile; its proved contraction facts are cited, and F64 realization of exact arrays is a follow-up | C10 |
| On a chart with a length coordinate x and a time coordinate t, reject dx² + dt² | `interpret(E, reading = phys, euclidean)` under (x: Length, t: Time) is `E_DIMENSION`, naming L^2 and T^2 | C17 |
| A declared metric using compatible scales can make the sum meaningful | `gram((l0^-2, 0), (0, t0^-2))` with the scales l0 = 3 and t0 = 2 interprets G = diag(1/9, 1/4) | C18 |
| #518: finite real inner-product spaces, selected positive metrics, a proof about the same accepted Core in both bases | Riemannian `MetricForm` in frames; the matrices of C7 and C8 are proved for the program value that checked Core builds | C8, C12 |
| An optimized change of representation needs a validated lowering | Not claimed: no optimizer, MidIR or LLVM validation (#417, #518) | — |
| Finite locally free module sheaves, Grassmannians, tensor diagrams with dimension grades, one certified monoidal model | Only the trivial bundle with global frames on `Affine(n)`. Sheaves, Grassmannians and `⊗` models are non-goals (#261, #201, #387) | — |

### Steps

| Step | Pull request | Merge |
| --- | --- | --- |
| S0: the tracker, ADR 0001 §11, ADR 0002, the skeleton of this map | [#760](https://github.com/MGYamada/Vastitas/pull/760) | `5e8ca90` |
| S1: the shared skeleton: data types, wire forms and binding constructors, each rejected until implemented; validity moved into `IndexedValidity.lean`; Rust IR forms | [#761](https://github.com/MGYamada/Vastitas/pull/761) | `d1e11ea` |
| Batch 2: the frame reference model; the kernel frame runtime; frame declaration checks; `nature::dimension` declaration checks; the Rust parser of frame and nature declarations; the bridge prerequisites | [#764](https://github.com/MGYamada/Vastitas/pull/764) | `09c1d2a` |
| Batch 3: the frame primitives in the registry and the Rust parser; the oracle theorems of the frame runtime, the frame declarations, the nature declarations, the frame primitives and frame weakening; the bridge comparisons and accepted-Core corollaries; `std::geometry::frame`, the `nature/` package and the boundary rule; module names; the acceptance rows of the oracle | [#767](https://github.com/MGYamada/Vastitas/pull/767), with batch 4 | `56a174c` |
| Batch 4: the Reference and guide chapters and appendices; the protocol, verification and contributor chapters, the specification claims and this map; the acceptance program and its native evidence | [#767](https://github.com/MGYamada/Vastitas/pull/767), with batch 3 | `56a174c` |

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

The examples of the Reference and guide chapters are tested evidence too.
`tests/examples.rs` builds and runs the book packages `examples/packages/frames/`,
`examples/packages/physical-dimensions/` and `examples/packages/stdlib-frames/`
(`book_programs_print_their_output`, each prints `42`), and checks the
diagnostics of the sixteen rejected packages of frames and dimensions under
`examples/reject/packages/` against their `.stderr` files
(`book_rejected_packages_print_their_diagnostics`), the six of the acceptance
lane included. The rows below cite them as "book reject".

## Evidence key

Kernel files are in `lean-kernel/VastitasKernel/`, and kernel regressions run
from `scripts/check_kernel_regressions.sh`. Oracle files are in
`lean/VastitasOracle/`, and bridge files in
`lean-bridge/VastitasBridge/Differential/`.

| Key | Implementation | Tests | Theorems |
| --- | --- | --- | --- |
| **D — frame declarations** | `FrameDeclarations.lean` (`checkMatrices`, `checkFrame`), `IndexedFrameSource.lean` (`elaborateFrames`, `elaborateFrameBindings`), `IndexedValidity.lean` (`Entry.Valid` calls `checkFrame`), `Indexed.lean` (`frameData?`, `frameFamily?`, `frameObject?`, `isFrameFamily`), `Limits.lean` | `FrameDeclarationRegression`; `tests/frame_dimension_declarations.rs`; `src/frontend/indexed_parser.rs`: `every_stage4_declaration_parses_to_its_wire_record`, `malformed_stage4_declarations_are_rejected_at_their_place`; `tests/stdlib_frames.rs`: `a_frame_of_an_object_outside_cinf_affine_is_rejected` | Oracle `FrameDeclarations` (`checkMatrices_sound`, `checkFrame_sound`, `frame_sound`, `dependent_rows_not_inverse`, `Examples.*`); bridge `Frame` (`frame_basis`, `polyMatrix_mul_eq_one`, `frame_realBasis`, `frameAt_eq_realFrame`), `FramePrerequisites` (`polyFrame_eval`, `polyFrame_realEval`, `isUnit_frame`) |
| **R — frame runtime** | `FrameRuntime.lean` (`encodeTangent`, `decodeTangent`, `encodeCotangent`, `decodeCotangent`, `frameMatrix`, `transition`, `apply`, `coapply`, `compose`, `entry`, `matrixEqual`) on `SmoothRuntime` | `FrameRuntimeRegression` | Oracle `FrameRuntime` (`adequacy`, `transition_laws`, `pairing_invariant`, `frameMatrix_natural`, `frameMatrix_decode`, `coapply_eq_pullback`, `roadmap_identity`, `frameMatrix_compose`, `point_dependent_frames`, `degenerate_frames`, `gram_in_frame`, `contraction_endpoints`); bridge `Frame`, `FramePrerequisites` |
| **P — frame primitives** | `IndexedPrimitiveBinding.lean` (the thirteen constructors, `FrameRef`), `IndexedFrameContracts.lean` (`frameDeclared` and the contracts), `IndexedFrameRegistry.lean` (the entries), `IndexedPrimitiveShapes.lean` (`Slot.frameVar`, `Slot.fixedFrame`, `Relation.sameFrame`, `Relation.frameObject`, `Relation.frameBound`, `TemplateSlot.frameIndex`), `IndexedPrimitiveFamilies.lean` (the wire forms), `IndexedPrimitiveDescriptors.lean` (`SharedLiteral.frame`, `RenderContext.frameMaps`), `IndexedPrimitiveValues.lean` (`frameArray`, `frameMatrix`), `IndexedCodegen.lean`; `src/frontend/indexed_parser.rs`, `src/indexed.rs`, `src/primitive_table.rs` | `FrameRegression`; `tests/frame_primitives.rs`: `frame_primitives_select_protocol_nine_and_decode_only_there`, `raw_wire_rejects_forged_frame_bindings`, `frame_program_checks_builds_and_prints_42`; `tests/emit_golden.rs`: `frame_lean_matches_the_emit_fixtures`; `src/frontend/indexed_parser.rs`: `every_frame_primitive_parses_to_its_wire_record`, `malformed_frame_primitives_are_rejected_at_their_place`; the native fixture `frame_programs` of `scripts/check_indexed_native.sh` | Oracle `FramePrimitives` (typing, `frameDeclared_spec`, runtime lengths, `*_association`, `*_shape`, `*_total`, `*_sound`), `FrameCore` (`core_frame_*`, `DeclaredFrame`), `IndexedSemantics.registry_sound`, `SmoothJacobian.registry_reverse_sound`; bridge `AcceptedFrames` |
| **W — frame weakening** | `IndexedFrameContracts.lean` (no contract reads a metric declaration), `IndexedFrameRegistry.lean` (the evaluators read the embedded frames) | `FrameRegression` ("the profile without frame bindings is accepted on its own", "declaration order independent") | Oracle `FrameWeakening`, `FrameCore.frame_bindings_environment_free`, `SmoothMetricWeakening` (`MetricFree` of every frame binding) |
| **N — physical dimensions** | `NatureDimension.lean` (`checkBaseDimension`, `checkQuantity`, `checkReading`, `checkScale`, `checkPhysicalMetric`, `entryValues`, `sameDimension`), `IndexedNatureSource.lean` (`elaborateNature`), `Indexed.lean` (`isBaseDimension`, `quantityDimension?`, `readingData?`, `scaleData?`, `isReadingFamily`, `isPhysicalMetricFamily`), `Limits.lean` (`dimensionBases`, `dimensionExponent`, `dimensionScaleFactors`) | `NatureRegression`; `tests/nature_dimension.rs`; `tests/frame_dimension_declarations.rs`; the parser tests of D | Oracle `NatureDimension`, `NatureWeakening` |
| **X — reference model** | `scripts/frame_reference.py`, `tests/fixtures/frames.json` | `VastitasAlgebraTest.FrameReferenceRegression`; `FrameDeclarationRegression` (the transcribed `frames` and `invalidFrames`); `scripts/test_frame_reference.py` (12 tests) | Tested only |
| **V — wire** | `IndexedDeclarationProtocol.lean` (`declarationBody`, `frameColumns`, `frameInverse`, `familyRepresentation`, `parameter`, `naturalField`, `exponent`, `dimensionFactor`, `physicalGram`), `ResourceProtocol.lean` (the protocol-9 gate), `src/indexed.rs` (`is_algebraic`) | `tests/frame_dimension_declarations.rs`: `frame_and_nature_declarations_select_protocol_nine_only`, `the_fixture_wire_carries_the_frame_and_nature_records`, `the_kernel_decodes_the_frame_and_nature_records`; `tests/protocol_shape.rs`: `frame_and_nature_records_reject_unknown_fields`; `tests/frame_primitives.rs`; the wire sections of `FrameDeclarationRegression`, `FrameRegression` and `NatureRegression`; `src/indexed.rs`: `every_frame_and_dimension_form_serializes_to_its_wire_shape_and_is_algebraic`, `the_table_keeps_the_former_allow_list` | Tested only: raw-wire rejection is not a theorem |
| **L — libraries** | `stdlib/src/geometry/frame/mod.vast` (`std::geometry::frame`), `nature/Vastitas.toml`, `nature/mod.vast`, `nature/dimension/mod.vast` (`nature::dimension`), `scripts/check_boundaries.py` (no `std` manifest depends on `nature`); module names: `src/frontend.rs` (`module_name`), `NamespaceChecker.lean` (`moduleName`), `IndexedSourceBodies.lean` (`legacyFallback`) | `tests/stdlib_frames.rs`; `tests/nature_dimension.rs`; `scripts/test_check_boundaries.py`; `tests/packages.rs`: `a_module_may_take_the_name_of_a_geometric_operation`, `geometric_operation_names_stay_reserved_outside_modules`, `the_kernel_checks_geometric_module_names_independently`; `NamespaceRegression`; `tests/examples.rs`: the package `module-names` and the rejected packages `geometric-use` and `geometric-function` | Uses the same checker as application code; kernel theorem `legacyFallback_uncallable` |
| **E — acceptance program** | `examples/packages/frames-and-dimensions/` (`src/profile.vast` declares the frames, maps, metrics and the physical reading; `src/main.vast` observes them with the failure codes 1–36); the rejected packages `frame-singular`, `frame-wrong-inverse`, `frame-other-frame`, `frame-other-object`, `dimension-dx2-dt2` and `dimension-wrong-kind` under `examples/reject/packages/` | `tests/frames_dimensions.rs`: `the_example_checks_builds_and_prints_42_in_place`, `mutated_observations_change_the_native_result`, `the_example_selects_protocol_nine_and_older_envelopes_reject_it`, `raw_wire_rejects_forged_frame_records`, `tampered_frame_bindings_and_bodies_are_rejected_by_the_kernel`, `frame_mismatches_are_rejected_statically`, `rejected_stage4_packages_print_their_diagnostics` | Uses the same checker and runtime as every program |

The bridge proves what the frame runtime means in mathlib:

- **Prerequisites.** `FramePrerequisites.lean`, pure Mathlib over a
  commutative ring: `frameBasis` (with `frameBasis_apply`,
  `frameBasis_repr`, `frameBasis_equivFun`, `basisFun_toMatrix_frameBasis`,
  `frameBasis_toMatrix_basisFun`), the dual basis
  (`frameBasis_dualBasis_apply`, `frameBasis_dualBasis_repr`,
  `frameBasis_dualBasis_equivFun`), `toMatrix_frameBasis`
  (`LinearMap.toMatrix` in two frames is Q′·J·P),
  `frameBasis_toMatrix_frameBasis`, `transition_self`, `transition_trans`,
  `transition_mul_transition`, `transition_mulVec`, `frameMatrix_change`,
  `pairing_frame`, `bilinToMatrix_frameBasis`,
  `toMatrix_toBilin'_frameBasis`, `bilinToMatrix_frameBasis_transport`,
  `gram_transport`, `posDef_frameGram`, `isUnit_frame`,
  `matrix_map_mul_eq_one`, `polyFrame_eval`, `realEval`, `realEval_apply`,
  `realEval_eq_aeval`, `realEval_ratCast`, `map_realEval_ratCast` and
  `polyFrame_realEval`.
- **The frame runtime.** `Frame.lean` reads the kernel's lists as real
  matrices: `realMatrix_matrixProduct`, `realVec_matVec`,
  `realVec_transposeVec`, `realVec_reverse`, `frameAt_of_inverse`,
  `frameAt_apply`, `frameAt_repr`, `frame_basis`,
  `mvPolynomial_eq_zero_of_eval`, `polyMatrix_mul_eq_one`,
  `polyMatrix_map_realEval`, `frameAt_eq_realFrame`, `frame_realBasis`,
  `encodeTangent_repr`, `decodeTangent_sum`, `encodeCotangent_repr`,
  `decodeCotangent_sum`, `frameMatrix_eq_toMatrix_fderiv`,
  `frame_arrays_same_map`, `frameMatrix_comp_toMatrix`,
  `transition_eq_basis_toMatrix`, `pairing_in_frame`, `flat_in_frame_bilin`,
  `gram_transport_frame` and `posDef_gram_in_frame`.
- **Accepted Core.** `AcceptedFrames.lean`: `declared_frame_inverse`,
  `accepted_frame_matrix_operands`, `checked_frame_matrix_fderiv`,
  `checked_frame_arrays_same_map`, `checked_frame_chain_rule`,
  `checked_frame_encode_repr`, `checked_frame_encode_dual_repr` and
  `checked_gram_in_frame`; see [premises](#premises-of-the-accepted-program-theorems).

`lean-bridge/Audit.lean` requires each of these names. It also checks that
`realVec_reverse`, `frameMatrix_eq_toMatrix_fderiv`, `frame_arrays_same_map`,
`frameMatrix_comp_toMatrix`, `checked_frame_matrix_fderiv`,
`checked_frame_arrays_same_map` and `checked_frame_chain_rule` reach no
chain-rule theorem of `ChainRule.lean` or of the oracle, and no
`pderiv_aeval`, with the positive control that the oracle's
`FrameRuntime.frameMatrix_eq` reaches `SmoothCalculus.backward_eq_cot`.

<a id="acceptance-conditions"></a>

## Acceptance conditions

The oracle states one corollary per condition that it covers, about accepted
programs, in `FrameAcceptance.lean` (`c4_adequacy` … `c19_kinds`); each
composes a Core-level theorem of `FrameCore` with a runtime theorem of
`FrameRuntime`, or restates the declaration theorems. The acceptance example
`examples/packages/frames-and-dimensions/` checks, builds and prints `42`.
At p = (2, 1) its map f(x, y) = (x² + y, xy) has the Jacobian
((4, 1), (1, 2)); its matrix in the frames (b, c) is ((4, 6), (−3/2, −1/2))
and in (b2, c2) it is ((2/3, −1), (3, 6)). Each observation has its own
failure code from 1 to 36, so a wrong result changes the output
(`mutated_observations_change_the_native_result`). "Code k" below is that
observation. The frames of the
kernel regressions are `b = columns((1, 0), (1, 2))` (det 2, P ≠ Pᵀ),
`c = columns((1, 1), (0, 3))`, the coordinate frame, the point-dependent
`bx = columns((1, 0), (x, 1))` and the empty frame of a point; the map
F(x, y) = (x + y, x y) has the Jacobian [[1, 1], [2, 1]] at p = (1, 2).

| Condition | Status and evidence |
| --- | --- |
| <a id="c1"></a>C1. Constant frames: `indexed frame b: Frame<X> = columns(...)`; the kernel computes the inverse and checks it again, and the inverse is never on the wire; `E_FRAME` for a singular frame, a wrong count or size, a wrong family, an object that is not smooth, and an inverse declared for a constant frame; `Frame<Pt> = columns()` is accepted; entry and matrix bounds give `E_LIMIT` | **Tested** (D): `FrameDeclarationRegression` ("every invalid frame of the reference model is E_FRAME with its own message", "a wrong number of columns is E_FRAME", "a column of the wrong length is E_FRAME", "a frame at a family of another representation is E_FRAME", "a frame of an object that is not a smooth affine object is E_FRAME", "a frame of a smooth object outside its family's domain is E_FRAME", "a wire inverse on a constant frame is E_FRAME, even when it is the correct inverse", "`Frame<Pt> = columns()` and `Frame<Pt> = coordinates` are the empty frame", "coordinates is the identity, with the identity as its inverse", "an entry of a constant frame beyond 2^512 is E_LIMIT, at the edge it is accepted", "a singular constant frame beyond the entry bound is E_LIMIT, not E_FRAME", "a dense constant frame with distinct 3-digit denominators gets its inverse", "a dense constant frame with distinct 63-digit denominators is E_LIMIT, also when singular", and the declaration audit of stored frames); `a_frame_of_an_object_outside_cinf_affine_is_rejected` (`tests/stdlib_frames.rs`); book reject `frame-constant-inverse` (a constant frame that declares an inverse: `E_FRAME`); codes 1 and 2 (the kernel's inverse of b gives v = (3, 2) the array (2, 1) over p; the coordinate frame keeps (3, 2)); book reject `frame-singular` and `raw_wire_rejects_forged_frame_records` (the exact inverse of b declared on the wire, and a singular b: `E_FRAME`). **Proved (oracle)**: `FrameDeclarations.checkMatrices_sound` and `checkFrame_sound` (an accepted frame names a frame family at a declared smooth object of dimension n, and P(p)·Q(p) = Q(p)·P(p) = I at every point, whatever search found Q), `frame_sound` (the same for every frame of a valid environment), `dependent_rows_not_inverse`, `Examples.singular_rejected` (`columns((1, 2), (2, 4))` with every inverse), `Examples.point_frame_accepted`, `Examples.skew_accepted` (a constant frame of determinant 2); `FrameAcceptance.declared_invertible`. **Proved (bridge)**: `frame_basis` and `frame_realBasis` (an accepted frame is a basis of ℝⁿ at every real point), `frameAt_eq_realFrame`, `isUnit_frame`. **Tested, not proved**: that `invert?` finds the inverse of every invertible constant frame. |
| <a id="c2"></a>C2. Polynomial frames: a frame polynomial in the point needs a declared `inverse = columns(...)`; the kernel checks P·Q = Q·P = I as an identity of canonical polynomials within a budget; a wrong inverse is rejected, and so is `columns((x, 0), (0, 1))`; frames whose determinant is not constant are not claimed | **Tested** (D): `FrameDeclarationRegression` ("columns((x, 0), (0, 1)) is not a frame, with or without a declared inverse", "a wrong declared inverse on the wire is E_FRAME", "a declared inverse of the wrong shape is E_FRAME", "a frame whose determinant is a constant other than 1 is accepted with its declared inverse", "the identities of a polynomial frame beyond the term limit are E_LIMIT, before the comparison", "the identities of a polynomial frame beyond the work budget are E_LIMIT, before the comparison", "a polynomial frame with large entries and a cheap identity is accepted", "the audit rejects a wrong stored inverse of a polynomial frame"); the reference frames r and s and the invalid cases `MISSING_INVERSE` and `WRONG_INVERSE` of `tests/fixtures/frames.json`; book reject `frame-missing-inverse` (a frame that depends on the point without a declared inverse: `E_FRAME`); code 3 (r with its declared inverse gives v the array (1, 1)); book reject `frame-wrong-inverse`; `raw_wire_rejects_forged_frame_records` (r without its inverse, and r with the inverse of b: `E_FRAME`). **Proved (oracle)**: `FrameDeclarations.polyMatMul_ok`, `products_ok` (a product within the budget is the plain product), `matrixAt_plainMatMul` (evaluation is a ring map on matrices), `checkMatrices_sound`, `checkFrame_sound`, `Examples.diagonalX_rejected` (`columns((x, 0), (0, 1))` with every inverse), `Examples.shear_wrong_inverse_rejected`. **Proved (bridge)**: `polyMatrix_mul_eq_one` (the declared matrices are inverse as polynomial matrices), `polyFrame_realEval` and `frame_realBasis` (a basis at every real point). **Not claimed**: frames whose determinant is not a nonzero constant, such as diag(1 + x², 1); see [not claimed](#not-claimed). |
| <a id="c3"></a>C3. Static frame identity: arrays in b against arrays in b′ on the same object; a frame on another object of the same dimension; `Coords` against `Tangent`; `CoCoords` against `Coords`; each is a static `E_ENDPOINT` that names the frames and objects | **Tested** (P): `FrameRegression` ("an array in c where the map's source frame is b is rejected", "composing maps whose middle frames differ is rejected", "pairing arrays of two frames is rejected", "coapply of an array in the map's source frame is rejected", "a frame on another object of the same dimension is rejected", "Coords against Tangent and CoCoords against Coords are rejected", "an array checked at a point of another object is rejected", "a matrix of a map from another object is rejected", "a result type with the wrong frame is rejected", and the role-table messages "frame_apply names the map's source frame and the array's frame", "frame_compose names the middle frames", "frame_pairing and frame_coapply name both frames", "frame_decode names its declared frame", "frame_encode names the frame's object"); `arrays_in_different_frames_of_one_object_are_rejected_statically` (`tests/stdlib_frames.rs`: `same_coords(enc_b(v), enc_b2(v))` is `E_ENDPOINT` naming `Coords<b>` and `Coords<b2>`); book reject `frame-apply-frame` (`E_ENDPOINT`: "apply_map requires an array with frame b (the map's source frame), but the supplied array has frame r"), `frame-component-bound` (a component beyond the dimension of the frame) and `frame-encode-variance` (an encoding from a vector family to a covector array family: `E_FRAME`); `frame_mismatches_are_rejected_statically` (`tests/frames_dimensions.rs`: arrays in b and in b2, a vector of another object of the same dimension, a map from b applied to an array in b2, a vector where an array is expected and a vector array where a covector array is expected: `E_ENDPOINT`); `tampered_frame_bindings_and_bodies_are_rejected_by_the_kernel` (an encoding into b that names b2: `E_TYPE`; a matrix whose source frame is on the target of f, a Gram row that decodes an array in b with b2, a covector decoding of a vector array: `E_ENDPOINT`; a name that is no frame: `E_FRAME`); book rejects `frame-other-frame` (`same_coords` on `Coords<b>` and `Coords<b2>`, with the generic text of [gaps](#gaps)) and `frame-other-object`. **Proved (oracle)**: the associations of the frame bindings, `FramePrimitives.frameDecode_association`, `frameApply_association`, `frameCoapply_association`, `frameCompose_association`, `framePairing_association`, `frameEqual_association` and the other `*_association` theorems (an accepted call has its operands in the frames that the binding or the other operands require); `frameArray_has_type` and `frameMatrix_has_type` (a frame array is never a fiber); `FrameAcceptance.c10_contraction` (the operand types of accepted apply, coapply, compose and pairing). The diagnostic texts are tested, not proved. |
| <a id="c4"></a>C4. Adequacy: decode∘encode = id and encode∘decode = id, for vectors (P(p)⁻¹v) and covectors (P(p)ᵀα); the failure value is preserved | **Tested** (R, X): `FrameRuntimeRegression` ("decode ∘ encode and encode ∘ decode are the identity in every frame, at three points", "the failure value is preserved", "wrong component counts give the failure value", "a point of the wrong dimension gives the failure value"); `FrameReferenceRegression` (the `encodings` section); `test_decoding_inverts_encoding`; `frames_from_the_library_check_build_and_run_from_a_path_package` and `mutated_frame_observations_change_the_native_result` (`tests/stdlib_frames.rs`); codes 4–8 of the acceptance example (decoding after encoding and encoding after decoding in b and in r, for vectors and covectors; the failure value of a seed at another point and of a change of frame at another point). **Proved (oracle)**: `FrameRuntime.adequacy`; `FrameAcceptance.c4_adequacy` (an accepted `frame_decode(frame_encode(v))` decodes in the frame it encoded in and evaluates to the value of `v`; an accepted `frame_encode(frame_decode(a))` that encodes in the frame it decoded from evaluates to `a`); `FrameCore.core_frame_encode`, `core_frame_decode`, `DeclaredFrame.unique`. **Proved (bridge)**: `encodeTangent_repr` (encoding is `Basis.repr` in the frame), `decodeTangent_sum`, `encodeCotangent_repr` (the coordinates in the dual basis), `decodeCotangent_sum`; for accepted Core, `checked_frame_encode_repr` and `checked_frame_encode_dual_repr`. |
| <a id="c5"></a>C5. Transitions: b → b is the identity; b → b′ → b″ equals b → b″; b → b′ and b′ → b are inverse; a transition between frames of different objects is rejected | **Tested** (R, P, X): `FrameRuntimeRegression` ("b → b is the identity in every frame", "b → b' → c equals b → c", "b → b' and b' → b are inverse", "a transition sends the array of a vector in one frame to its array in the other", "the transition of a polynomial frame depends on the point"); `FrameRegression` ("a transition between frames of two objects is E_ENDPOINT, naming both", "a forged transition between frames of two objects is rejected"); book reject `frame-other-object` (a change of frame from b on `Plane` to c on `Image`: `E_ENDPOINT`); `FrameReferenceRegression` (the `transitions` section); `test_transition_laws`; codes 9 and 10 (b → b2 → b is the identity matrix, and b → b2 → r is b → r); `tampered_frame_bindings_and_bodies_are_rejected_by_the_kernel` (the same change of frame through a forged binding). **Proved (oracle)**: `FrameRuntime.transition_laws` (with `transition_self`, `transition_trans`, `transition_inverse`); `FrameAcceptance.c5_transitions` (an accepted transition from b to b is the identity, an accepted composite of transitions is the transition from the first frame to the last, and no transition between frames of two objects is accepted); `FrameCore.core_frame_transition`, `frameTransition_declared`. **Proved (bridge)**: `transition_eq_basis_toMatrix` (the runtime transition is Mathlib's `Basis.toMatrix` and sends coordinates to coordinates); `FramePrerequisites.transition_self`, `transition_trans`, `transition_mul_transition`. |
| <a id="c6"></a>C6. Pairing: the pairing in frames does not depend on the frame; mismatched points read (0, 0) | **Tested** (R): `FrameRuntimeRegression` ("the pairing in frames does not depend on the frame", "arrays at mismatched points read (0, 0)"); `test_pairing_does_not_depend_on_the_frame`; the pairing observation of `tests/stdlib_frames.rs`; codes 11 and 12 (α(v) = 9 in b, in the coordinate frame, in r and by the std pairing; arrays over two points pair to (0, 0)). **Proved (oracle)**: `FrameRuntime.pairing_invariant`, `pairing_frame_wrong_point`; `FrameAcceptance.c6_pairing` (an accepted `frame_pairing(frame_encode(α), frame_encode(v))` pairs arrays in one frame and evaluates to the pairing of α and v; over two points it reads (0, 0)); `FrameCore.core_frame_pairing`. **Proved (bridge)**: `pairing_in_frame` (the pairing of the arrays is α ⬝ᵥ v, the sum of the dual and the frame coordinates), `pairing_frame`. |
| <a id="c7"></a>C7. Roadmap identity: one accepted F at p lowered in nonorthogonal frames (b, c) and (b′, c′) with det ∉ {±1}; the arrays differ, both decode to the same coordinate-frame array, M_b′c′ = T_c·M_bc·T_b, and coapply in frames equals the Stage 3 `pullback` | **Tested** (R, X): `FrameRuntimeRegression` ("the arrays in (b, c) and (b', c') differ", "M_b'c' = T_c M_bc T_b", "both arrays decode to the same coordinate-frame array", "frameMatrix equals Q_c(F(p)) J(p) P_b(p) from the Jacobian", "coapply in frames equals the pullback", "apply in frames is adjoint to the pullback"); `FrameReferenceRegression` (the `matrices` section, in (b, c), (b′, c′), (r, s) and the coordinate frames); `test_one_map_in_two_frame_pairs`, `test_coapply_is_the_pullback`; codes 13–19 of the acceptance example (the entries (0, 0) are 4 in (b, c) and 2/3 in (b2, c2); both arrays decode to the matrix in the coordinate frames; M_b2c2 = T_{c→c2}·M_bc·T_{b2→b}; coapply in either pair equals the Stage 3 `pullback`). **Proved (oracle)**: `FrameRuntime.roadmap_identity` (`frameMatrix_natural`, `frameMatrix_decode`, `coapply_eq_pullback`, in either pullback mode); `FrameAcceptance.c7_two_frame_pairs` (two accepted lowerings of one map at one point run on the same program value and point, between the same objects; M′ = T_{c→c′}·M·T_{b′→b} with the values of accepted transitions; both decode to the Jacobian; coapply in either pair is `pullback`); `FrameCore.core_frame_matrix_lowerings`. **Proved (bridge)**: `frameMatrix_eq_toMatrix_fderiv` (a frame matrix is `LinearMap.toMatrix` of `fderiv ℝ` from the source frame at p to the target frame at F(p)), `frame_arrays_same_map` (both arrays decode, with `Matrix.toLin`, to the same map and the same coordinate-frame array); for accepted Core, `checked_frame_matrix_fderiv` and `checked_frame_arrays_same_map`. **Tested, not proved**: that the two arrays differ; for some frames they coincide. |
| <a id="c8"></a>C8. The same accepted Core: `frame_matrix` evaluates the program value that checked Core builds (`compose` makes a node), not an expanded composite; in frames, M(G∘F) = M(G at F(p))·M(F at p) | **Proved (oracle)**: `FrameCore.core_frame_matrix` (an accepted `frame_matrix(F, p)` evaluates to `FrameRuntime.frameMatrix F x P_b Q_c` on the program value and point that checked Core builds), `core_frame_matrix_compose` (for `frame_matrix(compose(g, f), p)` the program is the node `Program.compose G F`), `frameMatrix_node_rows` (its rows run the reverse pass along G and then along F), `core_frame_chain_rule_terms`; `FrameRuntime.frameMatrix_compose` (the chain rule in frames), `jacobianAt_compose`; `FrameAcceptance.c8_same_accepted_core` (both terms evaluate to the frame matrix on the program node); `IndexedSemantics.primitive_runtime_erasure` with `FrameCore.frame_runtime_operations`. **Proved (bridge)**: `frameMatrix_comp_toMatrix` and, for accepted Core, `checked_frame_chain_rule` (the matrix is `LinearMap.toMatrix` of DG(F(p)) ∘ DF(p), Mathlib's chain rule, independent of the kernel chain rule). **Tested** (R, P, X): `FrameRuntimeRegression` ("the compose node gives the matrix of the composite", "M(G ∘ F) = M(G at F(p)) M(F at p)"); the composite cases of `FrameReferenceRegression`; `test_chain_rule_in_frames`; `FrameRegression` ("the frame primitives lower to the frame and smooth runtimes"); `frame_lean_matches_the_emit_fixtures`; the native fixture `frame_programs`; code 20 (the matrix of the program node `compose_smooth(g(), f())` at p equals the product of the matrices of g at f(p) and of f at p, with the entry 13/2). **Not claimed**: native refinement of the generated C. |
| <a id="c9"></a>C9. Point-dependent frame at two points: the matrices differ, the arrays keep their points, mixed points give the failure value, and the target frame is evaluated at F(p) | **Tested** (R, P): `FrameRuntimeRegression` ("a polynomial frame at two points gives two matrices, each at its points", "the target frame is evaluated at F(p), not at p", "the polynomial frame r encodes differently at two points", "the transition of a polynomial frame depends on the point"); `FrameRegression` ("applying a map to an array over another point gives the failure value"); codes 21–24 (r at p and at q gives two matrices; the arrays keep their points; an array over p and a change of frame at q give the failure value; the target frame r is evaluated at shear(p) = (4, 1)). **Proved (oracle)**: `FrameRuntime.point_dependent_frames`, `frameMatrix_congr` (the target frame is read at F(p)), `Examples.doubleX_at_image` and `Examples.doubleX_other_point` (the matrices at two points differ, a computed instance); `FrameAcceptance.c9_point_dependent`. **Proved (bridge)**: `frameMatrix_eq_toMatrix_fderiv` (the target basis is the frame at F(p)), `frame_realBasis` (a polynomial frame is a basis at every real point). |
| <a id="c10"></a>C10. Contraction keeps endpoints: apply, coapply, compose and pairing check frames statically and points at run time; buffer ownership is cited from the Stage 1 numerical contraction theorems; F64 realization of exact arrays is a follow-up | **Proved (oracle)**: `FrameRuntime.contraction_endpoints` (apply, coapply and compose keep and check their points; a mismatch gives the failure value); `FrameAcceptance.c10_contraction` (the operand types of an accepted call fix the frames, and its value lies over the matrix's points); `FrameCore.core_frame_apply`, `core_frame_coapply`, `core_frame_compose`, `core_frame_pairing`; the associations of C3; cited for buffers, from the numerical profile of Stage 1: `StorageNumerical.nominal_endpoints` and `actual_loan_layout`. **Tested** (R, P): `FrameRuntimeRegression` ("apply needs the source point", "coapply needs the target point", "compose needs the middle point", "apply and coapply preserve the failure value", "compose preserves the failure value", "apply and coapply need one component per coordinate"); the static rejections of C3; codes 25–28 (apply moves an array from p to f(p), coapply from f(p) to p, a composite from p to g(f(p)); matrices whose middle points differ compose to the failure value). **Not claimed**: buffers and caller-owned storage for exact frame arrays. |
| <a id="c11"></a>C11. Degenerate cases: a rank-deficient map in both frame pairs; arrays of size 0×n, n×0 and 0×0 for `Pt` | **Tested** (R, P, X): `FrameRuntimeRegression` ("a rank-one map is rank one in both frame pairs", "a map Pt → ℝ² has a 2 × 0 matrix", "a map ℝ² → Pt has a 0 × 2 matrix", "a map Pt → Pt has a 0 × 0 matrix", "the empty frame encodes and decodes the empty array", "the transition of the empty frame is the 0 × 0 matrix", the apply, coapply and compose cases of the empty matrices, "coapply of the empty matrix agrees with the pullback"); `FrameRegression` ("the empty frame of a point gives the 0 × 0, 0 × 2 and 2 × 0 maps"); the rank-one cases of the reference fixture; `test_rank_one_map_stays_rank_one`; codes 29–32 (a rank-one map in both frame pairs; the 2 × 0, 0 × 2 and 0 × 0 matrices of the frame of `Pt`). **Proved (oracle)**: `FrameRuntime.degenerate_frames`, `Examples.rankOne_in_skew`, `Examples.point_adequacy` (C4 at dimension 0); `FrameDeclarations.Examples.point_frame_accepted`; `FrameAcceptance.c11_degenerate`. No theorem assumes a rank. |
| <a id="c12"></a>C12. Gram in a frame: `encode ∘ flat ∘ decode` equals PᵀGP, with the transport law TᵀG_bT; `sharp` likewise; no frame binding reads a metric declaration, so the Stage 3 metric-free statements are unchanged | **Proved (oracle)**: `FrameRuntime.gram_in_frame`, `flat_in_frame`, `sharp_in_frame`, `frameGram_transport`, `transition_eq`; `FrameAcceptance.c12_gram` (the accepted composites encode in the frame they decoded from; the transport law is stated for the value of a transition node and every Gram matrix of the object's dimension); `SmoothMetricForms.flat_uses_declared_gram`, `sharp_inverse_certified`; `FrameWeakening.frame_bindings_metric_free`. **Proved (bridge)**: `flat_in_frame_bilin` (lowering in a frame is `LinearMap.BilinForm.toMatrix` in the frame), `gram_transport_frame`, `posDef_gram_in_frame` (Riemannian evidence stays positive definite in every frame); `FramePrerequisites.bilinToMatrix_frameBasis_transport`, `gram_transport`, `posDef_frameGram`; for valid environments, `checked_gram_in_frame` (the Riemannian evidence and every frame of its object, at the runtime level: no Core node occurs in it). **Tested** (X): `FrameReferenceRegression` (the `grams` section, a positive definite and a Lorentz metric in the coordinate frame, b and r); `test_gram_transport`; codes 33–35 (the Gram matrix of a Riemannian metric in b is Pᵀ·G·P = ((2, 4), (4, 10)); in b2 it is Tᵀ·G_b·T; `sharp` in b is its inverse). |
| <a id="c13"></a>C13. Frame weakening: adding frame declarations changes no binding except the ones that name them, and no other declaration's validity | **Proved (oracle)**: `FrameWeakening.frame_weakening_binding` (in an environment with unique ids, every binding that names none of the added frames has the same validity, and every binding the same value), `frame_weakening_entry` (every entry has the same validity, for every table of class ranks), `frame_weakening_binding_of_valid`, `frame_weakening_entry_of_valid`, `stage3_bindings_frame_free`, `metric_bindings_frame_free`; `FrameAcceptance.c13_weakening`; `FrameCore.frame_bindings_environment_free`. **Tested** (P): `FrameRegression` ("the profile without frame bindings is accepted on its own", "declaration order independent"); `the_kernel_decodes_the_frame_and_nature_records` (the fixture with and without its frames). **Gap**: that `classRanks` is unchanged is not proved, so the validity of a whole environment under weakening is not stated; see [gaps](#gaps). |
| <a id="c14"></a>C14. Wire: protocol 9 only; protocols 7 and 8 give `E_PROTOCOL`; a forged inverse or transition on the wire is rejected, and so is a tampered embedded frame matrix in Core | **Tested** (V, P, D): `frame_and_nature_declarations_select_protocol_nine_only`; `frame_primitives_select_protocol_nine_and_decode_only_there`; `raw_wire_rejects_forged_frame_bindings` (a natural field that is not an unsigned decimal string of at most 64 digits, and a missing field: `E_PROTOCOL`); `frame_and_nature_records_reject_unknown_fields`; `FrameDeclarationRegression` ("protocols 7 and 8 reject each frame family representation with E_PROTOCOL", "protocols 7 and 8 reject a frame parameter with E_PROTOCOL", "protocols 7 and 8 reject each frame declaration with E_PROTOCOL", "a frame declaration takes exactly its fields", "a wire inverse on a constant frame is E_FRAME, even when it is the correct inverse", "a wrong declared inverse on the wire is E_FRAME", and the audit rejections of tampered stored frames); `FrameRegression` ("protocols 7 and 8 reject each frame primitive", "a natural field is an unsigned decimal string of at most 64 digits", "the wire carries no frame data: a matrix, an inverse or an object is an unknown field", "a forged embedded matrix or inverse is rejected", "a forged embedded object is rejected", "an embedded frame that is not a frame declaration is rejected", "a forged transition between frames of two objects is rejected", "a forged variance or swapped families are rejected"); `NatureRegression` (the wire shapes and the audit of tampered entries); `the_example_selects_protocol_nine_and_older_envelopes_reject_it` (protocols 7 and 8: `E_PROTOCOL`; 2–6 rejected); `raw_wire_rejects_forged_frame_records` (a declared inverse on a constant frame, a polynomial frame without its inverse or with a wrong one: `E_FRAME`; a matrix, an inverse or a transition on a frame declaration or binding: `E_PROTOCOL`); `tampered_frame_bindings_and_bodies_are_rejected_by_the_kernel` (a binding that names another frame, and a body that mixes frames). **Proved (oracle)** for the audit's half: `FramePrimitives.frameDeclared_spec` (a valid binding embeds each frame exactly as declared). Raw-wire rejection is tested only. |
| <a id="c15"></a>C15. Independent reference: `scripts/frame_reference.py` (constant and point-dependent frames, maps, Gram) agrees with the kernel through a fixture | **Tested** (X): `VastitasAlgebraTest.FrameReferenceRegression` compares `FrameRuntime` with the `encodings`, `transitions`, `matrices` and `grams` sections of `tests/fixtures/frames.json`, which `scripts/frame_reference.py` writes; `FrameDeclarationRegression` checks the frame declarations against a transcription of the `frames` and `invalidFrames` sections; `scripts/test_frame_reference.py` (12 tests, among them `test_fixture_is_current`, which runs the comparison of `--check`). The model takes map arrays from the Jacobian, the kernel from reverse runs. It covers the real plane only. |
| <a id="c16"></a>C16. Nature declarations: base dimensions, quantity kinds, readings and scales; integer exponents only; a reading covers each coordinate exactly once; scales are positive | **Tested** (N): `NatureRegression` ("a program declares at most 16 base dimensions", "a quantity is a product of powers of base dimensions; the exponent 0 drops out", "a quantity names base dimensions, each once, with exponents within the bound", "a reading names each coordinate once, in any order", "a reading names each coordinate of its object exactly once", "a reading reads each coordinate as a quantity", "a reading is of a smooth affine object, at a reading family", "a scale is a positive rational magnitude of a quantity", "exponents are bounded decimal strings with an optional sign", and the audit of stored declarations); `every_stage4_declaration_parses_to_its_wire_record` and `malformed_stage4_declarations_are_rejected_at_their_place` (`src/frontend/indexed_parser.rs`); `tests/frame_dimension_declarations.rs` (`the_fixture_checks_once_the_kernel_checks_frames_and_dimensions`: the fixture package with every declaration form checks); book rejects `dimension-reading-coordinate` (a reading that omits a coordinate) and `dimension-scale-magnitude` (a scale that is not positive). **Proved (oracle)**: `NatureDimension.checkBaseDimension_iff`, `checkQuantity_iff`, `checkReading_iff`, `checkScale_iff`, `valid_quantity`, `valid_reading`, `valid_scale`, `sameDimension_iff`; `FrameAcceptance.c16_nature_declarations`. |
| <a id="c17"></a>C17. Reject dx² + dt²: the std Euclidean metric interpreted under a (Length, Time) reading is `E_DIMENSION`, naming L² and T²; the plain std metric, with its evidence, `flat` and `sharp`, stays valid; generated code is byte-identical with and without nature declarations | **Tested** (N): `euclid_under_length_and_time_is_rejected_naming_l2_and_t2` (`tests/nature_dimension.rs`; the plain std metric with its evidence and `sharp` stays valid); `generated_code_is_byte_identical_without_the_nature_declarations` (byte identity with and without the nature declarations, and without the nature package); `NatureRegression` ("C17: the Euclidean metric under a reading with a length and a time is rejected, naming L^2 and T^2", "C17: the std metric stays valid; only the nature declaration is rejected", "the Euclidean metric under a reading with two lengths is accepted, with value L^2", "the std entries are valid on their own and with the nature entries", "an invalid nature entry leaves the std entries valid"); book reject `dimension-dx2-dt2` (`E_DIMENSION`: "the term x·x has dimension L^2 and the term t·t has dimension T^2"; also `rejected_stage4_packages_print_their_diagnostics`). **Proved (oracle)**: `NatureDimension.euclidean_sound`, `euclidean_rejected` (rejected whatever its declared value, for any two distinct base dimensions), `Roadmap.euclidean_check_rejected`, `Roadmap.euclidean_invalid`; `NatureWeakening.metric_nature_free`, `metric_valid_with_reading`, `flat_sharp_nature_free`, `validPrimitiveBinding_nature_insertion`, `evalPrimitive_nature_insertion`; `FrameAcceptance.c17_dx2_dt2_rejected`. Byte identity of generated code is tested, not proved. |
| <a id="c18"></a>C18. Scaled metric: l0 = 3 and t0 = 2 interpret G = diag(1/9, 1/4); a magnitude mismatch is rejected, and so is a scale of the wrong dimension; dx² − c²dt² with a velocity scale c is accepted; the gradient of x + t is (9, 4) through the Stage 3 `sharp` | **Tested** (N): `the_scaled_metric_is_accepted_and_its_gradient_is_nine_four` (the program prints 904, 100 times the x component plus the t component, natively); `scaled_interpretations_must_match_the_metric_and_its_dimensions`; `NatureRegression` (the four C18 checks, "a declared value that differs from the inferred one is rejected, naming both", and "a physical metric interprets a metric and a reading of its own object": an interpretation of a metric of another object, or under a reading of another object, is `E_DIMENSION`, the negative test of ADR 0002 §3); book rejects `dimension-gram-magnitude` (an entry whose magnitude differs from the metric) and `dimension-declared-value`; the book package `physical-dimensions`; code 36 of the acceptance example (the gradient of x + t under G = diag(1/9, 1/4) is (9, 4), in a program whose profile declares the reading, the scales and the interpretation). **Proved (oracle)**: `NatureDimension.physicalMetric_sound`, `valid_physicalMetric` (an accepted physical metric evaluates to the Gram matrix of its metric, and every nonzero term has one dimension), `entryValues_gram`, `scaleMonomialValue_sound`, `Roadmap.scaled_accepted`, `interpreted_valid`, `mismatch_rejected`, `wrong_dimension_rejected`, `minkowski_accepted`; `FrameAcceptance.c18_scaled_metric` (with the gradient (9, 4) by `decide +kernel`). The meaning of the gradient is the Stage 3 bridge theorem `Metric.gradient_riesz`. |
| <a id="c19"></a>C19. Kinds: Length and Wavelength, Energy and Torque are never identified; `normalized` with a Wavelength scale on a Length coordinate is rejected although the dimensions agree | **Tested** (N): `normalized_needs_the_kind_of_each_coordinate` (a `Wavelength` scale on the `Length` coordinate and a `Torque` scale on an `Energy` coordinate are rejected); `NatureRegression` ("C19: normalized(x: l0, t: t0) is accepted, in either order", "C19: normalized with a Wavelength scale on a Length coordinate is rejected", "C19: Energy and Torque are two kinds", "C19: in explicit rows only dimensions count, so a Wavelength scale may stand for a Length", "the audit compares the kinds of normalized, not their dimensions"); book reject `dimension-wrong-kind` (a `Wavelength` scale on the `Length` coordinate; also `rejected_stage4_packages_print_their_diagnostics`). **Proved (oracle)**: `NatureDimension.normalized_rejected_of_kind`, `valid_physicalMetric` (`Interprets.normalizedKinds`), `Roadmap.normalized_accepted`, `wavelength_rejected`, `wavelength_rows_accepted`; `FrameAcceptance.c19_kinds`. |
| <a id="c20"></a>C20. Boundary: std manifests stay inside `stdlib/`; nature depends on std; a std → nature edge is rejected by `scripts/check_boundaries.py` | **Tested** (L): `scripts/check_boundaries.py` (no `std` manifest depends on `nature`; `nature` depends on nothing outside `std` and `nature`); `scripts/test_check_boundaries.py` (`test_std_and_nature_manifests_follow_the_library_boundary`, `test_a_std_to_nature_edge_is_rejected`, `test_nature_depends_on_nothing_outside_std_and_nature`, `test_relative_segments_and_symbolic_links_cannot_hide_an_edge`, `test_malformed_library_manifests_fail_closed`, `test_actual_library_manifests_pass_and_reject_a_std_to_nature_edge`); `a_std_manifest_that_depends_on_nature_forms_a_cycle` (`tests/nature_dimension.rs`). `Cargo.toml` packages `nature/`, and the sparse checkout of the native compiler jobs of `ci.yml` includes it. Tested only. |
| <a id="c21"></a>C21. Libraries: `std::geometry::frame` and `nature::dimension` are usable from path packages, with a public-name audit | **Tested** (L): `frames_from_the_library_check_build_and_run_from_a_path_package` and `mutated_frame_observations_change_the_native_result` (`tests/stdlib_frames.rs`: arrays in a constant frame b and a polynomial frame r, a transition, a map array and a pairing, natively); `frame_module_exports_exactly_its_four_families` (`Frame`, `Coords`, `CoCoords`, `FrameMap`); `the_scaled_metric_is_accepted_and_its_gradient_is_nine_four`, `nature_and_the_application_share_one_std_package`, `dimension_module_exports_exactly_its_names` (`Reading`, `PhysicalMetric`, the base dimensions `L`, `T`, `M` and the quantities `Length`, `Time`, `Mass`, `Speed`, `Wavelength`, `Energy`, `Torque`), `the_dimension_module_is_reachable_by_items_paths_and_an_alias` (`tests/nature_dimension.rs`); the module names: `a_module_may_take_the_name_of_a_geometric_operation`, `geometric_operation_names_stay_reserved_outside_modules`, `the_kernel_checks_geometric_module_names_independently` (`tests/packages.rs`), the package `examples/packages/module-names/` and the rejected packages `geometric-use` and `geometric-function` (`tests/examples.rs`), the book reject `dimension-module-import` (`use nature::dimension;` is `E_RESERVED`), `NamespaceRegression`; the book packages `frames`, `physical-dimensions` and `stdlib-frames`; `function_body_affine_spellings_still_use_the_geometry_compatibility_export` (`tests/smooth_differential.rs`) and the library list of `tests/stdlib_geometry.rs`, which include `frame/mod.vast`. The kernel theorem `legacyFallback_uncallable` proves that a child module named like an operation never hides a declaration that a call could reach. The libraries use the same checker as application code. |
| <a id="c22"></a>C22. Native: the example checks, builds and prints `42`; a mutation test flips each of its codes | **Tested** (E): `the_example_checks_builds_and_prints_42_in_place`; `mutated_observations_change_the_native_result` (four groups of source mutations; a bitmask copy of the program maps code k to 2^(k−1), so each output names the failed set; every code 1–36 is flipped by some group); `rejected_stage4_packages_print_their_diagnostics`. Other native evidence: the book packages `frames`, `physical-dimensions` and `stdlib-frames` (`book_programs_print_their_output`), `frame_program_checks_builds_and_prints_42` (`tests/frame_primitives.rs`, the corpus program `tests/emit_corpus/frame-primitives/`), `frames_from_the_library_check_build_and_run_from_a_path_package` and `mutated_frame_observations_change_the_native_result` (`tests/stdlib_frames.rs`), `the_scaled_metric_is_accepted_and_its_gradient_is_nine_four` (`tests/nature_dimension.rs`), and the native fixture `frame_programs` of `scripts/check_indexed_native.sh`. **Assumed**: the Lean-to-C toolchain and the C compiler. **Not claimed**: performance. |
| <a id="c23"></a>C23. CI: green, with OS coverage recorded per job | **Tested** (CI): [#767](https://github.com/MGYamada/Vastitas/pull/767), the integration pull request of batches 3 and 4, has all 14 checks green at its head `15dd1e2`: [CI](https://github.com/MGYamada/Vastitas/actions/runs/43452684682) (both native compiler jobs, both GEMM adapter jobs, Rust formatting and lint, Lean proofs and axiom audit), [Mathematical bridge](https://github.com/MGYamada/Vastitas/actions/runs/43452684713) (and its push run [43452678966](https://github.com/MGYamada/Vastitas/actions/runs/43452678966)), [Documentation book](https://github.com/MGYamada/Vastitas/actions/runs/43452684788) and the four CodeQL analyses (actions, c-cpp, python, rust) with their summary check. The jobs that run the Stage 4 evidence: `ci.yml` "Rust formatting and lint" (ubuntu-latest: `cargo fmt`, `clippy`, `check_docs.py`, `check_spec.py`, `check_primitive_table.py`, `check_boundaries.py`, the Python tests under `scripts/` with the frame reference and boundary tests); "Native compiler (ubuntu-latest, no mathlib)" and "Native compiler (macos-latest, no mathlib)" (kernel build, `check_kernel_regressions.sh`, `check_indexed_native.sh`, `cargo test`); "Lean proofs and axiom audit" (ubuntu-latest: `VastitasOracle`, the axiom audits, the specification resolver, leanchecker replay); `lean-bridge.yml` "Daleckii–Krein proof and axiom audit" (ubuntu-latest: the bridge build, `Audit.lean`, the bridge specification resolver, leanchecker replay); `documentation.yml` "book" (ubuntu-latest). Batch 2, [#764](https://github.com/MGYamada/Vastitas/pull/764), had every job green: [CI](https://github.com/MGYamada/Vastitas/actions/runs/43426305869) (both native compiler jobs, both GEMM adapter jobs, Rust formatting and lint, Lean proofs and axiom audit), [Mathematical bridge](https://github.com/MGYamada/Vastitas/actions/runs/43426305779) and [Documentation book](https://github.com/MGYamada/Vastitas/actions/runs/43426306118). macOS bridge and oracle evidence is local only. |
| <a id="c24"></a>C24. Review: an independent whole-stage review, fixed or filed, before closing | **Planned.** A session other than the implementers reviews the whole stage after C23; its findings are fixed or filed before #759 closes. |

<a id="premises-of-the-accepted-program-theorems"></a>

## Premises of the accepted-program theorems

The theorems of `FrameAcceptance.lean` and of `AcceptedFrames.lean` are about
one accepted node or a small accepted term. The exceptions are the rows C13
and C16–C19, which are about declarations (see below), and two bridge
theorems for valid environments, which name no Core node:
`declared_frame_inverse` (a declared frame is invertible at every point) and
`checked_gram_in_frame` (the Gram matrix of Riemannian evidence in each
frame of its object). *Accepted* means that the Core term type-checks
against the module's declarations (`Typing.HasType`, which for a primitive
node includes the validity of its binding and the types of its operands)
and that the module's environment is valid
(`module.declarations.indexed.Valid`). Nothing is assumed about the frames:
a binding embeds each frame as its declaration (`FrameCore.DeclaredFrame`,
from the binding's validity), and the valid environment makes that frame
invertible at every point at the dimension of its object
(`FrameAcceptance.declared_invertible`, from `DeclaredFrame.checked` and
`FrameDeclarations.checkFrame_sound`). The lengths of points and arrays come
from their checked types. The bridge's `accepted_frame_matrix_operands`
derives in the same way that the map operand is a program checked as
ℝⁿ → ℝᵐ and that the point has n coordinates.

Two premises stay, as in the oracle's `core_*` theorems of Stage 3:

- **operand evaluation**: each leaf operand evaluates, at some fuel, to a
  value (`eval module fuel values t = some v`); for C8 at every large enough
  fuel (`IndexedEvaluation.Evaluates`);
- **operand typing**: those values have the operand types
  (`PrimitiveValuesHaveTypes`).

Typing fixes most frame identifications: `Coords<b>` makes
`frame_decode(frame_encode(v))` decode in the frame it encoded in, the middle
frame of `frame_compose` and the one frame of `frame_pairing` are fixed by
their associations, and `DeclaredFrame.unique` turns a named frame into its
embedded matrices. Where the program text chooses a frame that typing does
not fix, the statement says which: `frame_encode(frame_decode(a))` in C4 and
the Gram composites of C12 encode in the frame they decoded from, and the two
terms of C8 name the same outer frames.

These theorems are not composed with whole-term preservation,
`IndexedEvaluationSafety.evaluation_total_and_typed`, which keeps its own
premises: `CallReturns` for every callee of the term, uniqueness and
freshness of the allocated serials, a typed context and a valid declaration
set. C13 and C16–C19 are about declarations and bindings, the data that
checked Core reads; they are stated for environments, valid ones for
C16–C19, and for the roadmap environment that the kernel evaluates.

## Per-issue ledger

| Issue | Met by this profile | Open |
| --- | --- | --- |
| [#518](https://github.com/MGYamada/Vastitas/issues/518) basis adequacy | The finite exact slice: frames of the tangent fibers of `Affine(n)`, constant or polynomial in the point; arrays and map arrays in two nonorthogonal frame pairs that decode to the same map (C4, C7); a proof about the program value that checked Core builds (C8); Riemannian metrics in frames with Gram transport (C12) | Item 4 (Moore–Penrose inverses, kernels, images and projections); an optimized change of representation with a validated lowering and its floating-point and ownership obligations (#417); no LLVM witness |
| [#300](https://github.com/MGYamada/Vastitas/issues/300) `nature::dimension` | The minimal slice: base dimensions, quantity kinds, readings, positive scales and the physical interpretation of a std metric whose dimensional consistency the kernel checks (C16–C19) | Unit systems and conversion, rational exponents, natural units, Buckingham π; physical readings of frames, fibers and arrays; the dimension of a gradient |
| [#304](https://github.com/MGYamada/Vastitas/issues/304) std, monad and nature | The boundary as it applies to `nature::dimension`, recorded in ADR 0002 and checked by `check_boundaries.py` (C20); the physical metric is evidence about a std metric (C17) | The responsibilities of `monad`, and the boundary for other `nature` modules |
| [#264](https://github.com/MGYamada/Vastitas/issues/264) `std::geometry::metric` | Metrics in frames: the Gram matrix in a frame and its transport, `flat` and `sharp` in frames, positive definiteness in every frame (C12); no frame binding reads a metric | Position-dependent metrics and the items that the Stage 3 record leaves open |
| [#261](https://github.com/MGYamada/Vastitas/issues/261) bundles | The trivial bundle with global frames on `Affine(n)` only | Module sheaves, locally free bundles, Grassmannians, torsors and connections |
| [#66](https://github.com/MGYamada/Vastitas/issues/66), [#91](https://github.com/MGYamada/Vastitas/issues/91) linear algebra and GEMM | Change of basis for exact maps of tangent fibers (C5, C7) | The numerical profile is unchanged; `std::linalg` stays Planned |
| [#69](https://github.com/MGYamada/Vastitas/issues/69) contraction | Contraction in frames keeps its endpoints in the exact profile: frames statically, points at run time (C10) | Buffers and caller-owned storage for exact arrays (F64 realization) |

Non-goals that stay open: #201 and #387 (a certified `⊗`), #246 and #375
(exterior algebra and the Hodge star), #259 (modules), #161 (forward mode and
pushforward), #417 (MidIR and LLVM validation), #222 (performance).

<a id="gaps"></a>

## Gaps

- **Exact rationals in `frameMatrix`.** A frame matrix runs one recomputing
  reverse pass per row, m interpreted runs for a map to `Affine(m)`, and its
  exact rationals are not bounded. Neither the growth nor the cost is
  measured.
- **Class ranks under weakening.** `frame_weakening_entry` and the
  declaration theorems of `NatureWeakening` hold for every table of class
  ranks. That `classRanks` computes the same table with and without the added
  declarations is not proved, because its passes are private to the kernel's
  `Indexed` module; so the validity of a whole environment under weakening is
  not stated.
- **The message of `frame_equal`.** A mismatch of the operands of
  `frame_equal` is reported with the generic `E_ENDPOINT` text of its
  relation `sameApplication`, which names both types but not the role of the
  frame: `primitive capability, endpoint or coefficient contract failed:
  Coords<b>, Coords<b2>` (the rejected package `frame-other-frame`). The
  other frame bindings name the frames by role.
- **Completeness of `invert?`** for constant frames is tested, not proved.
  Soundness does not depend on it, because the kernel checks every inverse
  again; an incomplete search would reject a valid frame with `E_FRAME`.
- **Reference coverage.** The Python reference covers the real plane only;
  dimensions 3–16 have no independent reference, and dimension 0 is covered by
  `FrameRuntimeRegression`.
- **Composition with whole-term preservation** is not proved; see
  [premises](#premises-of-the-accepted-program-theorems).
- **Rust parsing** is Assumed. The kernel re-checks every declaration, but
  parser fidelity is tested only.
- **Performance** is not claimed (#222).

<a id="proof-boundary"></a>

## Proof boundary

- **Proved (oracle).**
  - An accepted frame is invertible at every point, for constant and
    polynomial frames; the singular and wrong examples are rejected.
  - The frame runtime: adequacy, the transition laws, pairing invariance,
    change of frame, decoding to the Jacobian, coapply as the Stage 3
    pullback, the chain rule in frames, point dependence, degenerate cases,
    Gram matrices in frames and endpoints of contraction.
  - Every frame binding is total and typed, erases to the runtime and embeds
    its frames as declared; the static frame checks are its associations.
  - Accepted frame nodes evaluate to the runtime operations on the program
    value that checked Core builds, and the acceptance rows C4–C13 and
    C16–C19 for accepted programs.
  - Frame declarations at any position leave every other declaration's
    validity unchanged, for every table of class ranks, and every unrelated
    binding; no frame binding reads a metric.
  - Nature declarations at any position leave the validity of every
    non-nature declaration unchanged, for every table of class ranks, and
    every binding. A non-nature declaration here is one other than a base
    dimension, a quantity, a reading, a scale or a physical metric. Nature
    declarations can change each other's validity: a 17th base dimension
    makes every base dimension invalid, because a program declares at most
    16 (`dimensionBases`).
  - The declarations of `nature::dimension` mean what ADR 0002 §3 states, and
    the roadmap example by kernel evaluation.
- **Proved (bridge).** Frames as Mathlib bases at every real point, arrays
  as `Basis.repr` and its dual, frame matrices as `LinearMap.toMatrix` of the
  Fréchet derivative, transitions as `Basis.toMatrix`, pairing invariance,
  Gram matrices as `LinearMap.BilinForm.toMatrix` with positive
  definiteness, and the chain rule in frames, at the runtime level. For
  accepted Core nodes too: frame matrices, the two arrays of one map, the
  chain rule in frames and the encodings. For valid environments: a
  declared frame is invertible at every point, and the Gram matrix of
  Riemannian evidence in every frame of its object. Transitions and pairing
  have runtime-level theorems only. The frame-matrix theorems use no
  chain-rule theorem.
- **Tested only.**
  - Raw-wire and tampered-Core rejection, and protocols 7 and 8.
  - Parser fidelity and diagnostic messages, including the `E_ENDPOINT`
    roles and the `E_DIMENSION` texts.
  - Byte identity of generated code with and without nature declarations.
  - Native execution of the compiled programs and their mutations.
  - Agreement with the Python reference.
  - Completeness of `invert?`; that the two arrays of C7 differ.
  - The boundary between `std` and `nature`.
- **Assumed.**
  - The Rust frontend's parsing.
  - The Lean-to-C toolchain and the C compiler.
  - Lean core `Rat` and GMP.
  - mathlib itself.

<a id="not-claimed"></a>

## Not claimed

Each gets a follow-up issue when Stage 4 closes, unless an issue already
owns it.

- Realizing exact frame arrays in F64 storage with caller-owned buffers.
- Generic `std` frame primitives, generic over frames.
- Frames whose determinant is not a nonzero constant (they need opens, #606).
- Physical readings of frames, fibers and arrays (graded fibers); the
  dimension of a gradient.
- Unit systems and conversion (100 cm = 1 m), rational exponents, natural
  units, Buckingham π (#300).
- Pushforward and forward mode (#161).
- Moore–Penrose inverses, kernels, images and projections (#518 item 4,
  #259, #264).
- Exterior algebra and the Hodge star (#246, #375); module sheaves,
  Grassmannians, torsors and connections (#261); `⊗` models (#201, #387).
- Optimized representation choice, MidIR and LLVM validation (#417, #518).
- Floats, native refinement and performance (#222).
- Unbounded `Rat` growth inside `frame_matrix`, and its m interpreted reverse
  runs.

## Validation

Batch 2 was validated locally on a 16 GiB machine before its CI run
([#764](https://github.com/MGYamada/Vastitas/pull/764)):
`check_kernel_regressions.sh` and `check_indexed_native.sh`, the oracle build
and `audit_axioms.lean`, the bridge build and `Audit.lean`, `cargo fmt`,
`clippy`, `cargo test --locked --all-targets` (667 passed, 0 failed, 17
ignored), `check_primitive_table.py`, `check_spec.py`, `check_docs.py`,
`check_boundaries.py`, `frame_reference.py --check`, the script unit tests,
`mdbook build` and `check_book.py`. Batches 3 and 4 run the same commands,
one heavy check at a time:

- `cargo fmt --check`, `cargo clippy --locked --all-targets -- -D warnings`
  and `cargo test --locked --all-targets --no-fail-fast`.
- `lake -d lean-kernel build` with every library, executable and regression
  library; `bash scripts/check_kernel_regressions.sh`;
  `bash scripts/check_indexed_native.sh`.
- `lake -d lean build VastitasOracle` and
  `(cd lean && lake env lean -DwarningAsError=true ../scripts/audit_axioms.lean)`.
- `(cd lean-bridge && lake build)` and
  `(cd lean-bridge && lake env lean Audit.lean)`; from the repository root,
  `bash scripts/replay_lean.sh lean-bridge VastitasBridge` (one thread).
- `python3 scripts/check_spec.py`, with the statement pins of the cited
  oracle and bridge theorems; `python3 scripts/check_primitive_table.py`;
  `python3 scripts/frame_reference.py --check`.
- `python3 scripts/check_boundaries.py` and
  `python3 -m unittest discover -s scripts -p 'test_*.py'`.
- `python3 scripts/check_docs.py`, `mdbook build` and
  `python3 scripts/check_book.py`.

CI also runs `lake -d lean env python3 scripts/check_axiom_audit.py` and the
leanchecker replay of the oracle and the kernel (C23).
