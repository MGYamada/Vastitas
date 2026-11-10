# Compiled reverse Core acceptance

This map links each acceptance condition of compiled reverse Core to its
implementation, tests, oracle and bridge theorems, and native evidence.
Compiled reverse Core extends the finite smooth profile of historical Stage 3
([acceptance map](stage3-acceptance.md)). The kernel compiles the reverse
passes of a checked program into Core and checks that Core again. The oracle
and the bridge prove what each generated function computes, and what each
compiled site computes under premises that no theorem discharges yet; whole
compiled modules agree with their source in tests, not in a theorem
([#665](https://github.com/MGYamada/Vastitas/issues/665);
[tracker #623](https://github.com/MGYamada/Vastitas/issues/623)). The map
does not include performance: the Fast like C verdict stays with #222.
[Verification boundaries](verification.md#compiled-reverse-core) describes
the compilation.

## Terms

- The [**runtime reverse pass**](appendix/glossary.md#runtime-reverse-pass)
  is the verified routine of the Stage 3 runtime: `SmoothRuntime.pullback`,
  `backward`, `differential` and `linearize`. It walks the program value that
  checked Core builds.
- A [**reverse site**](appendix/glossary.md#reverse-site) is a call whose
  [derivative rule](appendix/glossary.md#derivative-rule) is a reverse pass:
  a cotangent pullback in either mode, a differential, or the reverse pass of
  a tape that `linearize` builds.
- [**Compiled reverse Core**](appendix/glossary.md#compiled-reverse-core) is
  the Core that the kernel generates for the reverse sites of a checked
  module. Each site has forward Core and backward Core.
- The [**forward Core**](appendix/glossary.md#forward-core) of a site binds
  the input point r₀ and its images rᵢ = mᵢ(rᵢ₋₁) along the maps m₁, …, m_k
  of the site, in application order. Each map is one step. r_k is the primal
  value. The images are evaluated points; r₀ is the point operand as the
  source gives it.
- The points r₀, …, r_{k−1} are the
  [**residuals**](appendix/glossary.md#residual). They are ordinary Core
  values of the types `Smooth<P, Xᵢ>`. A saved site passes every point, the
  residuals and the primal value, to its backward Core.
- The seed of a differential is the **unit covector** at r_k: the coordinate
  covector of the 1-dimensional target.
- The [**backward Core**](appendix/glossary.md#backward-core) of a site is a
  generated function. It pulls the seed back along m_k, …, m₁.
- The [**Jacobian table**](appendix/glossary.md#jacobian-table) of a declared
  map is the matrix of its partial derivatives, which the kernel computes when
  it generates the program.
- A [**Jacobian step**](appendix/glossary.md#jacobian-step) is the step along
  a declared map. It applies the transpose of the map's Jacobian table at the
  saved point.
- An [**opaque step**](appendix/glossary.md#opaque-step) is a map whose
  structure the compilation does not open. The backward Core pulls the seed
  back along it with the runtime reverse pass in the site's residual policy.

## Scope and decisions

The conditions are the Target items T1–T5 and the acceptance boxes A1–A6 of
#623. The decisions behind the profile are:

- <a id="jacobian-tables"></a>**Derivative rules are precomputed Jacobian tables.** The derivative rule
  of a declared map is `morphism map`. A step along the map evaluates the
  Jacobian table of `map`, a literal of rational polynomials. The generated
  code declares each distinct table once, and every step names its table.
  Nothing is differentiated symbolically at run time.
- **Opaque maps and tapes take one runtime step.** A function parameter, the
  value of a branch or of a call, `composite(…)` and a map that the
  `reverseLeaves` budget does not reach are opaque steps; a map operand whose
  own `compose` calls exceed the budget is one opaque step as a whole. The
  backward Core pulls the seed back along each with the runtime reverse pass.
  A tape that crosses a function boundary keeps `linearize` and `backward`,
  and so does a tape bound by a `let` whose map or point is not a variable, a
  literal or a call of a non-allocating primitive, such as a call result or a
  branch value. The
  [per-code table](#acceptance-example-by-code) lists the opaque steps of the
  acceptance example.
- **Residuals are a `let` chain, and the backward Core is a function.** The
  forward Core is a chain of `let`s. It stands at a saved site, and inside the
  generated function of a recomputing site. The backward Core is a generated
  function of the opaque maps, the points and the seed. A saved site passes
  every point: the residuals and the primal value. A recomputing site passes
  r₀, and its function evaluates again the images that its steps read; its
  opaque steps run the runtime reverse pass in recomputed mode. The
  compilation adds no Core type.
- **The theorems cover the generated functions and, locally, the rewrite of
  a site.** The oracle proves what the forward and backward Core of every
  entry of a compiled module compute. The bridge proves the Fréchet
  comparison without the kernel chain rule. The rewrite of one site is proved
  under premises that are not discharged inside rewritten functions. Whole
  modules agree in tests, not in a theorem.

Further facts of the profile:

- **No rejection.** The compilation is designed to reject no accepted
  program. A site that it cannot compile stays a call of the runtime reverse
  pass; see [gaps](#gaps). A generated module that failed the Core audit
  would be an internal error (`E_INTERNAL_REVERSE`); no theorem excludes it,
  and no test reaches it.
- **Field.** QQ only, as in Stage 3. There are no floats.
- **Wire.** The wire form and the protocol versions are unchanged. The Rust
  frontend derives nothing; no file under `src/` changes.
- **Placement.** The kernel compiles after acceptance, in `check` and in code
  emission, and code generation receives only the compiled module.
- **Reference.** The runtime reverse pass stays, for opaque steps and as the
  routine that compiled Core agrees with.
- **Admission.** [ADR 0001 §10](adr/0001-mathematics-first-stdlib.md#compiled-reverse-core-amendment)
  admits compiled reverse Core for this profile.

### Steps

| Step | Content | Pull request | Batch |
| --- | --- | --- | --- |
| 1 | The field `reverse` of every registry entry; the step bindings `smoothApply` and `cotangentJacobian`; `SmoothRuntime.jacobian` and `jacobianStep`; the oracle's `ReverseSound` | [#661](https://github.com/MGYamada/Vastitas/pull/661) | [#663](https://github.com/MGYamada/Vastitas/pull/663) |
| 2 | Reading the maps of a site, the templates, the reserved declarations, the ledger, structural equality, validation, `Reverse.compile` and its wiring, generation from `compiled`, `reverseLeaves`; the kernel regression, the Rust tests, the goldens and the corpus | [#662](https://github.com/MGYamada/Vastitas/pull/662) | [#663](https://github.com/MGYamada/Vastitas/pull/663) |
| 3 | The oracle theorems (`SmoothReverseCore`, `IndexedReverseCore`, `SmoothReverseCompiled`), `scripts/check_chain_rule_free.lean` and the specification [reverse-core](spec/reverse-core.md) | [#669](https://github.com/MGYamada/Vastitas/pull/669) | [#672](https://github.com/MGYamada/Vastitas/pull/672) |
| 4 | The bridge theorems (`ReverseCore.lean`) and the independence walk of `lean-bridge/Audit.lean` | [#670](https://github.com/MGYamada/Vastitas/pull/670) | [#672](https://github.com/MGYamada/Vastitas/pull/672) |
| 5 | This map, the reference, guide and verification chapters, the ADR 0001 amendment and the glossary | [#671](https://github.com/MGYamada/Vastitas/pull/671) | [#672](https://github.com/MGYamada/Vastitas/pull/672) |

Status terms below:

- **Implemented** is code in the kernel that the compiler runs.
- **Proved (oracle)** is a theorem about kernel definitions in
  `lean/VastitasOracle/`, mathlib-free.
- **Proved (bridge)** is a mathlib theorem in `lean-bridge/`.
- **Tested** is a regression or integration test, including native
  execution. Testing is not a proof of all inputs.
- **Not claimed** is outside this profile; the
  [not-claimed list](#not-claimed) records it.

## Evidence key

Kernel files are in `lean-kernel/VastitasKernel/`, and kernel regressions run
from `scripts/check_kernel_regressions.sh`. Oracle files are in
`lean/VastitasOracle/`, and bridge files in
`lean-bridge/VastitasBridge/Differential/`.

| Key | Implementation | Tests | Theorems |
| --- | --- | --- | --- |
| **R — rules and steps** | `IndexedPrimitiveDescriptors.lean` (`ReverseRule`, `PassKind`, the field `reverse`), `IndexedPrimitiveRegistry.lean` (the rule of every entry; `smoothApply` and `cotangentJacobian` with their lowerings), `IndexedSmoothContracts.lean` (their contracts), `SmoothRuntime.lean` (`ratPoint`, `applyPoint`, `jacobian`, `jacobianStep`) | `SmoothRuntimeRegression` (the Jacobian table of g; a table step equals `cot` and the saved pullback; a seed over another point fails). The rule of each binding is tested through the compiled programs: the counts of Jacobian steps, compiled tapes and maps read through `compose` | Oracle `SmoothJacobian` (`jacobianStep_eq_of_output`, `jacobianStep_eq`, `pullback_congr_point`, `pullback_stepwise_applyPoint`, `smoothApply_sound`, `cotangentJacobian_sound`, `registry_reverse_sound`); `IndexedDescriptorDemo.directionalDerivative_reverseSound` |
| **G — generation** | `IndexedReverse.lean` (`resolve`, `compileSite`, `forwardLets`, `backwardBody`, `Entry.generated`, `Entry.declarations`, `rewriteFunction`, `generate`); `Limits.lean` and `compiler-limits.json` (`reverseLeaves`) | `ReverseCoreRegression`; `tests/reverse_core.rs` | Oracle `SmoothReverseCore` (what the templates compute), `IndexedReverseCore` (the structure of `generate`) and `SmoothReverseCompiled` (every entry of a compiled module, and the term at a compiled site) |
| **V — check again** | `IndexedReverse.lean` (`termEq` to `moduleEq`, `validate`, `Compiled`, `compile`, which runs the Core audit); `IndexedAuthorityCheck.lean` and `ResourcePure.lean` (the field `compiled`); `Main.lean` and `ResourceCodegen.lean` (generation from `compiled`) | The forged modules of `ReverseCoreRegression`; `the_wire_cannot_name_the_compiled_declarations` | Oracle `IndexedReverseCore` (`moduleEq_sound`, `validate_iff`, `compile_fails_only_by_audit`, the `compiled_*` and `public_*` theorems) and `SmoothReverseCompiled` (`public_wire_entries`, `legacy_wire_entries`, `public_resource_entries`, `public_pure_entry_computes`) |
| **E — emitted code** | The lowerings of the step bindings; `IndexedCodegen.lean` (the declaration of each distinct Jacobian table) | `generated_lean_matches_the_emit_fixtures` (`tests/emit_golden.rs`); `ReverseCoreRegression` ("1, 2 and 6 steps along one declared map give one Jacobian table", "two declared maps with one Jacobian table give one declaration", "a step that no emitted function calls gives no declaration"); the native fixtures `smooth_reverse_programs` and `smooth_reverse_extended` of `scripts/check_indexed_native.sh` | Tested only |
| **B — bridge** | — | `lean-bridge/Audit.lean` (requires every name below, and walks the constants of each proof) | Bridge `ReverseCore.lean` (`backward_eq_cot_kaehler`, `pullback_eq_cot_kaehler`; the `compiled_*_entry_frechet`, `compiled_*_entry_fderiv_adjoint`, `compiled_*_entry_kaehler` and `compiled_*_entry_cot_kaehler` theorems; `compiled_site_frechet`, `compiled_differential_site_frechet` and the `site_*_rewrite_frechet` theorems; `compiled_entries_frechet` and the public-path `*_frechet` theorems) |

Every theorem of `SmoothReverseCore` is stated on the kernel's own
definitions (`forwardLets`, `backwardBody`, `Entry.generated`) and on the
kernel evaluator, through `IndexedEvaluation.Evaluates`. Its premises about
the module are explicit: the step declarations (`StepsDeclared`,
`StepFormed`, `MorphismsDeclared`), the declaration of the forward step and
the lookup of the generated function.
`SmoothReverseCompiled.entry_well_formed` discharges all of them for every
entry of a compiled module. The premises that stay concern the arguments of a
call and the activation of a site; the [gaps](#gaps) list them.

<a id="chain-rule-independence"></a>

Six oracle theorems use the oracle chain rule
(`SmoothCalculus.backward_eq_cot`): `pullback_chain_cot`,
`saved_function_cot`, `compiled_saved_entry_cot`,
`compiled_recomputed_entry_cot`, `EntryComputes.saved_cot` and
`EntryComputes.recomputed_cot`. The others use the stepwise pullback and the
table steps. The oracle's import closure contains `SmoothCalculus`, so
chain-rule independence is checked on the constants that each proof uses. It
is checked, not proved:

- `scripts/check_chain_rule_free.lean`, a step of the CI job "Lean proofs and
  axiom audit", walks the constants of the 33 oracle theorems that the
  [specification](spec/reverse-core.md) states without the chain rule. It
  fails if one reaches a chain-rule theorem of `SmoothCalculus`. Its positive
  controls, `saved_function_cot`, `compiled_saved_entry_cot` and
  `compiled_recomputed_entry_cot`, must reach one.
- `lean-bridge/Audit.lean` walks the constants of the 28 bridge and oracle
  theorems of compiled entries and sites. It fails if one reaches the chain
  rule of `ChainRule.lean` or of the oracle, or `pderiv_aeval`. Its positive
  controls are `compiled_saved_entry_cot` and `checked_pullback_kaehler`.

<a id="acceptance-conditions"></a>

## Acceptance conditions

The acceptance example is the Stage 3 example
[`examples/packages/smooth-differential/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/smooth-differential),
unchanged. Each observation has its own failure code from 1 to 25. "Code k"
below is that observation.

| Condition | Status and evidence |
| --- | --- |
| <a id="t1"></a>T1. Transform: from the checked Core of a smooth program, the kernel produces forward Core (the primal value and the residuals as ordinary Core values) and backward Core (the pullback from the residuals and a seed); the transform works on checked IR only, and Rust derives nothing | **Implemented**: `Reverse.generate`, run by `Reverse.compile` on `executable.core` (G). No file under `src/` changes. **Tested**: `acceptance_sites_compile_to_generated_backward_functions` (the 22 reverse sites of the acceptance example give 22 generated functions, placed first and numbered after the source functions; each is called once; every Jacobian step lies in a generated function and names a table that the module declares once, a literal without variables; the 4 runtime reverse passes and their callers; the 4 unit covectors that the differentials pass as seeds; no call of `SmoothRuntime.differential`, `backward`, `linearize` or the recomputed mode); `ReverseCoreRegression` ("the fixture has one entry per reverse site", "every site of the fixture is compiled" for 45 sites, "the parameter h is one opaque step", "the let-bound map is read through: two declared steps", "both backward calls on the let-bound tape are compiled"). **Proved (oracle)**: `SmoothReverseCore.forwardLets_evaluates` and `forwardLets_primal` (the forward Core binds the images of the input point, which satisfy the residual relation, the last with the coordinates of the primal value); `SmoothReverseCompiled.compileSite_term` (the term at a compiled site binds the input point and continues with the forward Core); `IndexedReverseCore.generate_shape`, `generate_keeps_function`, `generate_entry_mem`, `generate_entry_function`, `generate_entry_declaration` (the generated functions and declarations are in the module, and every source function keeps its header); `SmoothReverseCompiled.generate_formed` (every entry of the ledger is well formed); `SmoothJacobian.registry_reverse_sound` (every registry entry keeps the promise of its derivative rule). |
| <a id="t2"></a>T2. Check again: the generated Core passes the same checker, typing and audits as source-derived Core; forged reverse Core is rejected | **Implemented**: `Reverse.compile` runs `Core.Typing.checkModule`, the Core audit of source-derived executable Core, on the generated module (V). A failed audit is `E_INTERNAL_REVERSE`. The source passes also run `validPass`, the provenance and static-target audit of their lowering records; generated functions have no lowering records and skip that audit. `validate` states that the generated module and the ledger are what `generate` returns for the source module. `compile` builds them that way, so this holds by construction: it is the certificate `Compiled.validated`, not a check, and it cannot detect an error of the generator. What rules out such an error is the oracle: its theorems are stated on the kernel's own templates and on every entry of a compiled module (T4, T5), so a generator change that breaks them fails the oracle build. The compiled declarations and functions have reserved names (`__vastitas_rd…`, `__vastitas_rf…`). **Tested**: the forged modules of [A4](#a4), which show that validation and the Core audit tell them from the compilation; `the_wire_cannot_name_the_compiled_declarations`. **Proved (oracle)**: `IndexedReverseCore.moduleEq_sound` (with `termEq_sound`, `termsEq_sound`, `functionEq_sound`, `functionsEq_sound`), `validate_iff`, `validate_sound`, `validate_no_entries`, `compile_fails_only_by_audit` (`compile` fails only when the Core audit rejects the generated module); `compiled_generate`, `compiled_entry_resolves`, `compiled_functions_total`, `compiled_main_total` (the compiled module is what `generate` returns for the executable Core, every entry resolves, and every function is total and typed); `SmoothReverseCompiled.entry_well_formed` (the forward, backward and seed steps of every entry are declarations of the compiled module, with their rules). |
| <a id="t3"></a>T3. Saved and recomputed residuals: both policies are expressible, and they agree | **Implemented**: `backwardBody` and `stepBinding`. A saved function takes every point, the residuals and the primal value; a recomputing function takes r₀ and evaluates in its body the images that its steps read. An opaque step runs the runtime reverse pass in the site's policy. **Tested**: codes 12 and 25; `each_pullback_binding_compiles_to_its_own_residual_policy` (`tests/smooth_differential.rs`); `acceptance_sites_compile_to_generated_backward_functions` (the two recomputing functions evaluate 5 images); `a_branch_chooses_the_map_of_a_reverse_pass` (`recomputed`, codes 4 and 8 of the corpus package: an opaque step in recomputed mode); `ReverseCoreRegression` ("the recomputing pullback keeps its mode; every other site saves", "the recomputing pullback reads through the let: three declared steps"). **Proved (oracle)**: `SmoothReverseCore.recomputed_function_evaluates`, `recomputed_function_pullback`, `saved_eq_recomputed`; `SmoothReverseCompiled.compiled_saved_entry` and `compiled_recomputed_entry` (for every entry of a compiled module, in its mode). **Proved (bridge)**: the Fréchet and Kähler meaning of both modes (T4, A3). |
| <a id="t4"></a>T4. Theorem: the forward Core evaluates to the primal value with residuals that satisfy the residual relation; the backward Core, for every seed over the output, evaluates to η ∘ D⟦P⟧(x); for the generated Core itself, reusing the chain rule and the meaning theorems of Stage 3 | **Proved (oracle)**: forward, `SmoothReverseCore.forwardLets_evaluates` and `forwardLets_primal`, for the primal value of the chain of the step programs. That this chain composes to the site's map value is `resolve_factors`, which only `compiled_site_evaluates` uses (T5). Backward, at any points, `saved_function_evaluates`; under the residual relation, `backwardPass_eq_pullback` and `saved_function_pullback` (the saved-mode pullback along the chain of the step programs, without the chain rule). For every entry of a compiled module, `SmoothReverseCompiled.compiled_saved_entry` and `compiled_recomputed_entry`, whose module premises `entry_well_formed` discharges. A seed over another point gives ⊥: `saved_function_foreign_seed`, `compiled_saved_entry_foreign_seed`. Meaning, through the Stage 3 chain rule `SmoothCalculus.backward_eq_cot`: `saved_function_cot`, `pullback_chain_cot`, `compiled_saved_entry_cot` and `compiled_recomputed_entry_cot` (`some ⟨x, cot F x η⟩` for the chain F of the step programs). On every public path, `public_wire_entries` (protocol 7), `legacy_wire_entries` (protocols 2–6), `public_resource_entries` and `public_pure_entry_computes` (protocols 8/9): every entry of the compiled module satisfies `EntryComputes`. **Proved (bridge)**: `compiled_saved_entry_frechet` and `compiled_recomputed_entry_frechet` (the call evaluates to the covector `(covector η).comp (fderiv ℝ (realProgram F) x)`), from the oracle's `compiled_saved_entry` and `compiled_recomputed_entry` and the Stage 3 theorem `Frechet.pullback_covector_eq_comp_fderiv`, without `ChainRule.lean`; `compiled_entries_frechet` and, on every public path, `public_wire_entries_frechet`, `legacy_wire_entries_frechet`, `public_resource_entries_frechet` and `public_pure_entry_frechet`. The premises that stay concern the call. Its arguments evaluate to one program per opaque step, the points and the seed. For a saved site, the points satisfy the residual relation. The chain is well typed from n to m coordinates, and the seed lies over the image with m components. The Fréchet theorems also need an input point with n coordinates ([#668](https://github.com/MGYamada/Vastitas/issues/668)). |
| <a id="t5"></a>T5. Refinement: the generated code agrees with the runtime reverse pass on the acceptance example, which may stay as a reference | **Tested**: the acceptance example prints `42` through compiled Core, and the 25-code expectations of `mutated_observations_change_the_native_result` are unchanged (A1). `VastitasAlgebraTest.ReverseExampleRegression` evaluates `main` of the acceptance example before and after the compilation: observational agreement of all 25 codes. `ReverseCoreRegression` compares each compiled site with its source call ("each compiled site evaluates to the value of the source site, failures included") on the 45 closed sites of `CotangentRegression.cotangentFixture`, a hand-built Core program that differs from the acceptance example; the compiled fixture and the compiled extended module also evaluate to 42. The corpus packages run with their mutations (A6). **Proved (oracle)**, for one site: `SmoothReverseCompiled.compiled_site_evaluates` (the term that `compileSite` returns and the source call evaluate to the same value, for a pullback in either mode, a differential and the reverse pass of a tape, direct or bound by a `let`), from `compileSite_term` and `resolve_factors` (the maps that the compilation reads compose to the value of the map operand); the local theorems `SmoothReverseCore.site_saved_rewrite`, `site_recomputed_rewrite`, `site_differential_rewrite` and `site_tape_rewrite`. <a id="site-premises"></a>Its premise that the module keeps the source bindings holds for every compiled module (`compiled_rules`). Applying `compiled_site_evaluates` inside a rewritten function needs six facts that no theorem discharges ([#665](https://github.com/MGYamada/Vastitas/issues/665)). The `let` definitions in scope agree with the activation (`DefsAgree`), and the operands read no symbol that the compilation binds. `rewrite` places the returned term at the site, and the ledger entries before the site are well formed. The map operand evaluates to a well-typed program. The source call of the theorem is the call with the same operands, which the compilation has already rewritten. **Proved (bridge)**: `compiled_site_frechet` and `compiled_differential_site_frechet` (a compiled pullback or differential site and its source call evaluate to the covector η ∘ DM(x) of the site's map value M), under the same premises; `site_saved_rewrite_frechet`, `site_recomputed_rewrite_frechet`, `site_differential_rewrite_frechet` and `site_tape_rewrite_frechet` (the local theorems). The direct tape form `backward(linearize(M, x), η)` has the local theorem only, and a tape bound by a `let` has no Fréchet theorem ([#668](https://github.com/MGYamada/Vastitas/issues/668)). **Not claimed**: refinement of a whole module ([#665](https://github.com/MGYamada/Vastitas/issues/665)). |
| <a id="a1"></a>A1. The Stage 3 acceptance example runs its reverse passes through generated Core and prints `42`; a mutation test flips its codes | **Tested**: `smooth_example_checks_builds_and_executes`; `mutated_observations_change_the_native_result` (every code 1–25 flipped by some group of mutations); `acceptance_sites_compile_to_generated_backward_functions`. The [per-code table](#acceptance-example-by-code) shows which steps each code reads. |
| <a id="a2"></a>A2. Oracle theorem: generated forward and backward Core are correct, relative to the oracle chain rule | **Proved (oracle)**: the theorems of T1, T3, T4 and T5. The statements relative to the chain rule are the six of [chain-rule independence](#chain-rule-independence): `pullback_chain_cot`, `saved_function_cot`, `compiled_saved_entry_cot`, `compiled_recomputed_entry_cot`, `EntryComputes.saved_cot` and `EntryComputes.recomputed_cot`. `scripts/check_chain_rule_free.lean` checks on constants, with positive controls, that the 33 theorems it lists, which the specification states without the chain rule, reach no chain-rule theorem. A theorem of T1–T5 that the script does not list, such as `generate_shape` or `backwardPass_eq_pullback`, is not checked. |
| <a id="a3"></a>A3. Bridge theorem: the generated backward Core equals the adjoint of `fderiv` of the accepted program | **Proved (bridge)**: `compiled_saved_entry_frechet` and `compiled_recomputed_entry_frechet` (for every entry of a compiled module, the generated backward Core is η ∘ DF(x) for mathlib's `fderiv ℝ` of the chain F of the step programs), and their componentwise forms `compiled_saved_entry_fderiv_adjoint` and `compiled_recomputed_entry_fderiv_adjoint`; for the source site, `compiled_site_frechet` and `compiled_differential_site_frechet`, under the premises of T5, and the local `site_*_rewrite_frechet` theorems (η ∘ DM(x) for the site's map value M); on every public path, `compiled_entries_frechet`, `public_wire_entries_frechet`, `legacy_wire_entries_frechet`, `public_resource_entries_frechet` and `public_pure_entry_frechet`. The Kähler corollaries: `compiled_saved_entry_kaehler` and `compiled_recomputed_entry_kaehler` (the fiber at x of the Kähler pullback), `compiled_saved_entry_cot_kaehler` and `compiled_recomputed_entry_cot_kaehler` (`cot` of the composite map), through `backward_eq_cot_kaehler` and `pullback_eq_cot_kaehler`, which use Kähler functoriality (`cot_compose_kaehler`). No proof uses the kernel chain rule or `pderiv_aeval`; `lean-bridge/Audit.lean` requires each name and checks this on constants, with positive controls. The premises are those of T4. The Fréchet theorems need an input point with n coordinates. The direct tape form has the local theorem only, and a tape bound by a `let` has no Fréchet theorem ([#668](https://github.com/MGYamada/Vastitas/issues/668)). |
| <a id="a4"></a>A4. Rejected: forged reverse Core, a residual from another point, mismatched endpoints, a seed over another point (the failure value), and a tampered tape | See [rejections](#rejections). |
| <a id="a5"></a>A5. Byte-level codegen tests for the generated reverse functions | **Tested**: `generated_lean_matches_the_emit_fixtures` pins `tests/fixtures/emit/smooth-differential.lean`, `reverse-branch.lean`, `reverse-tape.lean` and `reverse-domain.lean`, and the regenerated `smooth-cotangent.lean`, `smooth-metric.lean` and `stdlib-differential.lean`; non-smooth goldens are unchanged. `ReverseCoreRegression` ("the generated function of one declared step, byte for byte", the pullback along `gf` with the table `[[4t]]`; "the lowering calls the compiled steps and no runtime reverse pass at a compiled site"; "one generated function per site, before the source functions"). The native fixtures `smooth_reverse_programs` and `smooth_reverse_extended` compile and print `42`. **Not claimed**: native refinement of the generated code. |
| <a id="a6"></a>A6. No general differentiation of branches, loops or recursion; a branch may still choose which smooth map is built | **Implemented**: `ReverseRule` has the cases `none`, `morphism`, `chain`, `tape` and `pass`, and none differentiates a condition. A map that a branch chooses is an opaque step. The language has no loops, and the checker rejects recursion ([Core language](language/functions.md#calls)). **Tested**: `a_branch_chooses_the_map_of_a_reverse_pass` (`tests/emit_corpus/reverse-branch/`: four sites, each with one opaque step for the branch and, in `squared`, a Jacobian step along `sq`; both arms observed; mutations print `212` and `127`); `ReverseCoreRegression` ("the map chosen by a branch is one opaque step"). |

<a id="rejections"></a>

### Rejections

| Rejection | Outcome | Evidence |
| --- | --- | --- |
| Forged reverse Core | Static. No source or wire request can name a compiled declaration or supply Core, so the compiled module is the one that `generate` returns (`compile_fails_only_by_audit`). The forged modules below are not inputs of any pipeline path: they show that `validate`, and the Core audit for the ill-typed ones, tell a module from the compilation. An error of the generator itself is ruled out by the oracle theorems (T4, T5), not by validation. | **Tested**: `ReverseCoreRegression`: a backward function that returns its seed; the two steps of the shears in the opposite order (well typed, `main` changes); a step with its input and output points exchanged; a step along another declared map; a generated function under another owner; a missing generated function (Core audit); an extra function; a site left uncompiled; a function returning a covector over another object (Core audit); a ledger with another mode or a missing entry. `the_wire_cannot_name_the_compiled_declarations`: a declaration, morphism or function under a compiler name (`E_RESERVED`), a call of one (`E_NAME`), and the operations `smooth_apply` and `cotangent_jacobian` (`E_PROTOCOL`), for `check` and `emit`. **Proved (oracle)**: `IndexedReverseCore.validate_sound`, `compiled_codegen_input`, `legacy_compiled_codegen_input`, `generated_pure_entry_compiled`, `public_pure_entry_compiled`, `public_resource_compiled` (the compiled module of every public path is what `generate` returns for its executable Core; that code generation uses it is proved for the protocol 8/9 pure path, and read from `Main` for protocols 2–7). |
| A residual from another point | Static for a forged residual: the forward Core binds every residual, and no request can supply another; validation tells a forged module from the compilation. A source program that pulls back through the wrong intermediate point passes a seed over another point to the next site, which gives the failure value ⊥. | **Tested**: `ReverseCoreRegression` ("a residual from another point: a site passing the input point as the image is rejected", well typed); codes 9 and 10. **Proved (oracle)**: `SmoothReverseCore.forwardLets_evaluates` and `forwardLets_primal` (the residuals are the images); `SmoothReverseCompiled.compiled_saved_entry_foreign_seed`. |
| Mismatched endpoints | Static. The source call is `E_ENDPOINT`, as in Stage 3. The Core audit checks the generated module again. The compilation forms points and covectors only over objects that its families cover; any other site keeps the runtime reverse pass. | **Tested**: `smooth_endpoint_errors_name_the_failing_role`, `acceptance_rejects_wrong_objects_and_a_gradient_primitive_statically` (`tests/smooth_differential.rs`); `ReverseCoreRegression` (a generated function whose declared result is a covector over another object fails the Core audit). `validate_iff` characterizes validation. The Core audit of a forged step is tested, not proved. |
| A seed over another point | The failure value ⊥, at run time. | **Tested**: codes 8, 11 and 14; the corpus packages (`reverse-branch` codes 256 and 512, `reverse-tape` codes 32 and 64, compiled and runtime). **Proved (oracle)**: `SmoothReverseCore.saved_function_foreign_seed`, `backwardPass_foreign_seed`; `SmoothReverseCompiled.compiled_saved_entry_foreign_seed` (every saved entry of a compiled module); `SmoothJacobian.jacobianStep_eq_of_output`. The bridge theorems take a seed over the image as a premise. |
| A tampered tape | Static. A tape has no source or wire form, as in Stage 3. The compiled reverse pass of a tape bound by `let` reads the map and the point of its `linearize` and forms its own residuals. A tape from another point rejects the seed with ⊥. | **Tested**: `raw_wire_rejects_forged_fiber_and_tape_records` (`tests/smooth_differential.rs`); code 14; `a_tape_bound_by_let_compiles_and_a_tape_passed_to_a_function_keeps_its_routine`. No forged module of `ReverseCoreRegression` changes a tape site. **Proved (oracle)**: `IndexedReverseCore.validate_iff` (validation tells every change from the compilation, a tape site's included). |

<a id="acceptance-example-by-code"></a>

## Acceptance example by code

The acceptance example has 22 reverse sites: two in `stepwise`, one in each
of the three gradient functions and 17 in `main`. Each compiles to one
generated function. Of their 32 steps, 28 are Jacobian steps and 4 are opaque
steps. `stepped` (code 1), `detour` (code 9) and `dg` (code 18) are each
computed once and read by several codes.

| Code | Observation | Reverse sites it reads | Steps |
| --- | --- | --- | --- |
| 1, 6, 7 | `stepped`: 12 dt, over 3 and not over 18 | `stepwise`: the pullback along `g` at f(3), then along `f` at 3 | Jacobian, 1 + 1 |
| 2 | `stepped` equals the pullback along `gAfterF` | `main`: along `gAfterF`, read through its `let` | Jacobian, 2 |
| 3 | `stepped` equals the pullback along `composite(gAfterF)` | `main`: along `composite(gAfterF)` | **Opaque**: one runtime reverse pass over the composite |
| 4 | `stepped` equals the pullback along `gf` | `main`: along `gf()` | Jacobian, 1 |
| 5 | `same(gAfterF, gf())` | None | — |
| 8, 11 | `wrong`: a seed at 17 gives ⊥, which reads `(0, 0)` | `main`: along `gAfterF` | Jacobian, 2; the step along `g` gives ⊥ |
| 9 | `detour`: the wrong intermediate point gives ⊥ | `main`: along `g` at f(2), then along `f` at 3 | Jacobian, 1 + 1; the step along `f` gives ⊥ |
| 10 | ⊥ survives the identity | `main`: along `idL`, after `detour` | Jacobian, 1 |
| 12 | Recomputed equals saved | `main`: recomputed and saved along `gAfterF` | Jacobian, 2 + 2; the recomputing function evaluates 2 images |
| 13 | The tape pass equals the saved pullback | `main`: `backward(linearize(gAfterF, x), seed)` and the saved pullback | Jacobian, 2 + 2 |
| 14 | A tape from 3 rejects a seed at 16 | `main`: `backward(linearize(sq(), x), …)` | Jacobian, 1 |
| 25 | Recomputing evaluates each outer map at its own point | `main`: recomputed along `compose(sq(), gAfterF)` | Jacobian, 3; the recomputing function evaluates 3 images |
| 15 | The identity of the plane | `main`: along `idP` | Jacobian, 1 |
| 16, 17 | The shears at the origin | `main`: along `compose(shearB(), shearA())` and `compose(shearA(), shearB())` | Jacobian, 2 each |
| 18 | `dg` = (2, 1) at (1, 2) | `main`: `differential(g(), p)` | Jacobian, 1; its seed is the unit covector at g(1, 2) |
| 19, 20, 21 | The Euclid, Skew and Lorentz gradients | `gradient_euclid`, `gradient_skew`, `gradient_lorentz`: `differential(h, p)` | **Opaque**: the parameter `h`, one runtime reverse pass each |
| 22 | Two metrics give two gradients | `gradient_euclid` and `gradient_skew` | **Opaque** |
| 23 | sharp after flat | None | — |
| 24 | `dg` pairs with the Skew gradient to 2 | `dg` and `gradient_skew` | Jacobian, 1, and **opaque** |

The three gradient functions pull back along their parameter `h`, so their
steps are opaque even though every caller passes the declared `g`.
`composite(gAfterF)` expands the composite into one map at run time, and the
compilation does not open its result. `acceptance_sites_compile_to_generated_backward_functions`
pins these four runtime reverse passes and their callers.

## Related issues

| Issue | Met by this profile | Open |
| --- | --- | --- |
| [#361](https://github.com/MGYamada/Vastitas/issues/361) compiled pullbacks | Reverse Core that the kernel emits and checks again with the Core audit, for exact QQ polynomial maps; saved and recomputed residuals; the noncommuting shears and nonlinear composition through Jacobian steps (codes 1, 2, 4, 16 and 17) | Opaque steps compiled through specialization; preservation through passes (#164) |
| [#290](https://github.com/MGYamada/Vastitas/issues/290) proof-carrying differentiation | The theorem over generated forward and backward Core, restricted to the finite smooth profile (T4); a residual from another point is rejected (A4) | The derivation language, selected-backward and within contracts, and a whole-module refinement theorem ([#665](https://github.com/MGYamada/Vastitas/issues/665)) |

<a id="gaps"></a>

## Gaps

- **Whole-module refinement is not proved.** The oracle proves the generated
  function of every entry, and the term at each compiled site against its
  source call (`compiled_site_evaluates`). Applying it inside a rewritten
  function needs six facts that no theorem discharges; [T5](#site-premises)
  lists them. A refinement theorem for every function is a follow-up
  ([#665](https://github.com/MGYamada/Vastitas/issues/665)). The kernel
  regressions compare the result of `main` before and after the compilation:
  of the acceptance example, of the cotangent fixture and of the extended
  module. The corpus packages run only compiled, against values derived by
  hand. The regressions compare single sites only on the 45 closed sites of
  the cotangent fixture.
- **The compiled-entry theorems keep premises.** One program per opaque step,
  composable programs and, for a saved site, the residual relation are
  premises on the arguments of a call. That consecutive steps share their
  objects is not proved, and no theorem needs it. The Fréchet theorems assume
  an input point with n coordinates. The direct tape form has the local bridge
  theorem only, and a tape bound by a `let` has no Fréchet theorem.
  Discharging these is a follow-up ([#668](https://github.com/MGYamada/Vastitas/issues/668)).
- **Opaque maps and escaping tapes use the runtime reverse pass.** Opaque
  steps are function parameters, values of branches and calls,
  `composite(…)`, and maps that `reverseLeaves` does not reach. A map operand
  whose own `compose` calls exceed the budget is one opaque step as a whole,
  so none of its maps is compiled, and the order of the operands decides
  which part of a map fits. A tape passed to or returned from a function keeps
  `backward`, and so does a tape bound by a `let` over a call result or a
  branch value ([#666](https://github.com/MGYamada/Vastitas/issues/666)). A
  whole site stays a call of the
  runtime reverse pass when its maps cannot be read, or when a family of the
  generated Core does not cover one of its objects (`reverse-domain`). It
  also stays when its declarations would exceed the 4096 declaration ids of a
  module. A function whose compiled Core would exceed `generatedLets` keeps
  all its sites; no test reaches that budget. Compiling a function for each
  static map argument is a follow-up
  ([#664](https://github.com/MGYamada/Vastitas/issues/664)).
- **An opaque step evaluates its map forward twice:** once in the forward
  Core for its image, and again inside the runtime reverse pass ([#668](https://github.com/MGYamada/Vastitas/issues/668)).
  A recomputing function does not bind the image of a last opaque step,
  which nothing reads.
- **The input point is not evaluated once.** The forward Core binds r₀ as the
  point operand, so a composite point such as `compose(f(), x)` is evaluated
  by each step that reads it: the first forward step and the first backward
  step. The runtime reverse pass evaluated it once per pass. Each image is an
  evaluated point, a program node with one constant polynomial per
  coordinate, which every step that reads it evaluates again; see
  [storage ownership §7.10](storage-ownership.md#residual-retention).
- **A let-bound tape's forward Core runs again at each reverse pass.** Each
  reverse pass of the tape is a site that copies the tape's map and point.
  The tape's own `let` stays in the function.
- **No budget bounds the compilation's work or the emitted text.** Reading a
  site's maps looks up `let` definitions in a list, and a copyable compound
  leaf is bound again at each site that reads it. A size and work budget with
  a fallback to the runtime reverse pass is a follow-up
  ([#673](https://github.com/MGYamada/Vastitas/issues/673)).
- **Validation is a certificate, not a check.** `validate` states that the
  generated module and the ledger are what `generate` returns for the source
  module; `compile` builds them that way, and `compile_fails_only_by_audit`
  proves that only the Core audit can fail. No independent checker
  re-derives the templates, so validation cannot detect an error of the
  generator. The oracle theorems, stated on the kernel's own templates and on
  every entry of a compiled module, are what rule such errors out. `compile`
  also runs `generate` a second time inside `validate`.
- **The compilation runs once, on source Core.** An opaque step calls a
  `cotangent_pullback` declaration, whose rule is a reverse pass, so
  compiling generated Core again would compile that step again.
- **No floats and no performance claims.** Arithmetic is exact over QQ, and
  nothing is measured (#222).
- **Residual retention is not reached.** Residuals are immutable pure Core
  values: a saved site retains them, and a recomputing site recomputes them.
  The storage-backed retention of
  [storage ownership §7.10](storage-ownership.md#residual-retention),
  with value versions and invalidation, does not arise.

<a id="proof-boundary"></a>

## Proof boundary

- **Proved (oracle).**
  - Every registry entry keeps the promise of its derivative rule, and a
    Jacobian step is the pullback along its declared map at the saved point.
  - The forward Core binds the images, which satisfy the residual relation,
    the last with the coordinates of the primal value.
  - For every entry of a compiled module, a call of its generated function
    evaluates to the saved- or recomputed-mode pullback along the chain of
    the step programs, under the residual relation for a saved site. A seed
    over another point gives ⊥. Every entry of every module that a public
    path accepts or emits satisfies this.
  - Relative to the oracle chain rule, that value is the cotangent pullback
    `cot` of the composite map.
  - The term at a compiled site evaluates as its source call, for a pullback,
    a differential and the reverse pass of a tape. Applying it inside a
    rewritten function needs six facts that no theorem discharges
    ([T5](#site-premises),
    [#665](https://github.com/MGYamada/Vastitas/issues/665)).
  - Structural equality is sound, validation characterizes the result of
    `generate`, and `compile` fails only by the Core audit. The compiled
    module of every public path is that result, with total and typed
    functions. That code generation uses
    it is proved for the protocol 8/9 pure path and read from `Main` for
    protocols 2–7.
- **Proved (bridge).**
  - For every entry of a compiled module, and on every public path, the
    generated backward Core is η ∘ DF(x) for mathlib's `fderiv ℝ` of the
    chain F of the step programs, given an input point with n coordinates.
  - Its components are `cot` of the composite map and the fiber at x of the
    Kähler pullback.
  - A compiled pullback or differential site and its source call evaluate to
    η ∘ DM(x) for the site's map value M, under the premises of the oracle's
    site theorem. The direct tape form has the local theorem only, and a tape
    bound by a `let` has no Fréchet theorem
    ([#668](https://github.com/MGYamada/Vastitas/issues/668)).
- **Checked, not proved.** Chain-rule independence.
  `scripts/check_chain_rule_free.lean` and `lean-bridge/Audit.lean` walk the
  constants of every theorem stated without the chain rule, with positive
  controls ([chain-rule independence](#chain-rule-independence)).
- **Tested only.**
  - Agreement of the result of `main` before and after the compilation, on
    the acceptance example, the cotangent fixture and the extended module,
    and of the closed sites of the cotangent fixture with their source calls.
    The corpus packages against values derived by hand.
  - The listed forged modules, which validation is proved to tell from the
    compilation, and the wire requests that name compiled declarations.
  - The generated code, byte for byte, and its native execution.
  - The budget fallbacks of `reverseLeaves` and of the declaration bound.
- **Assumed.** As in Stage 3: the Rust frontend's parsing, the Lean-to-C
  toolchain and the C compiler, Lean core `Rat` and GMP, and mathlib itself.

<a id="not-claimed"></a>

## Not claimed

- Refinement of a whole compiled module; native refinement of the generated
  code.
- Floating-point realization of the reverse Core with an error contract
  ([#667](https://github.com/MGYamada/Vastitas/issues/667)), and
  performance against equivalent C (#222).
- Optimizer preservation of (primal, pullback) pairs (#164).
- Differentiation of branches, loops or recursion.
- Forward mode and HVP (#161); custom rules (#163); checkpointing beyond
  save-all and recompute-all (#544); complex AD (#71).
- Compiled Core for opaque steps, for tapes across functions, and for
  `composite(…)`. Follow-ups:
  [#664](https://github.com/MGYamada/Vastitas/issues/664), which also covers a
  compile-time Jacobian table for `composite(…)`, and
  [#666](https://github.com/MGYamada/Vastitas/issues/666).
- A refinement theorem for every function of a compiled module
  ([#665](https://github.com/MGYamada/Vastitas/issues/665)), and the premises
  that the compiled-entry theorems keep
  ([#668](https://github.com/MGYamada/Vastitas/issues/668)).

## Validation

The full suite ran once, on the integrated batch 2 head `f3938f6`, each Lean
and cargo job under the machine-wide lock and the heavy jobs one at a time.

| Command | Result |
| --- | --- |
| `lake -d lean-kernel build VastitasKernel VastitasPromotion VastitasPublicTest VastitasStorageTest VastitasAlgebraTest vastitas-kernel storage-native-fixture numerical-native-fixture` | pass |
| `bash scripts/check_kernel_regressions.sh` | pass, with `ReverseCoreRegression` |
| `bash scripts/check_indexed_native.sh` | pass, with `smooth_reverse_programs` and `smooth_reverse_extended` (42) |
| `bash scripts/check_storage_native.sh` | pass |
| `cargo fmt --check`, `cargo clippy --locked --all-targets -- -D warnings` | pass |
| `cargo test --locked --all-targets` | 541 passed, 0 failed, 14 ignored |
| `python3 scripts/capture_emit.py --kernel-fixtures --compare` against `05fd395` | only the emit of `smooth-cotangent`, `smooth-differential`, `smooth-metric` and `stdlib-differential` differs; the corpus packages and the two kernel fixtures are new |
| `lake -d lean build` | pass |
| `scripts/audit_axioms.lean` | 42,100 declarations in 305 modules |
| `scripts/check_chain_rule_free.lean` | 33 theorems reach none of 8 chain-rule theorems; 3 controls reach them |
| Oracle `spec_resolve.lean` | 65 theorems and 3 kernel definitions |
| `replay_lean.sh lean VastitasOracle`, `replay_lean.sh lean VastitasKernel` | pass |
| `check_axiom_audit.py` | 21 cases |
| `check_spec_lean.py`, `check_oracle_core.lean`, `check_edit_acceptance.lean` | pass |
| `lake -d lean-bridge build` | pass |
| Bridge `Audit.lean` | 1,049 declarations; chain-rule independence for 28 theorems |
| `replay_lean.sh lean-bridge -v VastitasBridge` | pass |
| `check_boundaries.py` and its unit tests | pass |
| Bridge `spec_resolve.lean` | 34 theorems |
| `check_docs.py`, `check_spec.py`, `check_primitive_table.py`, `mdbook build`, `check_book.py` | pass |

These are native and proof results of one machine. Native results are not
refinement proofs.
