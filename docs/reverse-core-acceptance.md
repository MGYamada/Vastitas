# Compiled reverse Core acceptance

This map links each acceptance condition of compiled reverse Core to its
implementation, tests, oracle and bridge theorems, and native evidence.
Compiled reverse Core extends the finite smooth profile of historical Stage 3
([acceptance map](stage3-acceptance.md)). The kernel compiles the reverse
passes of a checked program into Core, checks that Core again, and the oracle
and the bridge prove it correct
([tracker #623](https://github.com/MGYamada/Vastitas/issues/623)). The map
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
  value.
- The points r₀, …, r_{k−1} are the
  [**residuals**](appendix/glossary.md#residual). They are ordinary Core
  values of the types `Smooth<P, Xᵢ>`.
- The [**backward Core**](appendix/glossary.md#backward-core) of a site is a
  generated function. It pulls the seed back along m_k, …, m₁.
- The [**Jacobian table**](appendix/glossary.md#jacobian-table) of a declared
  map is the matrix of its partial derivatives, which the kernel computes when
  it generates the program. A step along a declared map applies the transpose
  of its table at the saved point.
- An [**opaque step**](appendix/glossary.md#opaque-step) is a map whose
  structure the compilation does not open. The backward Core pulls the seed
  back along it with the runtime reverse pass in saved mode.

## Scope and decisions

The conditions are the Target items T1–T5 and the acceptance boxes A1–A6 of
#623. The decisions behind the profile are:

- **Derivative rules are precomputed Jacobian tables.** The derivative rule
  of a declared map is `morphism map`. A step along the map evaluates the
  Jacobian table of `map`, a literal of rational polynomials in the generated
  code. Nothing is differentiated symbolically at run time.
- **Opaque maps and tapes take one runtime step.** A function parameter, the
  value of a branch or of a call, `composite(…)` and a map beyond the
  `reverseLeaves` budget are opaque steps. The backward Core pulls the seed
  back along each with the runtime reverse pass. A tape that crosses a
  function boundary keeps `linearize` and `backward`. The
  [per-code table](#acceptance-example-by-code) lists the opaque steps of the
  acceptance example.
- **Residuals are a `let` chain, and the backward Core is a function.** The
  forward Core is a chain of `let`s at the site. The backward Core is a
  generated function of the opaque maps, the points and the seed. A saved
  site passes every point. A recomputing site passes r₀, and its function
  evaluates the images again. The compilation adds no Core type.
- **The theorems cover the generated functions and, locally, the rewrite of
  a site.** The oracle proves what the forward and backward Core of every
  site shape compute. The bridge proves the Fréchet comparison without the
  kernel chain rule. The rewrite of one site is a local theorem with explicit
  premises. Whole modules agree in tests, not in a theorem.

Further facts of the profile:

- **No rejection.** The compilation rejects no accepted program. A site that
  it cannot compile stays a call of the runtime reverse pass; see
  [gaps](#gaps).
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

| Step | Content | Pull request |
| --- | --- | --- |
| 1 | The field `reverse` of every registry entry; the step bindings `smoothApply` and `cotangentJacobian`; `SmoothRuntime.jacobian` and `jacobianStep`; the oracle's `ReverseSound` | [#661](https://github.com/MGYamada/Vastitas/pull/661) |
| 2 | Reading the maps of a site, the templates, the reserved declarations, the ledger, structural equality, validation, `Reverse.compile` and its wiring, generation from `compiled`, `reverseLeaves`; the kernel regression, the Rust tests, the goldens and the corpus | TODO(pr) |
| 3 | The oracle theorems | TODO(pr) |
| 4 | The bridge theorems | TODO(pr) |
| 5 | This map, the reference, guide and verification chapters, the ADR 0001 amendment and the glossary | TODO(pr) |

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
| **R — rules and steps** | `IndexedPrimitiveDescriptors.lean` (`ReverseRule`, `PassKind`, the field `reverse`), `IndexedPrimitiveRegistry.lean` (the rule of every entry; `smoothApply` and `cotangentJacobian` with their lowerings), `IndexedSmoothContracts.lean` (their contracts), `SmoothRuntime.lean` (`Map.ratPoint`, `applyPoint`, `jacobian`, `jacobianStep`) | `SmoothRuntimeRegression` (the Jacobian table of g; a table step equals `cot` and the saved pullback; a seed over another point fails); `IndexedDescriptorRegression` | Oracle `SmoothJacobian` (`jacobianStep_eq_of_output`, `jacobianStep_eq`, `pullback_congr_point`, `pullback_stepwise_applyPoint`, `smoothApply_sound`, `cotangentJacobian_sound`, `registry_reverse_sound`); `IndexedDescriptorDemo.directionalDerivative_reverseSound` |
| **G — generation** | `IndexedReverse.lean` (`resolve`, `compileSite`, `forwardLets`, `backwardBody`, `Entry.generated`, `Entry.declarations`, `rewriteFunction`, `generate`); `Limits.lean` and `compiler-limits.json` (`reverseLeaves`) | `ReverseCoreRegression`; `tests/reverse_core.rs` | Oracle `SmoothReverseCore` (what the templates compute) and `IndexedReverseCore` (the structure of `generate`) |
| **V — check again** | `IndexedReverse.lean` (`termEq` to `moduleEq`, `validate`, `Compiled`, `compile`); `IndexedAuthorityCheck.lean` and `ResourcePure.lean` (the field `compiled`); `Main.lean` and `ResourceCodegen.lean` (generation from `compiled`) | The forged modules of `ReverseCoreRegression`; `the_wire_cannot_name_the_compiled_declarations` | Oracle `IndexedReverseCore` (`moduleEq_sound`, `validate_iff`, the `compiled_*` and `public_*` theorems) |
| **E — emitted code** | The lowerings of the step bindings | `generated_lean_matches_the_emit_fixtures` (`tests/emit_golden.rs`); the native fixtures `smooth_reverse_programs` and `smooth_reverse_extended` of `scripts/check_indexed_native.sh` | Tested only |
| **B — bridge** | `ReverseCore.lean` TODO(name) | — | Bridge TODO(name) |

Every theorem of `SmoothReverseCore` is stated on the kernel's own
definitions (`forwardLets`, `backwardBody`, `Entry.generated`) and on the
kernel evaluator, through `IndexedEvaluation.Evaluates`. Its premises about
the module are explicit: the step declarations (`StepsDeclared`,
`StepFormed`, `MorphismsDeclared`), the declaration of the forward step and
the lookup of the generated function. Only `saved_function_cot` and
`pullback_chain_cot` use the oracle chain rule
(`SmoothCalculus.backward_eq_cot`); the other theorems use the stepwise
pullback and the table steps.

<a id="acceptance-conditions"></a>

## Acceptance conditions

The acceptance example is the Stage 3 example
[`examples/packages/smooth-differential/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/smooth-differential),
unchanged. Each observation has its own failure code from 1 to 25. "Code k"
below is that observation.

| Condition | Status and evidence |
| --- | --- |
| <a id="t1"></a>T1. Transform: from the checked Core of a smooth program, the kernel produces forward Core (the primal value and the residuals as ordinary Core values) and backward Core (the pullback from the residuals and a seed); the transform works on checked IR only, and Rust derives nothing | **Implemented**: `Reverse.generate`, run by `Reverse.compile` on `executable.core` (G). No file under `src/` changes. **Tested**: `acceptance_sites_compile_to_generated_backward_functions` (the 22 reverse sites of the acceptance example give 22 generated functions, placed first and numbered after the source functions; each is called once; every Jacobian step lies in a generated function, with its table as a literal without variables; the 4 runtime reverse passes and their callers; the 4 unit seeds of the differentials; no call of `SmoothRuntime.differential`, `backward`, `linearize` or the recomputed mode); `ReverseCoreRegression` ("the fixture has one entry per reverse site", "every site of the fixture is compiled" for 45 sites, "the parameter h is one opaque step", "the let-bound map is read through: two declared steps", "both backward calls on the let-bound tape are compiled"). **Proved (oracle)**: `SmoothReverseCore.forwardLets_evaluates` and `residualRel_images` (the forward Core binds the images of the input point, which satisfy the residual relation); `IndexedReverseCore.generate_shape`, `generate_keeps_function`, `generate_entry_mem`, `generate_entry_function`, `generate_entry_declaration` (the generated functions and declarations are in the module, and every source function keeps its header); `SmoothJacobian.registry_reverse_sound` (every registry entry keeps the promise of its derivative rule). |
| <a id="t2"></a>T2. Check again: the generated Core passes the same checker, typing and audits as source-derived Core; forged reverse Core is rejected | **Implemented**: `Reverse.compile` runs `Core.Typing.checkModule`, the Core audit of source-derived executable Core, on the generated module, and `validate` compiles the source module again and compares (V). A failure is `E_INTERNAL_REVERSE`. The compiled declarations and functions have reserved names (`__vastitas_rd…`, `__vastitas_rf…`). **Tested**: the forged modules of [A4](#a4); `the_wire_cannot_name_the_compiled_declarations`. **Proved (oracle)**: `IndexedReverseCore.moduleEq_sound` (with `termEq_sound`, `termsEq_sound`, `functionEq_sound`, `functionsEq_sound`), `validate_iff`, `validate_sound`, `validate_no_entries`; `compiled_generate`, `compiled_entry_resolves`, `compiled_functions_total`, `compiled_main_total` (the compiled module is the recompilation of the executable Core, every entry resolves, and every function is total and typed). |
| <a id="t3"></a>T3. Saved and recomputed residuals: both policies are expressible, and they agree | **Implemented**: `backwardBody`. A saved function takes every point; a recomputing function takes r₀ and evaluates the images in its body. **Tested**: codes 12 and 25; `each_pullback_binding_compiles_to_its_own_residual_policy` (`tests/smooth_differential.rs`); `acceptance_sites_compile_to_generated_backward_functions` (the two recomputing functions evaluate 5 images); `a_branch_chooses_the_map_of_a_reverse_pass` (`recomputed`, codes 4 and 8 of the corpus package); `ReverseCoreRegression` ("the recomputing pullback keeps its mode; every other site saves", "the recomputing pullback reads through the let: three declared steps"). **Proved (oracle)**: `SmoothReverseCore.recomputed_function_evaluates`, `recomputed_function_pullback`, `saved_eq_recomputed`. |
| <a id="t4"></a>T4. Theorem: the forward Core evaluates to the primal value with residuals that satisfy the residual relation; the backward Core, for every seed over the output, evaluates to η ∘ D⟦P⟧(x); for the generated Core itself, reusing the chain rule and the meaning theorems of Stage 3 | **Proved (oracle)**: forward, `SmoothReverseCore.forwardLets_evaluates`; backward, `saved_function_evaluates` (at any points, the generated function computes `backwardPass`), `backwardPass_eq_pullback` and `saved_function_pullback` (under the residual relation, the saved-mode pullback along the composite, without the chain rule), `saved_function_foreign_seed`; meaning, `saved_function_cot` and `pullback_chain_cot` (`some ⟨x, cot P x η⟩`, through the Stage 3 chain rule `SmoothCalculus.backward_eq_cot`); trees, `Factors.pullback_chain`. The lift to every site of an accepted module: TODO(name). The public-path corollary for every request that `ResourceSource.Wire` accepts: TODO(name). **Proved (bridge)**: TODO(name), the generated backward Core equals `(covector η).comp (fderiv ℝ (realProgram P) x)`, from the oracle's forward and backward theorems and the Stage 3 theorem `Frechet.pullback_covector_eq_comp_fderiv`, without `ChainRule.lean`. |
| <a id="t5"></a>T5. Refinement: the generated code agrees with the runtime reverse pass on the acceptance example, which may stay as a reference | **Tested**: the acceptance example prints `42` through compiled Core, and the 25-code expectations of `mutated_observations_change_the_native_result` are unchanged (A1); `ReverseCoreRegression` ("each compiled site evaluates to the value of the source site, failures included", for the 45 sites of `CotangentRegression.cotangentFixture`, a Core analogue of the acceptance example; "the compiled module evaluates to 42"; the same on the extended module); the corpus packages with their mutations (A6). **Proved (oracle)**, for one site: `SmoothReverseCore.site_saved_rewrite`, `site_recomputed_rewrite`, `site_differential_rewrite` (the compiled Core of a site and its source call evaluate to the same covector, under explicit freshness premises). **Not claimed**: refinement of a whole module. |
| <a id="a1"></a>A1. The Stage 3 acceptance example runs its reverse passes through generated Core and prints `42`; a mutation test flips its codes | **Tested**: `smooth_example_checks_builds_and_executes`; `mutated_observations_change_the_native_result` (every code 1–25 flipped by some group of mutations); `acceptance_sites_compile_to_generated_backward_functions`. The [per-code table](#acceptance-example-by-code) shows which steps each code reads. |
| <a id="a2"></a>A2. Oracle theorem: generated forward and backward Core are correct, relative to the oracle chain rule | **Proved (oracle)**: the theorems of T1, T3 and T4. `saved_function_cot` is the statement relative to the chain rule; the other backward theorems do not use it. |
| <a id="a3"></a>A3. Bridge theorem: the generated backward Core equals the adjoint of `fderiv` of the accepted program | **Proved (bridge)**: TODO(name) (the Fréchet comparison of T4); TODO(name) (the Kähler corollary); TODO(name) (accepted Core and the public path). `lean-bridge/Audit.lean` requires each name: TODO(name). |
| <a id="a4"></a>A4. Rejected: forged reverse Core, a residual from another point, mismatched endpoints, a seed over another point (the failure value), and a tampered tape | See [rejections](#rejections). |
| <a id="a5"></a>A5. Byte-level codegen tests for the generated reverse functions | **Tested**: `generated_lean_matches_the_emit_fixtures` pins `tests/fixtures/emit/smooth-differential.lean`, `reverse-branch.lean`, `reverse-tape.lean` and `reverse-domain.lean`, and the regenerated `smooth-cotangent.lean`, `smooth-metric.lean` and `stdlib-differential.lean`; non-smooth goldens are unchanged. `ReverseCoreRegression` ("the generated function of one declared step, byte for byte", the pullback along `gf` with the table `[[4t]]`; "the lowering calls the compiled steps and no runtime reverse pass at a compiled site"; "one generated function per site, before the source functions"). The native fixtures `smooth_reverse_programs` and `smooth_reverse_extended` compile and print `42`. **Not claimed**: native refinement of the generated code. |
| <a id="a6"></a>A6. No general differentiation of branches, loops or recursion; a branch may still choose which smooth map is built | **Implemented**: `ReverseRule` has the cases `none`, `morphism`, `chain`, `tape` and `pass`, and none differentiates a condition. A map that a branch chooses is an opaque step. The language has no loops, and the checker rejects recursion ([Core language](stage0.md#surface-language)). **Tested**: `a_branch_chooses_the_map_of_a_reverse_pass` (`tests/emit_corpus/reverse-branch/`: four sites, each with one opaque step for the branch and, in `squared`, a Jacobian step along `sq`; both arms observed; mutations print `212` and `127`); `ReverseCoreRegression` ("the map chosen by a branch is one opaque step"). |

<a id="rejections"></a>

### Rejections

| Rejection | Outcome | Evidence |
| --- | --- | --- |
| Forged reverse Core | Static. `validate` rejects every module and ledger other than the recompilation of the source module; the Core audit also rejects the ill-typed ones. No source or wire request can name a compiled declaration or supply Core. | **Tested**: `ReverseCoreRegression`: a backward function that returns its seed; the two steps of the shears in the opposite order (well typed, `main` changes); a step with its input and output points exchanged; a step along another declared map; a generated function under another owner; a missing generated function (Core audit); an extra function; a site left uncompiled; a function returning a covector over another object (Core audit); a ledger with another mode or a missing entry. `the_wire_cannot_name_the_compiled_declarations`: a declaration, morphism or function under a compiler name (`E_RESERVED`), a call of one (`E_NAME`), and the operations `smooth_apply` and `cotangent_jacobian` (`E_PROTOCOL`), for `check` and `emit`. **Proved (oracle)**: `IndexedReverseCore.validate_sound`, `compiled_codegen_input`, `legacy_compiled_codegen_input`, `generated_pure_entry_compiled`, `public_pure_entry_compiled`, `public_resource_compiled` (on every public path, the emitted module is the recompilation of the executable Core). |
| A residual from another point | Static for a forged residual: the forward Core binds every residual, and validation rejects any other. A source program that pulls back through the wrong intermediate point passes a seed over another point to the next site, which gives the failure value ⊥. | **Tested**: `ReverseCoreRegression` ("a residual from another point: a site passing the input point as the image is rejected", well typed); codes 9 and 10. **Proved (oracle)**: `SmoothReverseCore.forwardLets_evaluates` (the residuals are the images); `saved_function_foreign_seed`. |
| Mismatched endpoints | Static. The source call is `E_ENDPOINT`, as in Stage 3. In generated Core, a step over the wrong object fails the Core audit, and the compilation forms points and covectors only over objects that its families cover. | **Tested**: `smooth_endpoint_errors_name_the_failing_role`, `acceptance_rejects_wrong_objects_and_a_gradient_primitive_statically` (`tests/smooth_differential.rs`); `ReverseCoreRegression` ("a generated function returning a covector over another object fails the Core audit"); `a_reverse_pass_through_an_object_outside_the_cotangent_domain_keeps_the_runtime_pass`. Static rejection is tested, not proved. |
| A seed over another point | The failure value ⊥, at run time. | **Tested**: codes 8, 11 and 14; the corpus packages (`reverse-branch` codes 256 and 512, `reverse-tape` codes 32 and 64, compiled and runtime). **Proved (oracle)**: `SmoothReverseCore.saved_function_foreign_seed`, `backwardPass_foreign_seed`; `SmoothJacobian.jacobianStep_eq_of_output`. **Proved (bridge)**: TODO(name). |
| A tampered tape | Static. A tape has no source or wire form, as in Stage 3. The compiled reverse pass of a tape bound by `let` reads the map and the point of its `linearize` and forms its own residuals, which validation fixes. A tape from another point rejects the seed with ⊥. | **Tested**: `raw_wire_rejects_forged_fiber_and_tape_records` (`tests/smooth_differential.rs`); the residual forgery above; code 14; `a_tape_bound_by_let_compiles_and_a_tape_passed_to_a_function_keeps_its_routine`. |

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
| 18 | `dg` = (2, 1) at (1, 2) | `main`: `differential(g(), p)` | Jacobian, 1; the unit seed at g(1, 2) |
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
| [#361](https://github.com/MGYamada/Vastitas/issues/361) compiled pullbacks | Reverse Core that the kernel emits, checks again and validates by recompilation, for exact QQ polynomial maps; saved and recomputed residuals; the noncommuting shears and nonlinear composition through Jacobian steps (codes 1, 2, 4, 16 and 17) | Opaque steps compiled through specialization; preservation through passes (#164) |
| [#290](https://github.com/MGYamada/Vastitas/issues/290) proof-carrying differentiation | The theorem over generated forward and backward Core, restricted to the finite smooth profile (T4); a residual from another point is rejected (A4) | The derivation language, selected-backward and within contracts, and a whole-module refinement theorem |
| [#629](https://github.com/MGYamada/Vastitas/issues/629) | — | Sharing of repeated literals, such as the Jacobian table of a map that several steps read |

<a id="gaps"></a>

## Gaps

- **Whole-module refinement is not proved.** The oracle proves the generated
  functions and the rewrite of one site under explicit premises. That a
  compiled module evaluates as its source does is tested: on the acceptance
  example, on the 45 sites of the cotangent fixture and on the corpus.
- **Opaque maps and escaping tapes use the runtime reverse pass.** Opaque
  steps are function parameters, values of branches and calls,
  `composite(…)`, and maps beyond `reverseLeaves`. A tape passed to or
  returned from a function keeps `backward`. A whole site stays a call of the
  runtime reverse pass when its maps cannot be read, or when a family of the
  generated Core does not cover one of its objects (`reverse-domain`). It
  also stays when its declarations would exceed the 4096 declaration ids of a
  module. A function whose compiled Core would exceed `generatedLets` keeps
  all its sites; no test reaches that budget. Compiling a function for each
  static map argument is a follow-up
  ([#664](https://github.com/MGYamada/Vastitas/issues/664)).
- **An opaque step evaluates its map forward twice:** once in the forward
  Core for its image, and again inside the runtime reverse pass.
- **A let-bound tape's forward Core runs again at each reverse pass.** Each
  reverse pass of the tape is a site that copies the tape's map and point.
  The tape's own `let` stays in the function.
- **Jacobian tables are repeated per step.** Each Jacobian step carries its
  table as a literal, so two steps along one declared map repeat it. Sharing
  literals is the subject of #629.
- **Validation is by recompilation.** `validate` compiles the source module
  again and compares the result structurally; no independent checker
  re-derives the templates. `moduleEq_sound` makes the comparison sound, so
  validation is as strong as the generator, whose output the oracle theorems
  describe.
- **The compilation runs once, on source Core.** An opaque step calls a saved
  `cotangent_pullback` declaration, whose rule is a reverse pass, so
  compiling generated Core again would compile that step again.
- **No floats and no performance claims.** Arithmetic is exact over QQ, and
  nothing is measured (#222).
- **Residual retention is not reached.** Residuals are immutable pure Core
  values: a saved site retains them, and a recomputing site recomputes them.
  The storage-backed retention of
  [storage ownership §7.10](storage-ownership.md#710-reverse-residual-retention-and-mutation),
  with value versions and invalidation, does not arise.

<a id="proof-boundary"></a>

## Proof boundary

- **Proved (oracle).**
  - Every registry entry keeps the promise of its derivative rule, and a
    Jacobian step is the pullback along its declared map at the saved point.
  - The forward Core binds the images. Under the residual relation, the saved
    and recomputing backward functions compute the saved- and
    recomputed-mode pullbacks along the composite of the steps. A seed over
    another point gives ⊥.
  - Relative to the oracle chain rule, the backward Core is the cotangent
    pullback `cot` of the composite map.
  - The rewrite of one site evaluates as the source call, under explicit
    premises.
  - Structural equality is sound, validation characterizes the recompilation,
    and on every public path the emitted module is that recompilation, with
    total and typed functions.
- **Proved (bridge).** TODO(name): the Fréchet comparison of the generated
  backward Core, its Kähler corollary and the public-path corollary.
- **Tested only.**
  - Agreement of whole compiled modules with their source.
  - Rejection of forged modules and of wire requests that name compiled
    declarations.
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
  [#664](https://github.com/MGYamada/Vastitas/issues/664),
  [#666](https://github.com/MGYamada/Vastitas/issues/666).
- A refinement theorem for every function of a compiled module
  ([#665](https://github.com/MGYamada/Vastitas/issues/665)), and the premises
  that the compiled-entry theorems keep
  ([#668](https://github.com/MGYamada/Vastitas/issues/668)).

## Validation

TODO(validation): the commands of the integrated batch and their results.
