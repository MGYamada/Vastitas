import VastitasBridge.Differential.Frechet
import VastitasBridge.Differential.Kaehler
import VastitasOracle.SmoothReverseCompiled

/-!
# Compiled reverse Core means the derivative

The compiler replaces each reverse site that it compiles by forward Core and a generated
backward function, and lists the site in the ledger of the compiled module (`Reverse.Compiled`).
A site outside the ledger keeps the runtime reverse pass. The Oracle states what a call of the
generated function evaluates to: the runtime pullback of the seed along the chain of the step
programs, in the site's mode (`SmoothReverseCompiled.compiled_saved_entry`,
`compiled_recomputed_entry`). This file reads that pullback over `ℝ` and in Kähler differentials,
for every entry of every compiled module:

* **`compiled_saved_entry_frechet`**, **`compiled_recomputed_entry_frechet`**: when the chain
  `F` of the step programs is well typed as `ℝⁿ → ℝᵐ`, the input point has `n` coordinates and
  the seed `η` lies over `F(x)` with `m` components, the call evaluates to a covector over `x`
  with `n` components, which as a linear functional is `η ∘ DF(x)`, with Mathlib's Fréchet
  derivative of the real program. `compiled_saved_entry_fderiv_adjoint` and
  `compiled_recomputed_entry_fderiv_adjoint` state it componentwise: component `j` is
  `Σᵢ ηᵢ (DF(x) eⱼ)ᵢ`, the transpose of the Jacobian applied to `η`.
* **`compiled_saved_entry_cot_kaehler`**, **`compiled_recomputed_entry_cot_kaehler`**: under
  the same premises, without the coordinate count of `x`, the call evaluates to the covector
  over `x` whose components are `cot` of the composite map that `F` denotes, applied to `η`.
  `backward_eq_cot_kaehler` reaches the composite map through Kähler functoriality
  (`cot_compose_kaehler`).
* **`compiled_saved_entry_kaehler`**, **`compiled_recomputed_entry_kaehler`**: component `j` of
  the same covector is the value at `x` of the `j`-th coordinate of the Kähler pullback of
  `Σᵢ ηᵢ dyᵢ` along the polynomial map `F` denotes.
* `EntryFrechet` collects the Fréchet statement of one entry in both modes;
  `compiled_entries_frechet`, `public_wire_entries_frechet` (protocol 7),
  `legacy_wire_entries_frechet` (protocols 2-6), `public_resource_entries_frechet` and
  `public_pure_entry_frechet` (protocols 8/9) state it for every ledger entry of every module
  that a public path accepts or emits.

The Fréchet theorems compose the Oracle's `compiled_saved_entry` and
`compiled_recomputed_entry`, which use the stepwise pullback, with
`Frechet.pullback_covector_eq_comp_fderiv`, whose composite case is Mathlib's chain rule
`HasFDerivAt.comp`. The Kähler theorems compose the same Oracle theorems with
`backward_eq_cot_kaehler`. No theorem here uses the kernel chain rule. The proofs use none of
`cot_compose`, `backward_eq_cot`, `pullback_composite` and `pullback_comp` of `ChainRule.lean`,
none of `SmoothCalculus.cot_compose`, `backward_eq_cot`, `backward_eq_cot_saved`,
`pullback_composite`, `pullback_eq_composite` and `Cov.pullback_comp` of the Oracle, and not the
formal chain rule `pderiv_aeval`. The import closure of this file contains the Oracle's
`SmoothCalculus` but not `ChainRule.lean`, so the claim concerns the constants that the proofs
use. `lean-bridge/Audit.lean` walks those constants and checks it.

The premises that stay concern the arguments of the call: one smooth map per opaque step
(`count`), arguments that evaluate to those maps, the points and the seed (`argumentsEval`),
and for a saved site the residual relation of the saved points. To these the theorems add the
typing of the chain from `n` to `m` coordinates and a seed over the image with `m` components.
The Fréchet theorems also need an input point with `n` coordinates. The theorems concern checked
Core, not the generated text or native code.

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

noncomputable section

namespace VastitasBridge.Differential

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime
open VastitasKernel.Indexed (Variance)
open VastitasKernel.Indexed.Core.Semantics (Values)
open VastitasOracle.SmoothRuntime
open VastitasOracle.IndexedEvaluation (Evaluates ArgumentsEvaluate)
open VastitasOracle.SmoothReverseCore (chain stepPrograms ResidualRel functionArguments
  composable_of_wellTyped)
open VastitasBridge.AlgebraicGeometry.Kernel
open MvPolynomial

variable {n m : ℕ}

/-! ## Programs through Kähler functoriality -/

/-- **The reverse pass is `cot` of the denoted map, through Kähler differentials.** The
recomputing reverse pass of a well-typed program equals the cotangent pullback along the
composite polynomial map it denotes. The composite case is `cot_compose_kaehler`, Kähler
functoriality; the proof does not use `cot_compose` or `pderiv_aeval`. -/
theorem backward_eq_cot_kaehler {F : Program} (hF : F.wellTyped n m = true) (x η : List ℚ) :
    F.reverse x η = cot F.denote x η := by
  induction F generalizing n m x η with
  | primitive map => rfl
  | compose after before ihAfter ihBefore =>
    simp only [Program.wellTyped, Bool.and_eq_true] at hF
    rw [Program.reverse, ihAfter hF.2, ihBefore hF.1,
      ← VastitasOracle.SmoothCalculus.eval_denote hF.1, Program.denote,
      cot_compose_kaehler (wellFormed_iff.1 (VastitasOracle.SmoothCanonical.denote_wellFormed hF.2))
        (wellFormed_iff.1 (VastitasOracle.SmoothCanonical.denote_wellFormed hF.1))]

/-! ## A term that evaluates to a pullback -/

/-- Component `j` of a covector that is `η ∘ L` is `Σᵢ ηᵢ (L eⱼ)ᵢ`. -/
lemma getD_eq_of_covector_eq {k l : ℕ} {c η : List ℚ} {L : (Fin k → ℝ) →L[ℝ] (Fin l → ℝ)}
    (h : covector k c = (covector l η).comp L) (j : Fin k) :
    ((c.getD j 0 : ℚ) : ℝ) = ∑ i : Fin l, ((η.getD i 0 : ℚ) : ℝ) * L (Pi.single j 1) i := by
  rw [← covector_single k c j, h, ContinuousLinearMap.comp_apply, covector_apply]

/-- A term that evaluates to the pullback of a seed over `F(x)`, in either mode, along a program
`F` checked as `ℝⁿ → ℝᵐ`, evaluates to a covector over `x` with `n` components which, as a
linear functional, is the seed composed with Mathlib's Fréchet derivative of `F` at `x`. -/
theorem evaluates_pullback_frechet {module : Indexed.Core.Module} {values : Values}
    {term : Indexed.Core.Term}
    (mode : PullbackMode) {F : Program} (typed : F.wellTyped n m = true) {start : Program}
    (startLength : (coordinates start).length = n) {seed : Fiber}
    (over : seed.point = F.eval (coordinates start)) (components : seed.components.length = m)
    (evaluated : Evaluates module values term
      (.indexed (.fiber .cotangent (pullback mode F start (some seed))))) :
    ∃ r : Fiber, Evaluates module values term (.indexed (.fiber .cotangent (some r))) ∧
      r.point = coordinates start ∧ r.components.length = n ∧
      covector n r.components = (covector F.outputArity seed.components).comp
        (fderiv ℝ (realProgram F n) (realPoint n (coordinates start))) := by
  obtain ⟨r, hr, hpoint, hlength, hcovector⟩ :=
    pullback_covector_eq_comp_fderiv mode typed start startLength seed over components
  rw [hr] at evaluated
  exact ⟨r, evaluated, hpoint, hlength, hcovector⟩

/-- The same, componentwise: component `j` is `Σᵢ ηᵢ (DF(x) eⱼ)ᵢ`. -/
theorem evaluates_pullback_fderiv_adjoint {module : Indexed.Core.Module} {values : Values}
    {term : Indexed.Core.Term} (mode : PullbackMode) {F : Program} (typed : F.wellTyped n m = true)
    {start : Program} (startLength : (coordinates start).length = n) {seed : Fiber}
    (over : seed.point = F.eval (coordinates start)) (components : seed.components.length = m)
    (evaluated : Evaluates module values term
      (.indexed (.fiber .cotangent (pullback mode F start (some seed))))) :
    ∃ r : Fiber, Evaluates module values term (.indexed (.fiber .cotangent (some r))) ∧
      r.point = coordinates start ∧ r.components.length = n ∧ ∀ j : Fin n,
        ((r.components.getD j 0 : ℚ) : ℝ) = ∑ i : Fin F.outputArity,
          ((seed.components.getD i 0 : ℚ) : ℝ) *
            fderiv ℝ (realProgram F n) (realPoint n (coordinates start)) (Pi.single j 1) i := by
  obtain ⟨r, hr, hpoint, hlength, hcovector⟩ :=
    evaluates_pullback_frechet mode typed startLength over components evaluated
  exact ⟨r, hr, hpoint, hlength, getD_eq_of_covector_eq hcovector⟩

/-- **The checked pullback is `cot` of the denoted map, through Kähler differentials.** For a
program `F` checked as `ℝⁿ → ℝᵐ` and a seed over `F(x)` with `m` components, the pullback in
either mode is the covector over `x` with components `cot F.denote x η`. This is the Oracle's
`SmoothReverseCore.pullback_chain_cot` for any program, proved through `backward_eq_cot_kaehler`
instead of `SmoothCalculus.backward_eq_cot`. -/
theorem pullback_eq_cot_kaehler (mode : PullbackMode) {F : Program}
    (typed : F.wellTyped n m = true) (start : Program) (seed : Fiber)
    (over : seed.point = F.eval (coordinates start)) (components : seed.components.length = m) :
    pullback mode F start (some seed) =
      some ⟨coordinates start, cot F.denote (coordinates start) seed.components⟩ := by
  rw [pullback_spec, ite_eq_left ⟨over, by rw [components, wellTyped_outputArity typed]⟩,
    backward_eq_cot_kaehler typed]

/-- A term that evaluates to the pullback of a seed over `F(x)`, in either mode, along a program
`F` checked as `ℝⁿ → ℝᵐ`, evaluates to a covector over `x` whose component `j` is the value at
`x` of the `j`-th coordinate of the Kähler pullback of `Σᵢ ηᵢ dyᵢ` along the map `F` denotes. -/
theorem evaluates_pullback_kaehler {module : Indexed.Core.Module} {values : Values}
    {term : Indexed.Core.Term}
    (mode : PullbackMode) {F : Program} (typed : F.wellTyped n m = true) {start : Program}
    {seed : Fiber} (over : seed.point = F.eval (coordinates start))
    (components : seed.components.length = m)
    (evaluated : Evaluates module values term
      (.indexed (.fiber .cotangent (pullback mode F start (some seed))))) :
    ∃ r : Fiber, Evaluates module values term (.indexed (.fiber .cotangent (some r))) ∧
      r.point = coordinates start ∧ ∀ j : Fin n,
        r.components.getD j 0 =
          MvPolynomial.eval (evalPoint n (coordinates start))
            ((KaehlerDifferential.mvPolynomialBasis ℚ (Fin n)).repr
              (pullbackForm (imageFamily n m F.denote.images) (constForm m seed.components)) j) := by
  rw [pullback_eq_cot_kaehler mode typed start seed over components] at evaluated
  exact ⟨_, evaluated, rfl, pullback_eq_pullbackForm_fiber
    (wellFormed_iff.1 (VastitasOracle.SmoothCanonical.denote_wellFormed typed)) _ _⟩

/-! ## The entries of a compiled module -/

section Compiled

variable {requireMain : Bool} {source : Indexed.Core.Typing.CheckedModule requireMain}

/-- **A saved entry computes `η ∘ DF(x)`.** In a compiled module, call the generated function of
a saved entry on arguments that evaluate to one smooth map per opaque step, an input point `x`
with `n` coordinates, one saved point per step in the residual relation and a seed `η`. When the
chain `F` of the step programs is well typed as `ℝⁿ → ℝᵐ` and `η` lies over `F(x)` with `m`
components, the call evaluates to a covector over `x` with `n` components, which as a linear
functional is `η` composed with Mathlib's Fréchet derivative of the real program `F` at `x`:
the adjoint of `DF(x)` applied to `η`.

The proof composes the Oracle's `compiled_saved_entry` with `pullback_covector_eq_comp_fderiv`.
Neither uses `cot_compose`, `backward_eq_cot` or `pderiv_aeval`. -/
theorem compiled_saved_entry_frechet (compiled : Indexed.Core.Reverse.Compiled source)
    {entry : Indexed.Core.Reverse.Entry} (member : entry ∈ compiled.entries)
    (saved : entry.site.mode = .saved) {values : Values} {arguments : List Indexed.Core.Term}
    {opaques : List Program} (count : opaques.length = entry.site.opaqueSteps.length)
    (typed : (chain (stepPrograms entry.site.steps opaques)).wellTyped n m = true)
    (start : Program) (startLength : (coordinates start).length = n) {outputs : List Program}
    (residual : ResidualRel (stepPrograms entry.site.steps opaques) start outputs)
    (variance : Variance) (seed : Fiber)
    (over : seed.point = (chain (stepPrograms entry.site.steps opaques)).eval (coordinates start))
    (components : seed.components.length = m)
    (argumentsEval : ArgumentsEvaluate compiled.core.module values arguments
      (functionArguments opaques (start :: outputs) variance (some seed)))
    (substitution : List (Indexed.ObjectRef × Indexed.ObjectRef)) (result : Indexed.Core.Result) :
    ∃ r : Fiber,
      Evaluates compiled.core.module values (.call entry.function arguments substitution result)
        (.indexed (.fiber .cotangent (some r))) ∧
      r.point = coordinates start ∧ r.components.length = n ∧
      covector n r.components =
        (covector (chain (stepPrograms entry.site.steps opaques)).outputArity seed.components).comp
          (fderiv ℝ (realProgram (chain (stepPrograms entry.site.steps opaques)) n)
            (realPoint n (coordinates start))) :=
  evaluates_pullback_frechet .saved typed startLength over components
    (VastitasOracle.SmoothReverseCompiled.compiled_saved_entry compiled member saved count
      (composable_of_wellTyped _ typed) start residual variance (some seed) argumentsEval
      substitution result)

/-- **A recomputing entry computes `η ∘ DF(x)`.** The same for the generated function of a
recomputing entry, called on one smooth map per opaque step, the input point and the seed. The
proof composes the Oracle's `compiled_recomputed_entry` with `pullback_covector_eq_comp_fderiv`,
without `cot_compose`, `backward_eq_cot` or `pderiv_aeval`. -/
theorem compiled_recomputed_entry_frechet (compiled : Indexed.Core.Reverse.Compiled source)
    {entry : Indexed.Core.Reverse.Entry} (member : entry ∈ compiled.entries)
    (recomputed : entry.site.mode = .recomputed) {values : Values}
    {arguments : List Indexed.Core.Term}
    {opaques : List Program} (count : opaques.length = entry.site.opaqueSteps.length)
    (typed : (chain (stepPrograms entry.site.steps opaques)).wellTyped n m = true)
    (start : Program) (startLength : (coordinates start).length = n) (variance : Variance)
    (seed : Fiber)
    (over : seed.point = (chain (stepPrograms entry.site.steps opaques)).eval (coordinates start))
    (components : seed.components.length = m)
    (argumentsEval : ArgumentsEvaluate compiled.core.module values arguments
      (functionArguments opaques [start] variance (some seed)))
    (substitution : List (Indexed.ObjectRef × Indexed.ObjectRef)) (result : Indexed.Core.Result) :
    ∃ r : Fiber,
      Evaluates compiled.core.module values (.call entry.function arguments substitution result)
        (.indexed (.fiber .cotangent (some r))) ∧
      r.point = coordinates start ∧ r.components.length = n ∧
      covector n r.components =
        (covector (chain (stepPrograms entry.site.steps opaques)).outputArity seed.components).comp
          (fderiv ℝ (realProgram (chain (stepPrograms entry.site.steps opaques)) n)
            (realPoint n (coordinates start))) :=
  evaluates_pullback_frechet .recomputed typed startLength over components
    (VastitasOracle.SmoothReverseCompiled.compiled_recomputed_entry compiled member recomputed count
      (composable_of_wellTyped _ typed) start variance (some seed) argumentsEval substitution result)

/-- The saved entry componentwise: component `j` of the result is `Σᵢ ηᵢ (DF(x) eⱼ)ᵢ`. -/
theorem compiled_saved_entry_fderiv_adjoint (compiled : Indexed.Core.Reverse.Compiled source)
    {entry : Indexed.Core.Reverse.Entry} (member : entry ∈ compiled.entries)
    (saved : entry.site.mode = .saved) {values : Values} {arguments : List Indexed.Core.Term}
    {opaques : List Program} (count : opaques.length = entry.site.opaqueSteps.length)
    (typed : (chain (stepPrograms entry.site.steps opaques)).wellTyped n m = true)
    (start : Program) (startLength : (coordinates start).length = n) {outputs : List Program}
    (residual : ResidualRel (stepPrograms entry.site.steps opaques) start outputs)
    (variance : Variance) (seed : Fiber)
    (over : seed.point = (chain (stepPrograms entry.site.steps opaques)).eval (coordinates start))
    (components : seed.components.length = m)
    (argumentsEval : ArgumentsEvaluate compiled.core.module values arguments
      (functionArguments opaques (start :: outputs) variance (some seed)))
    (substitution : List (Indexed.ObjectRef × Indexed.ObjectRef)) (result : Indexed.Core.Result) :
    ∃ r : Fiber,
      Evaluates compiled.core.module values (.call entry.function arguments substitution result)
        (.indexed (.fiber .cotangent (some r))) ∧
      r.point = coordinates start ∧ r.components.length = n ∧ ∀ j : Fin n,
        ((r.components.getD j 0 : ℚ) : ℝ) =
          ∑ i : Fin (chain (stepPrograms entry.site.steps opaques)).outputArity,
            ((seed.components.getD i 0 : ℚ) : ℝ) *
              fderiv ℝ (realProgram (chain (stepPrograms entry.site.steps opaques)) n)
                (realPoint n (coordinates start)) (Pi.single j 1) i :=
  evaluates_pullback_fderiv_adjoint .saved typed startLength over components
    (VastitasOracle.SmoothReverseCompiled.compiled_saved_entry compiled member saved count
      (composable_of_wellTyped _ typed) start residual variance (some seed) argumentsEval
      substitution result)

/-- The recomputing entry componentwise. -/
theorem compiled_recomputed_entry_fderiv_adjoint (compiled : Indexed.Core.Reverse.Compiled source)
    {entry : Indexed.Core.Reverse.Entry} (member : entry ∈ compiled.entries)
    (recomputed : entry.site.mode = .recomputed) {values : Values}
    {arguments : List Indexed.Core.Term}
    {opaques : List Program} (count : opaques.length = entry.site.opaqueSteps.length)
    (typed : (chain (stepPrograms entry.site.steps opaques)).wellTyped n m = true)
    (start : Program) (startLength : (coordinates start).length = n) (variance : Variance)
    (seed : Fiber)
    (over : seed.point = (chain (stepPrograms entry.site.steps opaques)).eval (coordinates start))
    (components : seed.components.length = m)
    (argumentsEval : ArgumentsEvaluate compiled.core.module values arguments
      (functionArguments opaques [start] variance (some seed)))
    (substitution : List (Indexed.ObjectRef × Indexed.ObjectRef)) (result : Indexed.Core.Result) :
    ∃ r : Fiber,
      Evaluates compiled.core.module values (.call entry.function arguments substitution result)
        (.indexed (.fiber .cotangent (some r))) ∧
      r.point = coordinates start ∧ r.components.length = n ∧ ∀ j : Fin n,
        ((r.components.getD j 0 : ℚ) : ℝ) =
          ∑ i : Fin (chain (stepPrograms entry.site.steps opaques)).outputArity,
            ((seed.components.getD i 0 : ℚ) : ℝ) *
              fderiv ℝ (realProgram (chain (stepPrograms entry.site.steps opaques)) n)
                (realPoint n (coordinates start)) (Pi.single j 1) i :=
  evaluates_pullback_fderiv_adjoint .recomputed typed startLength over components
    (VastitasOracle.SmoothReverseCompiled.compiled_recomputed_entry compiled member recomputed count
      (composable_of_wellTyped _ typed) start variance (some seed) argumentsEval substitution result)

/-- **A saved entry computes `cot` of the composite map.** For the call of
`compiled_saved_entry_frechet`, with an input point of any number of coordinates, the call
evaluates to the covector over `x` whose components are `cot` of the composite map that the
chain `F` denotes, at `x`, applied to `η`. This is the Oracle's `compiled_saved_entry_cot`. Its
proof composes the Oracle's `compiled_saved_entry` with `pullback_eq_cot_kaehler`, and so uses
neither `cot_compose`, `backward_eq_cot` nor `pderiv_aeval`. -/
theorem compiled_saved_entry_cot_kaehler (compiled : Indexed.Core.Reverse.Compiled source)
    {entry : Indexed.Core.Reverse.Entry} (member : entry ∈ compiled.entries)
    (saved : entry.site.mode = .saved) {values : Values} {arguments : List Indexed.Core.Term}
    {opaques : List Program} (count : opaques.length = entry.site.opaqueSteps.length)
    (typed : (chain (stepPrograms entry.site.steps opaques)).wellTyped n m = true)
    (start : Program) {outputs : List Program}
    (residual : ResidualRel (stepPrograms entry.site.steps opaques) start outputs)
    (variance : Variance) (seed : Fiber)
    (over : seed.point = (chain (stepPrograms entry.site.steps opaques)).eval (coordinates start))
    (components : seed.components.length = m)
    (argumentsEval : ArgumentsEvaluate compiled.core.module values arguments
      (functionArguments opaques (start :: outputs) variance (some seed)))
    (substitution : List (Indexed.ObjectRef × Indexed.ObjectRef)) (result : Indexed.Core.Result) :
    Evaluates compiled.core.module values (.call entry.function arguments substitution result)
      (.indexed (.fiber .cotangent (some ⟨coordinates start,
        cot (chain (stepPrograms entry.site.steps opaques)).denote (coordinates start)
          seed.components⟩))) := by
  rw [← pullback_eq_cot_kaehler .saved typed start seed over components]
  exact VastitasOracle.SmoothReverseCompiled.compiled_saved_entry compiled member saved count
    (composable_of_wellTyped _ typed) start residual variance (some seed) argumentsEval
    substitution result

/-- **A recomputing entry computes `cot` of the composite map.** The same for the generated
function of a recomputing entry. This is the Oracle's `compiled_recomputed_entry_cot`, proved
from `compiled_recomputed_entry` and `pullback_eq_cot_kaehler`, without `cot_compose`,
`backward_eq_cot` or `pderiv_aeval`. -/
theorem compiled_recomputed_entry_cot_kaehler (compiled : Indexed.Core.Reverse.Compiled source)
    {entry : Indexed.Core.Reverse.Entry} (member : entry ∈ compiled.entries)
    (recomputed : entry.site.mode = .recomputed) {values : Values}
    {arguments : List Indexed.Core.Term}
    {opaques : List Program} (count : opaques.length = entry.site.opaqueSteps.length)
    (typed : (chain (stepPrograms entry.site.steps opaques)).wellTyped n m = true)
    (start : Program) (variance : Variance) (seed : Fiber)
    (over : seed.point = (chain (stepPrograms entry.site.steps opaques)).eval (coordinates start))
    (components : seed.components.length = m)
    (argumentsEval : ArgumentsEvaluate compiled.core.module values arguments
      (functionArguments opaques [start] variance (some seed)))
    (substitution : List (Indexed.ObjectRef × Indexed.ObjectRef)) (result : Indexed.Core.Result) :
    Evaluates compiled.core.module values (.call entry.function arguments substitution result)
      (.indexed (.fiber .cotangent (some ⟨coordinates start,
        cot (chain (stepPrograms entry.site.steps opaques)).denote (coordinates start)
          seed.components⟩))) := by
  rw [← pullback_eq_cot_kaehler .recomputed typed start seed over components]
  exact VastitasOracle.SmoothReverseCompiled.compiled_recomputed_entry compiled member recomputed
    count (composable_of_wellTyped _ typed) start variance (some seed) argumentsEval substitution
    result

/-- **A saved entry computes the fiber of the Kähler pullback.** For the call of
`compiled_saved_entry_frechet`, component `j` of the resulting covector is the value at `x` of
the `j`-th `mvPolynomialBasis` coordinate of the Kähler pullback of `Σᵢ ηᵢ dyᵢ` along the
polynomial map that the chain `F` denotes, in `Ω[ℚ[x₁, …, xₙ]⁄ℚ]`. The input point may have any
number of coordinates. The proof composes the Oracle's `compiled_saved_entry` with
`backward_eq_cot_kaehler` and `pullback_eq_pullbackForm_fiber`, without `cot_compose`,
`backward_eq_cot` or `pderiv_aeval`. -/
theorem compiled_saved_entry_kaehler (compiled : Indexed.Core.Reverse.Compiled source)
    {entry : Indexed.Core.Reverse.Entry} (member : entry ∈ compiled.entries)
    (saved : entry.site.mode = .saved) {values : Values} {arguments : List Indexed.Core.Term}
    {opaques : List Program} (count : opaques.length = entry.site.opaqueSteps.length)
    (typed : (chain (stepPrograms entry.site.steps opaques)).wellTyped n m = true)
    (start : Program) {outputs : List Program}
    (residual : ResidualRel (stepPrograms entry.site.steps opaques) start outputs)
    (variance : Variance) (seed : Fiber)
    (over : seed.point = (chain (stepPrograms entry.site.steps opaques)).eval (coordinates start))
    (components : seed.components.length = m)
    (argumentsEval : ArgumentsEvaluate compiled.core.module values arguments
      (functionArguments opaques (start :: outputs) variance (some seed)))
    (substitution : List (Indexed.ObjectRef × Indexed.ObjectRef)) (result : Indexed.Core.Result) :
    ∃ r : Fiber,
      Evaluates compiled.core.module values (.call entry.function arguments substitution result)
        (.indexed (.fiber .cotangent (some r))) ∧
      r.point = coordinates start ∧ ∀ j : Fin n,
        r.components.getD j 0 =
          MvPolynomial.eval (evalPoint n (coordinates start))
            ((KaehlerDifferential.mvPolynomialBasis ℚ (Fin n)).repr
              (pullbackForm
                (imageFamily n m (chain (stepPrograms entry.site.steps opaques)).denote.images)
                (constForm m seed.components)) j) :=
  evaluates_pullback_kaehler .saved typed over components
    (VastitasOracle.SmoothReverseCompiled.compiled_saved_entry compiled member saved count
      (composable_of_wellTyped _ typed) start residual variance (some seed) argumentsEval
      substitution result)

/-- **A recomputing entry computes the fiber of the Kähler pullback.** -/
theorem compiled_recomputed_entry_kaehler (compiled : Indexed.Core.Reverse.Compiled source)
    {entry : Indexed.Core.Reverse.Entry} (member : entry ∈ compiled.entries)
    (recomputed : entry.site.mode = .recomputed) {values : Values}
    {arguments : List Indexed.Core.Term}
    {opaques : List Program} (count : opaques.length = entry.site.opaqueSteps.length)
    (typed : (chain (stepPrograms entry.site.steps opaques)).wellTyped n m = true)
    (start : Program) (variance : Variance) (seed : Fiber)
    (over : seed.point = (chain (stepPrograms entry.site.steps opaques)).eval (coordinates start))
    (components : seed.components.length = m)
    (argumentsEval : ArgumentsEvaluate compiled.core.module values arguments
      (functionArguments opaques [start] variance (some seed)))
    (substitution : List (Indexed.ObjectRef × Indexed.ObjectRef)) (result : Indexed.Core.Result) :
    ∃ r : Fiber,
      Evaluates compiled.core.module values (.call entry.function arguments substitution result)
        (.indexed (.fiber .cotangent (some r))) ∧
      r.point = coordinates start ∧ ∀ j : Fin n,
        r.components.getD j 0 =
          MvPolynomial.eval (evalPoint n (coordinates start))
            ((KaehlerDifferential.mvPolynomialBasis ℚ (Fin n)).repr
              (pullbackForm
                (imageFamily n m (chain (stepPrograms entry.site.steps opaques)).denote.images)
                (constForm m seed.components)) j) :=
  evaluates_pullback_kaehler .recomputed typed over components
    (VastitasOracle.SmoothReverseCompiled.compiled_recomputed_entry compiled member recomputed count
      (composable_of_wellTyped _ typed) start variance (some seed) argumentsEval substitution result)

end Compiled

/-! ## Every entry of every public path -/

/-- The Fréchet statement of a ledger entry in `module`, in the site's mode: a call of the
entry's generated function, on arguments that evaluate to one smooth map per opaque step, an
input point `x` with `n` coordinates, for a saved site one saved point per step in the residual
relation, and a seed `η` over `F(x)` with `m` components, where the chain `F` of the step
programs is well typed as `ℝⁿ → ℝᵐ`, evaluates to a covector over `x` with `n` components which,
as a linear functional, is `η ∘ DF(x)`. -/
structure EntryFrechet (module : Indexed.Core.Module) (entry : Indexed.Core.Reverse.Entry) :
    Prop where
  saved : entry.site.mode = .saved →
    ∀ (values : Values) (arguments : List Indexed.Core.Term) (opaques : List Program) (n m : ℕ)
      (start : Program) (outputs : List Program) (variance : Variance) (seed : Fiber)
      (substitution : List (Indexed.ObjectRef × Indexed.ObjectRef)) (result : Indexed.Core.Result),
      opaques.length = entry.site.opaqueSteps.length →
      (chain (stepPrograms entry.site.steps opaques)).wellTyped n m = true →
      (coordinates start).length = n →
      ResidualRel (stepPrograms entry.site.steps opaques) start outputs →
      seed.point = (chain (stepPrograms entry.site.steps opaques)).eval (coordinates start) →
      seed.components.length = m →
      ArgumentsEvaluate module values arguments
        (functionArguments opaques (start :: outputs) variance (some seed)) →
      ∃ r : Fiber,
        Evaluates module values (.call entry.function arguments substitution result)
          (.indexed (.fiber .cotangent (some r))) ∧
        r.point = coordinates start ∧ r.components.length = n ∧
        covector n r.components =
          (covector (chain (stepPrograms entry.site.steps opaques)).outputArity seed.components).comp
            (fderiv ℝ (realProgram (chain (stepPrograms entry.site.steps opaques)) n)
              (realPoint n (coordinates start)))
  recomputed : entry.site.mode = .recomputed →
    ∀ (values : Values) (arguments : List Indexed.Core.Term) (opaques : List Program) (n m : ℕ)
      (start : Program) (variance : Variance) (seed : Fiber)
      (substitution : List (Indexed.ObjectRef × Indexed.ObjectRef)) (result : Indexed.Core.Result),
      opaques.length = entry.site.opaqueSteps.length →
      (chain (stepPrograms entry.site.steps opaques)).wellTyped n m = true →
      (coordinates start).length = n →
      seed.point = (chain (stepPrograms entry.site.steps opaques)).eval (coordinates start) →
      seed.components.length = m →
      ArgumentsEvaluate module values arguments
        (functionArguments opaques [start] variance (some seed)) →
      ∃ r : Fiber,
        Evaluates module values (.call entry.function arguments substitution result)
          (.indexed (.fiber .cotangent (some r))) ∧
        r.point = coordinates start ∧ r.components.length = n ∧
        covector n r.components =
          (covector (chain (stepPrograms entry.site.steps opaques)).outputArity seed.components).comp
            (fderiv ℝ (realProgram (chain (stepPrograms entry.site.steps opaques)) n)
              (realPoint n (coordinates start)))

/-- An entry that computes the pullback of its site (`EntryComputes`) satisfies the Fréchet
statement. -/
theorem entry_computes_frechet {module : Indexed.Core.Module}
    {entry : Indexed.Core.Reverse.Entry}
    (computes : VastitasOracle.SmoothReverseCompiled.EntryComputes module entry) :
    EntryFrechet module entry :=
  ⟨fun saved values arguments opaques _ _ start outputs variance seed substitution result count
      typed startLength residual over components argumentsEval =>
    evaluates_pullback_frechet .saved typed startLength over components
      (computes.saved saved values arguments opaques start outputs variance (some seed) substitution
        result count (composable_of_wellTyped _ typed) residual argumentsEval),
    fun recomputed values arguments opaques _ _ start variance seed substitution result count typed
      startLength over components argumentsEval =>
    evaluates_pullback_frechet .recomputed typed startLength over components
      (computes.recomputed recomputed values arguments opaques start variance (some seed)
        substitution result count (composable_of_wellTyped _ typed) argumentsEval)⟩

/-- **Every entry of a compiled module computes `η ∘ DF(x)`.** -/
theorem compiled_entries_frechet {requireMain : Bool}
    {source : Indexed.Core.Typing.CheckedModule requireMain}
    (compiled : Indexed.Core.Reverse.Compiled source) :
    ∀ entry ∈ compiled.entries, EntryFrechet compiled.core.module entry :=
  fun entry member => entry_computes_frechet
    (VastitasOracle.SmoothReverseCompiled.compiled_entries_compute compiled entry member)

/-- **Protocol 7.** For every JSON that `Indexed.Wire.check` accepts, every entry of the
compiled module of the accepted certificate, the module that `Main` emits, computes `η ∘ DF(x)`. -/
theorem public_wire_entries_frechet {json : Lean.Json} {requireMain : Bool}
    (accepted : VastitasKernel.Indexed.Wire.CheckedInput json requireMain) :
    ∀ entry ∈ accepted.checked.compiled.entries,
      EntryFrechet accepted.checked.compiled.core.module entry :=
  fun entry member => entry_computes_frechet
    (VastitasOracle.SmoothReverseCompiled.public_wire_entries accepted entry member)

/-- **Protocols 2-6.** The same for every JSON that the legacy checker accepts. -/
theorem legacy_wire_entries_frechet {json : Lean.Json} {requireMain : Bool}
    (accepted : VastitasKernel.Indexed.LegacySource.CheckedInput json requireMain) :
    ∀ entry ∈ accepted.checked.compiled.entries,
      EntryFrechet accepted.checked.compiled.core.module entry :=
  fun entry member => entry_computes_frechet
    (VastitasOracle.SmoothReverseCompiled.legacy_wire_entries accepted entry member)

/-- **Protocols 8/9.** For every JSON that `ResourceSource.Wire.check` accepts, every entry of
both compiled modules of the certificate (the pure program and the pure values of a resource
entry) computes `η ∘ DF(x)`. -/
theorem public_resource_entries_frechet {json : Lean.Json} {requireMain : Bool}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain) :
    (∀ entry ∈ input.checked.pureProgram.compiled.entries,
      EntryFrechet input.checked.pureProgram.compiled.core.module entry) ∧
    ∀ entry ∈ input.checked.values.compiled.entries,
      EntryFrechet input.checked.values.compiled.core.module entry :=
  ⟨fun entry member => entry_computes_frechet
      ((VastitasOracle.SmoothReverseCompiled.public_resource_entries input).1 entry member),
    fun entry member => entry_computes_frechet
      ((VastitasOracle.SmoothReverseCompiled.public_resource_entries input).2 entry member)⟩

/-- **Protocols 8/9 emit without a resource entry.** The module that the public emit path
generates code from is the compiled pure program of the checked certificate, and every entry of
its ledger computes `η ∘ DF(x)` there. -/
theorem public_pure_entry_frechet {json : Lean.Json}
    {program : VastitasKernel.ResourceSource.Program}
    {generated : VastitasKernel.ResourceSource.Codegen.Generated}
    (decoded : VastitasKernel.ResourceSource.Wire.program json = .ok program)
    (found : program.entry = none)
    (emitted : VastitasKernel.ResourceSource.Wire.emit json = .ok generated) :
    ∃ checked : VastitasKernel.ResourceSource.Checked program true,
      VastitasKernel.ResourceSource.check program true = .ok checked ∧
    ∃ core : Indexed.Core.Typing.CheckedModule true,
      core.module = checked.pureProgram.compiled.core.module ∧
      Indexed.Core.Codegen.generate core = .ok generated.source ∧
      ∀ entry ∈ checked.pureProgram.compiled.entries, EntryFrechet core.module entry := by
  obtain ⟨checked, accepted, core, same, emittedCore, computes⟩ :=
    VastitasOracle.SmoothReverseCompiled.public_pure_entry_computes decoded found emitted
  exact ⟨checked, accepted, core, same, emittedCore,
    fun entry member => entry_computes_frechet (computes entry member)⟩

end VastitasBridge.Differential
