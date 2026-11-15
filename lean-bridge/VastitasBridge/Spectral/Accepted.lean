import VastitasBridge.Spectral.Algebra
import VastitasBridge.Differential.Accepted
import VastitasBridge.Differential.ReverseCore
import VastitasOracle.SpectralAcceptance

/-!
# Accepted spectral bindings mean Daleckii–Krein and implicit differentiation

The bridge statements of Stage 5 (#806) about accepted Core, composed from the Oracle's
`SpectralCore` and `SpectralAcceptance`, the Stage 3 Fréchet theorems
(`Differential/Accepted.lean`, `Differential/ReverseCore.lean`), the spectral algebra in Mathlib
terms (`Spectral/Algebra.lean`) and the typed Daleckii–Krein theorems
(`Analysis/DaleckiiKreinTyped.lean`, `Spectral/Prerequisites.lean`).

* **Trace powers.** The real map of an accepted `trace_power(H, k)` is `y ↦ tr (H(y)ᵏ)` with
  the field `realField` of the declared endomorphism (`realProgram_tracePower`, from
  `SpectralCore.spectralInvariant_tracePower_at` at `ℝ`). For a symmetric endomorphism its
  derivative read with a covector `c` is `c₀` times the Daleckii–Krein cotangent
  `dkCotangent (· ^ k) (hermAt …) (trPairing 1)` composed with `hermDeriv …`
  (`covector_fderiv_tracePower`; `tracePower_fderiv_dk` for `c = [1]`).
* **Accepted Core.** An accepted `differential(f, p)` of an accepted symmetric trace power
  evaluates to that covector at `p` (`checked_trace_power_dk`, from
  `checked_differential_frechet`). A compiled reverse site of one declared step along a
  trace-power invariant computes the seed's component times the cotangent in both modes
  (`TracePowerSiteDK`, `EntryFrechet.trace_power_dk`); every compiled module
  (`compiled_trace_power_dk`) and the public protocol 8/9 paths
  (`public_resource_entries_trace_power_dk`, `public_pure_entry_trace_power_dk`) do so for all
  their entries (`TracePowerDK`), the step's map being the invariant's own
  (`SpectralCore.compiled_invariant_step`).
* **The roadmap gradient.** For the Stage 5 field `H = rows((x, y), (y, −x))` the cotangent is
  `(4y₀, 4y₁)` at every real point (`stage5_dk_gradient`).
* **Branches.** On the branch, an accepted `branch_differential(p, t, branch = B)` is `Dλ(p)`
  for every real `λ` that is differentiable at `p`, passes through `(p, t)` and keeps
  `χ(x, λ x) = 0` near `p` (`checked_branch_differential_implicit`, from
  `SpectralAcceptance.c10_branch_derivative`, `SpectralValid.slopeAt_ne_zero` and
  `implicit_branch_fderiv_eval`). The existence of such a `λ` is not claimed here.

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

noncomputable section

namespace VastitasBridge.Spectral

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasKernel.AlgebraRuntime (Poly Map)
open VastitasKernel.SmoothRuntime (Program Fiber coordinates)
open VastitasOracle.IndexedEvaluation (Evaluates ArgumentsEvaluate)
open VastitasOracle.SmoothReverseCore (chain stepPrograms ResidualRel functionArguments)
open VastitasOracle.SpectralCore (DeclaredEndo)
open VastitasOracle.SpectralDeclarations (polyEntry)
open VastitasBridge.Differential (realPoly realPoint realProgram realMap covector covector_apply
  hasFDerivAt_realProgram EntryFrechet)
open VastitasBridge.Analysis.DaleckiiKrein (dkCotangent trPairing)
open scoped Matrix Topology

/-! ## The real program of an accepted trace power -/

section Invariant

variable {env : Indexed.Environment} {application : Application} {map : Map} {endo : EndoRef} {k : ℕ}

/-- A declared symmetric endomorphism has a symmetric real field. -/
theorem endo_realField_symm (envValid : env.Valid) (declared : DeclaredEndo env endo)
    (hsym : endo.symmetric = true) (m : ℕ) :
    (realField m endo.rows.length endo.rows)ᵀ = realField m endo.rows.length endo.rows := by
  obtain ⟨-, -, -, -, hsymm⟩ := declared.checked envValid
  exact realField_transpose (hsymm hsym)

/-- **The real map of an accepted `trace_power(H, k)`** is `y ↦ tr (H(y)ᵏ)`, with the field of the
declared endomorphism over `ℝ`, at every real point. -/
theorem realProgram_tracePower (envValid : env.Valid)
    (valid : spectralInvariantValid env application map (.tracePower endo k) = true) :
    ∃ m, smoothDimension? env endo.object = some m ∧ map.arity = m ∧ map.images.length = 1 ∧
      ∀ (y : Fin m → ℝ) (i : Fin (Program.primitive map).outputArity),
        realProgram (.primitive map) m y i =
          (((realField m endo.rows.length endo.rows).map (MvPolynomial.eval y)) ^ k).trace := by
  obtain ⟨-, -, m, -, image, -, hm0, -, harity, -, himages, hcanonical, -, -⟩ :=
    VastitasOracle.SpectralCore.spectralInvariant_valid_sound valid
  have hm : smoothDimension? env endo.object = some m := hm0
  obtain ⟨declared, m', image', hm', -, himages', -, -, hat⟩ :=
    VastitasOracle.SpectralCore.spectralInvariant_tracePower_at (R := ℝ) envValid valid
  rw [hm] at hm'
  cases hm'
  rw [himages] at himages'
  cases himages'
  refine ⟨m, hm, harity, by simp [himages], fun y i => ?_⟩
  have hi : (i : ℕ) = 0 := by
    have := i.isLt
    simp only [Program.outputArity, himages, List.length_singleton] at this
    omega
  have hget : map.images.getD i [] = image := by simp [himages, hi]
  show MvPolynomial.eval y (realPoly m (map.images.getD i [])) = _
  rw [hget, realPoly_eval,
    ← evalIn_ofFn (VastitasOracle.SmoothCalculus.arity_of_canonical hcanonical) y,
    hat (algebraRatHom ℝ) (List.ofFn y), ringTrace_eq_trace (VastitasOracle.SpectralAlgebra.shape_ringPow _ _ k).1,
    listMatrix_ringPow (VastitasOracle.SpectralAlgebra.length_evalMatrix _ _ _),
    listMatrix_evalMatrix (declared.arity envValid hm) y, realField_map_eval]
  rfl

/-- **The DK cotangent of an accepted trace power.** For a symmetric declared endomorphism, the
covector `c` pulled back by the derivative of the invariant's real map is `c₀` times the
Daleckii–Krein cotangent of the trace pairing at `H(y)`, composed with `DH(y)`. -/
theorem covector_fderiv_tracePower (envValid : env.Valid)
    (valid : spectralInvariantValid env application map (.tracePower endo k) = true) {m : ℕ}
    (hm : smoothDimension? env endo.object = some m)
    (hM : (realField m endo.rows.length endo.rows)ᵀ = realField m endo.rows.length endo.rows)
    (c : List ℚ) (y : Fin m → ℝ) :
    (covector (Program.primitive map).outputArity c).comp
        (fderiv ℝ (realProgram (.primitive map) m) y) =
      ((c.getD 0 0 : ℚ) : ℝ) •
        (dkCotangent (· ^ k) (hermAt (realField m endo.rows.length endo.rows) hM y)
          (trPairing 1)).comp (hermDeriv (realField m endo.rows.length endo.rows) hM y) := by
  obtain ⟨m', hm', -, hlength, hprogram⟩ := realProgram_tracePower envValid valid
  rw [hm] at hm'
  cases hm'
  have hcomponent : ∀ i : Fin (Program.primitive map).outputArity,
      (ContinuousLinearMap.proj i).comp (fderiv ℝ (realProgram (.primitive map) m) y) =
        (dkCotangent (· ^ k) (hermAt (realField m endo.rows.length endo.rows) hM y)
          (trPairing 1)).comp (hermDeriv (realField m endo.rows.length endo.rows) hM y) := by
    intro i
    have hfun : (fun z => realProgram (.primitive map) m z i) =
        fun z => (((realField m endo.rows.length endo.rows).map (MvPolynomial.eval z)) ^ k).trace :=
      funext fun z => hprogram z i
    have h := (hasFDerivAt_pi'.mp
      (hasFDerivAt_realProgram (.primitive map) m y).differentiableAt.hasFDerivAt) i
    rw [hfun] at h
    rw [← h.fderiv, fderiv_trace_pow_field]
  ext v
  rw [ContinuousLinearMap.comp_apply, covector_apply]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hv : ∀ i : Fin (Program.primitive map).outputArity,
      fderiv ℝ (realProgram (.primitive map) m) y v i =
        (dkCotangent (· ^ k) (hermAt (realField m endo.rows.length endo.rows) hM y)
          (trPairing 1)).comp (hermDeriv (realField m endo.rows.length endo.rows) hM y) v := fun i => by
    rw [← hcomponent i]
    rfl
  simp only [hv]
  rw [← Finset.sum_mul]
  congr 1
  have hlen : (Program.primitive map).outputArity = 1 := hlength
  rw [Fintype.sum_equiv (finCongr hlen) (fun i => ((c.getD i 0 : ℚ) : ℝ))
    (fun i : Fin 1 => ((c.getD i 0 : ℚ) : ℝ)) (fun i => rfl), Fin.sum_univ_one]
  rfl

/-- **The derivative of an accepted trace power** read with the unit covector: the Daleckii–Krein
cotangent of `Re tr` at `H(y)`, composed with `DH(y)`. -/
theorem tracePower_fderiv_dk (envValid : env.Valid)
    (valid : spectralInvariantValid env application map (.tracePower endo k) = true) {m : ℕ}
    (hm : smoothDimension? env endo.object = some m)
    (hM : (realField m endo.rows.length endo.rows)ᵀ = realField m endo.rows.length endo.rows)
    (y : Fin m → ℝ) :
    (covector (Program.primitive map).outputArity [1]).comp
        (fderiv ℝ (realProgram (.primitive map) m) y) =
      (dkCotangent (· ^ k) (hermAt (realField m endo.rows.length endo.rows) hM y)
        (trPairing 1)).comp (hermDeriv (realField m endo.rows.length endo.rows) hM y) := by
  rw [covector_fderiv_tracePower envValid valid hm hM [1] y]
  simp

end Invariant

/-! ## Accepted Core: the `differential` of an accepted trace power -/

section Checked

/-- **Checked DK gradient.** An accepted `differential(f, p)` node whose function operand evaluates
to an accepted `trace_power(H, k)` of a symmetric declared endomorphism evaluates to a covector
over `p`, with one component per coordinate, that is the Daleckii–Krein cotangent of `Re tr` at
`H(p)` composed with `DH(p)`. -/
theorem checked_trace_power_dk {module : Core.Module} {functions : Core.Typing.Signatures}
    {ctx : Core.Typing.Context} {world : World} {fuel : ℕ} {values : Values} {id : DeclId}
    {function point : Core.Term} {result : Result} {smooth cotangent line : DeclId}
    {operands : List ValueType} {output : ValueType} {pointValue : Value}
    {application : Application} {map : Map} {endo : EndoRef} {k : ℕ}
    (envValid : module.declarations.indexed.Valid)
    (valid : spectralInvariantValid module.declarations.indexed application map
      (.tracePower endo k) = true)
    (hsym : endo.symmetric = true)
    (found : module.declarations.primitive? id = some (.differential smooth cotangent line))
    (input : ([function, point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Core.Typing.HasType module.declarations functions ctx
      (.primitive id [function, point] result))
    (functionEval : eval module fuel values function = some (.indexed (.smooth (.primitive map))))
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world
      [.indexed (.smooth (.primitive map)), pointValue] operands) :
    ∃ (x : Program) (m : ℕ)
      (hM : (realField m endo.rows.length endo.rows)ᵀ = realField m endo.rows.length endo.rows),
      smoothDimension? module.declarations.indexed endo.object = some m ∧
      pointValue = .indexed (.smooth x) ∧ (coordinates x).length = m ∧
      ∃ r : Fiber,
        eval module (fuel + 1) values (.primitive id [function, point] result) =
          some (.indexed (.fiber .cotangent (some r))) ∧
        r.point = coordinates x ∧ r.components.length = m ∧
        covector m r.components =
          (dkCotangent (· ^ k)
            (hermAt (realField m endo.rows.length endo.rows) hM (realPoint m (coordinates x)))
            (trPairing 1)).comp
            (hermDeriv (realField m endo.rows.length endo.rows) hM (realPoint m (coordinates x))) := by
  obtain ⟨φ, x, n, hφ, rfl, hwt, hx, r, hr, hpoint, hlength, hcov⟩ :=
    VastitasBridge.Differential.checked_differential_frechet found input outputType accepted
      functionEval pointEval typed
  simp only [Value.indexed.injEq, IndexedValue.smooth.injEq] at hφ
  subst hφ
  obtain ⟨m, hm, harity, -, -⟩ := realProgram_tracePower envValid valid
  have hn : n = m := by
    have h := (VastitasBridge.Differential.wellFormed_iff.mp hwt).arity
    omega
  subst hn
  have declared : DeclaredEndo module.declarations.indexed endo :=
    (VastitasOracle.SpectralCore.spectralInvariant_valid_sound valid).1
  have hM := endo_realField_symm envValid declared hsym n
  exact ⟨x, n, hM, hm, rfl, hx, r, hr, hpoint, hlength, by
    rw [hcov, tracePower_fderiv_dk envValid valid hm hM]⟩

end Checked

/-! ## Compiled reverse Core along an accepted trace power -/

section Compiled

/-- What a reverse site of one declared step along the map of `trace_power(H, k)` computes, in
each mode: a call of its generated function evaluates to a covector over the input point whose
components are the seed's component times the Daleckii–Krein cotangent of `Re tr` at `H(y)`
composed with `DH(y)`. -/
def TracePowerSiteDK (module : Core.Module) (entry : Core.Reverse.Entry) (map : Map)
    (endo : EndoRef) (k m : ℕ)
    (hM : (realField m endo.rows.length endo.rows)ᵀ = realField m endo.rows.length endo.rows) :
    Prop :=
  (entry.site.mode = .saved →
    ∀ (values : Values) (arguments : List Core.Term) (start : Program) (outputs : List Program)
      (variance : Variance) (seed : Fiber) (substitution : List (Indexed.ObjectRef × Indexed.ObjectRef))
      (result : Result),
      (coordinates start).length = m → ResidualRel [.primitive map] start outputs →
      seed.point = (Program.primitive map).eval (coordinates start) →
      seed.components.length = 1 →
      ArgumentsEvaluate module values arguments
        (functionArguments [] (start :: outputs) variance (some seed)) →
      ∃ r : Fiber,
        Evaluates module values (.call entry.function arguments substitution result)
          (.indexed (.fiber .cotangent (some r))) ∧
        r.point = coordinates start ∧ r.components.length = m ∧
        covector m r.components = ((seed.components.getD 0 0 : ℚ) : ℝ) •
          (dkCotangent (· ^ k)
            (hermAt (realField m endo.rows.length endo.rows) hM (realPoint m (coordinates start)))
            (trPairing 1)).comp
            (hermDeriv (realField m endo.rows.length endo.rows) hM
              (realPoint m (coordinates start)))) ∧
  (entry.site.mode = .recomputed →
    ∀ (values : Values) (arguments : List Core.Term) (start : Program) (variance : Variance)
      (seed : Fiber) (substitution : List (Indexed.ObjectRef × Indexed.ObjectRef)) (result : Result),
      (coordinates start).length = m →
      seed.point = (Program.primitive map).eval (coordinates start) →
      seed.components.length = 1 →
      ArgumentsEvaluate module values arguments (functionArguments [] [start] variance (some seed)) →
      ∃ r : Fiber,
        Evaluates module values (.call entry.function arguments substitution result)
          (.indexed (.fiber .cotangent (some r))) ∧
        r.point = coordinates start ∧ r.components.length = m ∧
        covector m r.components = ((seed.components.getD 0 0 : ℚ) : ℝ) •
          (dkCotangent (· ^ k)
            (hermAt (realField m endo.rows.length endo.rows) hM (realPoint m (coordinates start)))
            (trPairing 1)).comp
            (hermDeriv (realField m endo.rows.length endo.rows) hM
              (realPoint m (coordinates start))))

/-- **An entry along an accepted trace power computes the DK cotangent.** An entry that computes
`η ∘ DF(x)` (`EntryFrechet`), whose site is one declared step along the map of a valid
`trace_power(H, k)` binding, computes the seed's component times the Daleckii–Krein cotangent. -/
theorem EntryFrechet.trace_power_dk {module : Core.Module} {entry : Core.Reverse.Entry}
    (hf : EntryFrechet module entry) (declarations : module.declarations.Valid)
    {step : Core.Reverse.Step} (hsteps : entry.site.steps = [step]) {morphism : DeclId}
    {stepApplication : Application} {map : Map}
    (kind : step.kind = .declared morphism stepApplication map) {application : Application}
    {endo : EndoRef} {k : ℕ}
    (found : module.declarations.primitive? morphism =
      some (.spectralInvariant application map (.tracePower endo k)))
    {m : ℕ} (hm : smoothDimension? module.declarations.indexed endo.object = some m)
    (hM : (realField m endo.rows.length endo.rows)ᵀ = realField m endo.rows.length endo.rows) :
    TracePowerSiteDK module entry map endo k m hM := by
  have valid : spectralInvariantValid module.declarations.indexed application map
      (.tracePower endo k) = true := VastitasOracle.FrameCore.binding_valid declarations found
  have envValid := declarations.indexed
  obtain ⟨-, -, m', -, image, -, hm0, -, harity, hbasis, himages, hcanonical, -, -⟩ :=
    VastitasOracle.SpectralCore.spectralInvariant_valid_sound valid
  have hm' : smoothDimension? module.declarations.indexed endo.object = some m' := hm0
  rw [hm] at hm'
  cases hm'
  have hprograms : stepPrograms entry.site.steps [] = [.primitive map] := by
    rw [hsteps]
    simp [stepPrograms, kind]
  have hchain : chain (stepPrograms entry.site.steps []) = .primitive map := by
    rw [hprograms]
    rfl
  have hopaque : ([] : List Program).length = entry.site.opaqueSteps.length := by
    simp [Core.Reverse.Site.opaqueSteps, hsteps, kind]
  have hwt : (chain (stepPrograms entry.site.steps [])).wellTyped m 1 = true := by
    rw [hchain]
    simp [Program.wellTyped, SmoothRuntime.wellFormed, harity, hbasis, himages, hcanonical]
  refine ⟨fun hmode values arguments start outputs variance seed substitution result hlen hres hpt
      hcomp hargs => ?_, fun hmode values arguments start variance seed substitution result hlen hpt
      hcomp hargs => ?_⟩
  · obtain ⟨r, hev, hrp, hrl, hcov⟩ := hf.saved hmode values arguments [] m 1 start outputs variance
      seed substitution result hopaque hwt hlen (by rw [hprograms]; exact hres)
      (by rw [hchain]; exact hpt) hcomp hargs
    refine ⟨r, hev, hrp, hrl, ?_⟩
    rw [hcov, hchain, covector_fderiv_tracePower envValid valid hm hM]
  · obtain ⟨r, hev, hrp, hrl, hcov⟩ := hf.recomputed hmode values arguments [] m 1 start variance
      seed substitution result hopaque hwt hlen (by rw [hchain]; exact hpt) hcomp hargs
    refine ⟨r, hev, hrp, hrl, ?_⟩
    rw [hcov, hchain, covector_fderiv_tracePower envValid valid hm hM]

/-- Every reverse site of `entry` that is one declared step along the map of a symmetric
`trace_power(H, k)` declaration computes its Daleckii–Krein cotangent. -/
def TracePowerDK (module : Core.Module) (entry : Core.Reverse.Entry) : Prop :=
  ∀ (step : Core.Reverse.Step) (morphism : DeclId) (stepApplication : Application) (stepMap : Map)
    (application : Application) (map : Map) (endo : EndoRef) (k m : ℕ),
    entry.site.steps = [step] → step.kind = .declared morphism stepApplication stepMap →
    module.declarations.primitive? morphism =
      some (.spectralInvariant application map (.tracePower endo k)) →
    endo.symmetric = true → smoothDimension? module.declarations.indexed endo.object = some m →
    stepMap = map ∧
      ∃ hM : (realField m endo.rows.length endo.rows)ᵀ = realField m endo.rows.length endo.rows,
        TracePowerSiteDK module entry map endo k m hM

/-- The entries of a compiled module that compute `η ∘ DF(x)` compute the DK cotangent along their
trace-power steps: the step's map is the invariant's own (`compiled_invariant_step`). -/
theorem trace_power_dk_of_frechet {requireMain : Bool}
    {source : Core.Typing.CheckedModule requireMain} (compiled : Core.Reverse.Compiled source)
    (frechet : ∀ entry ∈ compiled.entries, EntryFrechet compiled.core.module entry) :
    ∀ entry ∈ compiled.entries, TracePowerDK compiled.core.module entry := by
  intro entry member step morphism stepApplication stepMap application map endo k m hsteps kind
    found hsym hm
  obtain ⟨hsame, -⟩ := VastitasOracle.SpectralCore.compiled_invariant_step compiled member
    (by rw [hsteps]; exact List.mem_singleton_self _) kind found
  subst hsame
  have declarations := compiled.core.typed.declarations
  have valid : spectralInvariantValid compiled.core.module.declarations.indexed application stepMap
      (.tracePower endo k) = true := VastitasOracle.FrameCore.binding_valid declarations found
  have hM := endo_realField_symm declarations.indexed
    (VastitasOracle.SpectralCore.spectralInvariant_valid_sound valid).1 hsym m
  exact ⟨rfl, hM, EntryFrechet.trace_power_dk (frechet entry member) declarations hsteps kind found
    hm hM⟩

/-- **Every compiled module.** -/
theorem compiled_trace_power_dk {requireMain : Bool}
    {source : Core.Typing.CheckedModule requireMain} (compiled : Core.Reverse.Compiled source) :
    ∀ entry ∈ compiled.entries, TracePowerDK compiled.core.module entry :=
  trace_power_dk_of_frechet compiled (VastitasBridge.Differential.compiled_entries_frechet compiled)

/-- **Protocols 8/9.** For every JSON that `ResourceSource.Wire.check` accepts, every entry of the
compiled pure program and of the compiled value fragments computes the DK cotangent along its
trace-power steps. -/
theorem public_resource_entries_trace_power_dk {json : Lean.Json} {requireMain : Bool}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain) :
    (∀ entry ∈ input.checked.pureProgram.compiled.entries,
      TracePowerDK input.checked.pureProgram.compiled.core.module entry) ∧
    ∀ entry ∈ input.checked.values.compiled.entries,
      TracePowerDK input.checked.values.compiled.core.module entry :=
  ⟨trace_power_dk_of_frechet _ (VastitasBridge.Differential.public_resource_entries_frechet input).1,
    trace_power_dk_of_frechet _ (VastitasBridge.Differential.public_resource_entries_frechet input).2⟩

/-- **Protocols 8/9 emit without a resource entry.** The module that the public emit path
generates code from computes the DK cotangent along its trace-power steps. -/
theorem public_pure_entry_trace_power_dk {json : Lean.Json}
    {program : VastitasKernel.ResourceSource.Program}
    {generated : VastitasKernel.ResourceSource.Codegen.Generated}
    (decoded : VastitasKernel.ResourceSource.Wire.program json = .ok program)
    (found : program.entry = none)
    (emitted : VastitasKernel.ResourceSource.Wire.emit json = .ok generated) :
    ∃ checked : VastitasKernel.ResourceSource.Checked program true,
      VastitasKernel.ResourceSource.check program true = .ok checked ∧
    ∃ core : Core.Typing.CheckedModule true,
      core.module = checked.pureProgram.compiled.core.module ∧
      Core.Codegen.generate core = .ok generated.source ∧
      ∀ entry ∈ checked.pureProgram.compiled.entries, TracePowerDK core.module entry := by
  obtain ⟨checked, accepted, core, same, emittedCore, frechet⟩ :=
    VastitasBridge.Differential.public_pure_entry_frechet decoded found emitted
  refine ⟨checked, accepted, core, same, emittedCore, ?_⟩
  rw [same]
  exact trace_power_dk_of_frechet _ (by rw [← same]; exact frechet)

end Compiled

/-! ## The Stage 5 field -/

section Stage5

/-- The Stage 5 field `H = rows((x, y), (y, −x))` over `MvPolynomial (Fin 2) ℝ`. -/
def stage5Field : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 2) ℝ) :=
  realField 2 2 VastitasOracle.SpectralDeclarations.Examples.rows

theorem stage5Field_symm : stage5Fieldᵀ = stage5Field :=
  realField_transpose VastitasOracle.SpectralDeclarations.Examples.rows_symmetric

theorem realPoly_var_two (i : Fin 2) : realPoly 2 (Poly.var 2 i) = MvPolynomial.X i := by
  have he : VastitasBridge.AlgebraicGeometry.Kernel.toExp 2
      (VastitasKernel.AlgebraRuntime.Monomial.var 2 i) = Finsupp.single i 1 := by
    ext j
    fin_cases i <;> fin_cases j <;>
      simp [VastitasBridge.AlgebraicGeometry.Kernel.toExp_apply,
        VastitasKernel.AlgebraRuntime.Monomial.var]
  rw [realPoly, Poly.var, VastitasBridge.AlgebraicGeometry.Kernel.toMv_cons,
    VastitasBridge.AlgebraicGeometry.Kernel.toMv_nil, add_zero,
    VastitasBridge.AlgebraicGeometry.Kernel.termMv, he]
  simp [MvPolynomial.X]

theorem stage5Field_eq : stage5Field =
    !![MvPolynomial.X 0, MvPolynomial.X 1; MvPolynomial.X 1, -MvPolynomial.X 0] := by
  have hx : realPoly 2 VastitasOracle.SpectralDeclarations.Examples.x = MvPolynomial.X 0 :=
    realPoly_var_two 0
  have hy : realPoly 2 VastitasOracle.SpectralDeclarations.Examples.y = MvPolynomial.X 1 :=
    realPoly_var_two 1
  have hnx : realPoly 2 (Poly.neg VastitasOracle.SpectralDeclarations.Examples.x) =
      -MvPolynomial.X 0 := by
    rw [realPoly, VastitasBridge.AlgebraicGeometry.Kernel.toMv_neg, map_neg, ← realPoly, hx]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stage5Field, realField, polyEntry, VastitasOracle.SpectralDeclarations.Examples.rows, hx,
      hy, hnx]

/-- **The roadmap gradient through Daleckii–Krein.** For the Stage 5 field, at every real point
`y`, the Daleckii–Krein cotangent of `Re tr` for `t ↦ t²` at `H(y)`, composed with `DH(y)`, is
the covector `(4y₀, 4y₁)`. -/
theorem stage5_dk_gradient (y v : Fin 2 → ℝ) :
    (dkCotangent (· ^ 2) (hermAt stage5Field stage5Field_symm y) (trPairing 1)).comp
      (hermDeriv stage5Field stage5Field_symm y) v = 4 * y 0 * v 0 + 4 * y 1 * v 1 := by
  rw [← fderiv_trace_pow_field stage5Field stage5Field_symm 2 y,
    fderiv_trace_pow_field_apply stage5Field stage5Field_symm 2 y v, stage5Field_eq]
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, MvPolynomial.pderiv_X]
  ring

end Stage5

/-! ## The branch differential is the derivative of every branch -/

section Branch

open VastitasKernel.SmoothRuntime (evalAt partialDerivative)
open VastitasKernel.SpectralRuntime (onBranch slopeAt branchPoint branchDifferential)

theorem eval_map_ratCast {n : ℕ} (g : Fin n → ℚ) (Q : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.eval (fun i => (g i : ℝ)) (MvPolynomial.map (algebraMap ℚ ℝ) Q) =
      ((MvPolynomial.eval g Q : ℚ) : ℝ) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- The real value of a formal partial derivative at a rational point is the rational value. -/
theorem eval_realPoly_pderiv {n : ℕ} {p : Poly} (hp : VastitasOracle.SmoothCalculus.Arity n p)
    (j : Fin n) {z : List ℚ} (hz : z.length = n) :
    MvPolynomial.eval (realPoint n z) (MvPolynomial.pderiv j (realPoly n p)) =
      ((evalAt (partialDerivative j p) z : ℚ) : ℝ) := by
  rw [realPoly, MvPolynomial.pderiv_map, ← VastitasBridge.Differential.toMv_partial j.isLt hp,
    VastitasBridge.Differential.evalAt_eq_eval (VastitasOracle.SmoothCalculus.arity_partial hp j) hz]
  exact eval_map_ratCast (fun i : Fin n => z.getD i 0) _

theorem realPoint_snoc {m : ℕ} {z w : List ℚ} (hz : z.length = m) :
    (Fin.snoc (realPoint m z) ((w.getD 0 0 : ℚ) : ℝ) : Fin (m + 1) → ℝ) =
      realPoint (m + 1) (z ++ w) := by
  have h1 : (z ++ w).getD m 0 = w.getD 0 0 := by
    rw [← hz]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  have h2 : ∀ j < m, (z ++ w).getD j 0 = z.getD j 0 := fun j hj => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show j < z.length by omega)]
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [realPoint, Fin.snoc_last, Fin.val_last, h1]
  · simp only [realPoint, Fin.snoc_castSucc, Fin.val_castSucc, h2 i i.isLt]

/-- **The emitted branch differential is the derivative of every branch.** In a valid
environment an accepted `branch_differential(p, t, branch = B)` evaluates to the runtime branch
differential. On the branch it is a covector over `p` that equals `Dλ(p)` for every real function
`λ` that is differentiable at `p`, passes through `(p, t)` and keeps `χ(x, λ x) = 0` near `p`. -/
theorem checked_branch_differential_implicit {module : Core.Module}
    {functions : Core.Typing.Signatures} {ctx : Core.Typing.Context} {world : World} {fuel : ℕ}
    {values : Values} {id : DeclId} {result : Result} {operands : List ValueType}
    {output : ValueType} {point valueTerm : Core.Term} {smooth cotangent line : DeclId}
    {branch : BranchRef} {pointValue valueValue : Value}
    (envValid : module.declarations.indexed.Valid)
    (found : module.declarations.primitive? id =
      some (.branchDifferential smooth cotangent line branch))
    (input : ([point, valueTerm].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Core.Typing.HasType module.declarations functions ctx
      (.primitive id [point, valueTerm] result))
    (pointEval : eval module fuel values point = some pointValue)
    (valueEval : eval module fuel values valueTerm = some valueValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [pointValue, valueValue]
      operands) :
    ∃ m x v, pointValue = .indexed (.smooth x) ∧ valueValue = .indexed (.smooth v) ∧
      (coordinates x).length = m ∧ (coordinates v).length = 1 ∧
      eval module (fuel + 1) values (.primitive id [point, valueTerm] result) =
        some (.indexed (.fiber .cotangent
          (branchDifferential branch.localize branch.spectrum.characteristic x v))) ∧
      (onBranch branch.localize branch.spectrum.characteristic x v = true →
        ∃ fiber : Fiber,
          branchDifferential branch.localize branch.spectrum.characteristic x v = some fiber ∧
          fiber.point = coordinates x ∧ fiber.components.length = m ∧
          ∀ lam : (Fin m → ℝ) → ℝ, DifferentiableAt ℝ lam (realPoint m (coordinates x)) →
            lam (realPoint m (coordinates x)) = (((coordinates v).getD 0 0 : ℚ) : ℝ) →
            (∀ᶠ z in 𝓝 (realPoint m (coordinates x)),
              MvPolynomial.eval (Fin.snoc z (lam z) : Fin (m + 1) → ℝ)
                (realPoly (m + 1) branch.spectrum.characteristic) = 0) →
            fderiv ℝ lam (realPoint m (coordinates x)) = covector m fiber.components) := by
  obtain ⟨m, x, v, rfl, rfl, hx, hv, evaluated, -, hon⟩ :=
    VastitasOracle.SpectralAcceptance.c10_branch_derivative envValid found input outputType accepted
      pointEval valueEval typed
  obtain ⟨declared, -, m', x', v', hm', hxeq, -, hx', -, -, -⟩ :=
    VastitasOracle.SpectralCore.core_spectral_branch_differential found input outputType accepted
      pointEval valueEval typed
  simp only [Value.indexed.injEq, IndexedValue.smooth.injEq] at hxeq
  subst hxeq
  have hmm : m' = m := by omega
  subst hmm
  obtain ⟨m'', idempotence, quotient, hm'', hvalid, hw⟩ := declared.checked envValid
  rw [hm'] at hm''
  cases hm''
  refine ⟨m', x, v, rfl, rfl, hx, hv, evaluated, fun hb => ?_⟩
  obtain ⟨fiber, P, hd, hP, hpoint, hlength, himpl⟩ := hon hb
  refine ⟨fiber, hd, hpoint, hlength, fun lam hdiff hval hzero => ?_⟩
  have hs := hvalid.slopeAt_ne_zero hw hx hb
  have hχ := hvalid.characteristic_arity
  have hbp : (branchPoint x v).length = m' + 1 := by simp [branchPoint, hx, hv]
  have hsnoc : (Fin.snoc (realPoint m' (coordinates x)) (lam (realPoint m' (coordinates x))) :
      Fin (m' + 1) → ℝ) = realPoint (m' + 1) (branchPoint x v) := by
    rw [hval]
    exact realPoint_snoc hx
  have hpartial : ∀ j : Fin (m' + 1),
      MvPolynomial.eval (Fin.snoc (realPoint m' (coordinates x)) (lam (realPoint m' (coordinates x))) :
        Fin (m' + 1) → ℝ) (MvPolynomial.pderiv j (realPoly (m' + 1) branch.spectrum.characteristic)) =
        ((evalAt (partialDerivative j branch.spectrum.characteristic) (branchPoint x v) : ℚ) : ℝ) :=
    fun j => by rw [hsnoc]; exact eval_realPoly_pderiv hχ j hbp
  have hslope : ((slopeAt branch.spectrum.characteristic x v : ℚ) : ℝ) =
      MvPolynomial.eval (Fin.snoc (realPoint m' (coordinates x)) (lam (realPoint m' (coordinates x))) :
        Fin (m' + 1) → ℝ) (MvPolynomial.pderiv (Fin.last m') (realPoly (m' + 1) branch.spectrum.characteristic)) := by
    rw [hpartial]
    simp [slopeAt, hx]
  have hsR : ((slopeAt branch.spectrum.characteristic x v : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hs
  ext w
  rw [VastitasBridge.Spectral.implicit_branch_fderiv_eval _ hdiff hzero (by rw [← hslope]; exact hsR) w,
    covector_apply, ← hslope, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hpartial]
  have hc := (himpl i i.isLt).1
  have hcR : ((fiber.components.getD i 0 : ℚ) : ℝ) * ((slopeAt branch.spectrum.characteristic x v : ℚ) : ℝ) =
      -((evalAt (partialDerivative i branch.spectrum.characteristic) (branchPoint x v) : ℚ) : ℝ) := by
    exact_mod_cast hc
  simp only [Fin.val_castSucc]
  field_simp
  linear_combination -(w i) * hcR

end Branch

end VastitasBridge.Spectral
