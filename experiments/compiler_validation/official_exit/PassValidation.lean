import FunctionLowering

/-! Validate the pass and its resolution trace against the independent namespace index. -/
namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed FunctionSource
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

attribute [local cbv_opaque] accumulated idx geometry
theorem traceValid : functionPass.references.all (fun r => decide (r.Valid readyCompiler.input.body.index)) = true := by
  apply List.all_eq_true.mpr
  intro r member
  change r ∈ (geometryNames.map (ref ·)).reverse at member
  obtain ⟨n, hn,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp member)
  have known : ∀ n ∈ geometryNames, n ∈ names := by decide
  exact decide_eq_true (referenceValid n (known n hn))

theorem passValid (audit : Bool) : Compiler.validPass readyCompiler.input audit functionPass = true := by
  unfold Compiler.validPass
  rw [traceValid]
  cases audit <;> cbv

theorem noFamilies : Compiler.validFamilyUses readyCompiler.input functionPass = true := rfl

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.passValid
