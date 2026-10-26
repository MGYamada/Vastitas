import VastitasKernel.DispatchChecker
import VastitasOracle.Dispatch
import VastitasOracle.ActivationSafety

/-! Stage 1's actual acceptance path is connected to the complete checked-core
theorems, not only the historical annotation certificate. Finite target choices
retain the real checker equation and row equation, so their unique optimality
is established by the independently specified dispatch selection relation.

This does not prove the Rust parser, the raw rewriting pass's full source
correspondence, or Lean/C/native code generation. The semantic theorem concerns
the exact lowered core returned by the public Stage 1 checker. -/
namespace VastitasOracle.DispatchLowering
open VastitasKernel VastitasKernel.DispatchChecker VastitasKernel.Semantics

theorem selected_target_sound (family : Family) (key : Dispatch.Key) (target : Target family key) :
    key ∈ family.domain ∧
    Dispatch.Selection Dispatch.publicHierarchy family.checked.methods key (some target.method) :=
  ⟨target.admitted, VastitasOracle.Dispatch.winner_sound family.raw.params.length
    family.domain family.methods family.checked family.accepted key target.method target.selected⟩

/-- No branch accepts before the unchanged core checker has accepted the exact
lowered module. Diagnostic decoration affects failures only. -/
theorem checkProgram_core (program : RawProgram) (requireMain : Bool) (certified : CertifiedModule)
    (accepted : checkProgram program requireMain = .ok certified) :
    ∃ core, lowerProgram program = .ok core ∧ checkModule core requireMain = .ok certified := by
  unfold checkProgram at accepted
  cases lowered : lowerProgram program with
  | error diagnostic => simp [lowered, bind, Except.bind] at accepted
  | ok core =>
      simp only [lowered, bind, Except.bind] at accepted
      cases checked : checkModule core requireMain with
      | error diagnostic => simp [checked, throw] at accepted
      | ok result =>
          simp [checked, pure, Except.pure] at accepted
          subst result
          exact ⟨core, rfl, checked⟩

theorem checkProgram_typed_and_ordered (program : RawProgram) (requireMain : Bool)
    (certified : CertifiedModule) (accepted : checkProgram program requireMain = .ok certified) :
    Typing.ModuleWellTyped certified.val ∧ Dependency.ModuleOrdered certified.val := by
  obtain ⟨core, _, checked⟩ := checkProgram_core program requireMain certified accepted
  obtain ⟨_, _, typed, ordered⟩ := checkModule_typed_and_ordered core requireMain certified checked
  exact ⟨typed, ordered⟩

/-- Public Stage 1 acceptance establishes termination and endpoint preservation
of every generated core function for all well-typed argument environments. -/
theorem checkProgram_total_for_arguments (program : RawProgram) (requireMain : Bool)
    (certified : CertifiedModule) (accepted : checkProgram program requireMain = .ok certified)
    (function : CheckedFunction) (member : function ∈ certified.val.functions)
    (world : World) (env : Environment) (context : ContextHasType world env function.params) :
    ∃ value, Eval certified.val.functions env function.body value ∧
      ValueHasType world value function.returnType := by
  obtain ⟨typed, ordered⟩ := checkProgram_typed_and_ordered program requireMain certified accepted
  exact ActivationSafety.module_total_for_arguments certified.val typed ordered function member world env context

end VastitasOracle.DispatchLowering
