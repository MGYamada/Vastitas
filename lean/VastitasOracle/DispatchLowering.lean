import VastitasKernel.FunctionChecker
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
    Dispatch.Selection family.nominals.hierarchy family.checked.methods key (some target.method) := by
  have correct := VastitasOracle.Dispatch.checkWith_sound family.nominals.hierarchy
    family.raw.params.length family.domain family.methods family.checked family.accepted
  refine ⟨target.admitted, ?_⟩
  have selected := VastitasOracle.Dispatch.winner_selection family.nominals.hierarchy
    family.raw.params.length family.domain family.methods family.checked correct key
    (correct.domain_valid key target.admitted)
  simpa [target.selected] using selected

/-- The structural audit fixes a Pair call's result to the actual selected
signature. No expected type or other candidate result participates. This also
applies to calls returned by surface and namespace acceptance via their core
typing theorems; it does not claim full raw-lowering correspondence. -/
theorem checked_call_pair_result (signatures : Typing.Signatures) (ctx : Typing.Context)
    (id : Nat) (args : List Term) (substitution : List (ObjectRef × ObjectRef))
    (result : ResultType) (signature : Typing.FunctionSignature) (element : PairElem)
    (found : Typing.lookupSignature signatures id = some signature)
    (returns : signature.returnType = .pair element)
    (typed : Typing.HasType signatures ctx (.call id args substitution result)) :
    result.ty = .pair element := by
  have rule := typed.2.2
  simp only [Typing.CallTyping, found] at rule
  simpa only [returns, Ty.rename] using rule.2.2.2.1

/-- No branch accepts before the core checker has accepted the exact
lowered module. Diagnostic decoration affects failures only. -/
theorem checkProgram_core (program : RawProgram) (requireMain : Bool) (certified : CertifiedModule)
    (accepted : checkProgram program requireMain = .ok certified) :
    ∃ lowered, Surface.lowerFunctions (Surface.Program.ofRaw program) = .ok lowered ∧
      checkModule lowered.module requireMain = .ok certified := by
  let surface := Surface.Program.ofRaw program
  change checkSurfaceProgram surface requireMain = .ok certified at accepted
  by_cases free : Surface.CaptureFree surface
  · by_cases shadowFree : Surface.LambdaShadowFree surface
    · cases lowered : Surface.lowerFunctions surface with
      | error diagnostic =>
        simp [checkSurfaceProgram, free, shadowFree, lowered, bind, Except.bind] at accepted
      | ok result =>
        by_cases valid : Surface.staticCallsValid result = true
        · refine ⟨result, rfl, ?_⟩
          simpa [checkSurfaceProgram, free, shadowFree, lowered, valid, bind, Except.bind] using accepted
        · simp [checkSurfaceProgram, free, shadowFree, lowered, valid, bind, Except.bind, throw] at accepted
    · simp [checkSurfaceProgram, free, shadowFree, bind, Except.bind, throw] at accepted
  · simp [checkSurfaceProgram, free, bind, Except.bind, throw] at accepted

theorem checkProgram_typed_and_ordered (program : RawProgram) (requireMain : Bool)
    (certified : CertifiedModule) (accepted : checkProgram program requireMain = .ok certified) :
    Typing.ModuleWellTyped certified.val ∧ Dependency.ModuleOrdered certified.val := by
  obtain ⟨core, _, checked⟩ := checkProgram_core program requireMain certified accepted
  obtain ⟨_, _, typed, ordered⟩ := checkModule_typed_and_ordered core.module requireMain certified checked
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
