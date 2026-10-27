import VastitasKernel.FunctionChecker
import VastitasOracle.DispatchLowering

/-! Soundness of the actual Stage 1b acceptance boundary. These results prove
source lambda closure freedom, independently audited static function contracts,
and typing/termination of the exact emitted core. They do not claim a complete
operational correspondence for specialization or equivalence of native code. -/
namespace VastitasOracle.Functions
open VastitasKernel VastitasKernel.Surface VastitasKernel.Semantics

theorem checkSurfaceProgram_capture_free (program : Surface.Program) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkSurfaceProgram program requireMain = .ok certified) :
    CaptureFree program := by
  by_cases free : CaptureFree program
  · exact free
  · simp [checkSurfaceProgram, free, throw, bind, Except.bind] at accepted

/-- The new syntax path checks the actual lowering result and its actual target
ledger before handing that very module to the independent core checker. -/
theorem checkSurfaceProgram_static_calls (program : Surface.Program) (requireMain : Bool)
    (certified : CertifiedModule) (expanded : program.legacyExact = none)
    (accepted : checkSurfaceProgram program requireMain = .ok certified) :
    ∃ lowered, lowerFunctions program = .ok lowered ∧ StaticCallsValid lowered ∧
      checkModule lowered.module requireMain = .ok certified := by
  have free := checkSurfaceProgram_capture_free program requireMain certified accepted
  cases lowered : lowerFunctions program with
  | error diagnostic => simp [checkSurfaceProgram, free, expanded, lowered, bind, Except.bind] at accepted
  | ok result =>
    by_cases valid : StaticCallsValid result
    · refine ⟨result, rfl, valid, ?_⟩
      simpa [checkSurfaceProgram, free, expanded, lowered, valid, bind, Except.bind] using accepted
    · simp [checkSurfaceProgram, free, expanded, lowered, valid, bind, Except.bind, throw] at accepted

theorem checkSurfaceProgram_core (program : Surface.Program) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkSurfaceProgram program requireMain = .ok certified) :
    ∃ core, checkModule core requireMain = .ok certified := by
  have free := checkSurfaceProgram_capture_free program requireMain certified accepted
  cases legacy : program.legacyExact with
  | none =>
    obtain ⟨lowered, _, _, checked⟩ :=
      checkSurfaceProgram_static_calls program requireMain certified legacy accepted
    exact ⟨lowered.module, checked⟩
  | some raw =>
    have old : checkProgram raw requireMain = .ok certified := by
      simpa [checkSurfaceProgram, free, legacy] using accepted
    obtain ⟨core, _, checked⟩ := DispatchLowering.checkProgram_core raw requireMain certified old
    exact ⟨core, checked⟩

theorem checkSurfaceProgram_typed_and_ordered (program : Surface.Program) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkSurfaceProgram program requireMain = .ok certified) :
    Typing.ModuleWellTyped certified.val ∧ Dependency.ModuleOrdered certified.val := by
  obtain ⟨core, checked⟩ := checkSurfaceProgram_core program requireMain certified accepted
  obtain ⟨_, _, typed, ordered⟩ := checkModule_typed_and_ordered core requireMain certified checked
  exact ⟨typed, ordered⟩

theorem lambda_free_names_are_global (program : Surface.Program) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkSurfaceProgram program requireMain = .ok certified)
    (scope : List String × Span) (member : scope ∈ program.scopes)
    (name : String) (freeName : name ∈ scope.1) : name ∈ program.globals :=
  checkSurfaceProgram_capture_free program requireMain certified accepted scope member name freeName

/-- Each recorded target has the exact structural Fn signature of an actual
backend definition; equal argument counts alone would not establish this. -/
theorem static_target_signature (lowered : Lowered) (valid : StaticCallsValid lowered)
    (call : StaticCall) (member : call ∈ lowered.calls) :
    ∃ definition ∈ lowered.definitions,
      definition.name = call.target ∧ definition.type = call.signature :=
  (valid call member).1

/-- Function arguments retain their expected contract even when erased from the
runtime parameter list. Their implementations are identified in the same table. -/
theorem function_argument_signature (lowered : Lowered) (valid : StaticCallsValid lowered)
    (call : StaticCall) (member : call ∈ lowered.calls)
    (binding : TypeExpr × Surface.Target) (argument : binding ∈ call.bindings) :
    binding.1 = binding.2.ty ∧ ∃ definition ∈ lowered.definitions,
      definition.name = binding.2.name ∧ definition.type = binding.2.ty :=
  (valid call member).2 binding argument

theorem checkSurfaceProgram_total_for_arguments (program : Surface.Program) (requireMain : Bool)
    (certified : CertifiedModule) (accepted : checkSurfaceProgram program requireMain = .ok certified)
    (function : CheckedFunction) (member : function ∈ certified.val.functions)
    (world : World) (env : Environment) (context : ContextHasType world env function.params) :
    ∃ value, Eval certified.val.functions env function.body value ∧
      ValueHasType world value function.returnType := by
  obtain ⟨typed, ordered⟩ := checkSurfaceProgram_typed_and_ordered program requireMain certified accepted
  exact ActivationSafety.module_total_for_arguments certified.val typed ordered function member world env context

end VastitasOracle.Functions
