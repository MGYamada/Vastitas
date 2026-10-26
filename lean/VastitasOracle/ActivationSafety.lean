import VastitasOracle.ProgramSafety

/-!
The public termination and preservation result quantifies over every well-typed
argument environment. Freshness is established by constructing an activation,
not required of the caller's ambient world. Different nominal IDs may denote
the same runtime object throughout these results.
-/
namespace VastitasOracle.ActivationSafety
open VastitasKernel VastitasKernel.Typing VastitasKernel.Semantics
open VastitasOracle.Safety VastitasOracle.ArgumentSafety VastitasOracle.ProgramSafety

theorem parameters_restrict (world : World) (env : Environment) (params : List CheckedParam)
    (formed : ParametersWellFormed [] params) (context : ContextHasType world env params) :
    ContextHasType (restrictWorld (parameterRefs params) world) env params := by
  intro param member
  obtain ⟨value, found, typed, branded⟩ := context param member
  refine ⟨value, found, ?_, ?_⟩
  · apply valueHasType_restrictWorld world (parameterRefs params) value param.ty
    · simpa [parameterRefs] using parameter_scopes [] params formed param member
    · exact typed
  · cases objectRef : param.resultType.objectRef with
    | none => trivial
    | some ref =>
        have branded : ValueHasObjectRef world value (some ref) := by
          simpa [objectRef] using branded
        obtain ⟨object, equal, denotes⟩ := branded
        refine ⟨object, equal, refDenotes_restrictWorld world (parameterRefs params) ref object ?_ denotes⟩
        cases ref with
        | base base => trivial
        | «local» base id =>
            exact List.mem_filterMap.mpr ⟨param, member, objectRef⟩

theorem restricted_activation_fresh (world : World) (params allocations : List ObjectRef)
    (unique : (params ++ allocations).Nodup)
    (localAllocations : ∀ ref ∈ allocations, LocalRef ref) :
    WorldFreshFor (restrictWorld params world) allocations := by
  intro ref member
  have absent : ref ∉ params := by
    intro inParams
    exact (List.nodup_append.mp unique).2.2 ref inParams ref member rfl
  cases ref with
  | base base => exact False.elim (localAllocations (.base base) member)
  | «local» base id => simp [interpretRef, restrictWorld, absent]

/-- Fresh activation removes the incidental freshness premise from FunctionSafe. -/
theorem function_total_for_arguments (functions : List CheckedFunction)
    (function : CheckedFunction) (formed : ParametersWellFormed [] function.params)
    (unique : (parameterRefs function.params ++ allocatedRefs function.body).Nodup)
    (localAllocations : ∀ ref ∈ allocatedRefs function.body, LocalRef ref)
    (safe : FunctionSafe functions function)
    (world : World) (env : Environment) (context : ContextHasType world env function.params) :
    ∃ value, Eval functions env function.body value ∧ ValueHasType world value function.returnType := by
  obtain ⟨value, evaluated, typed⟩ := safe
    (restrictWorld (parameterRefs function.params) world) env
    (parameters_restrict world env function.params formed context)
    (restricted_activation_fresh world _ _ unique localAllocations)
  exact ⟨value, evaluated, valueHasType_of_worldExtends _ _
    (restrictWorld_extends world (parameterRefs function.params)) value function.returnType typed⟩

/-- Every declared function in a well-typed, acyclic module terminates for every
well-typed argument environment and preserves its declared return endpoints. -/
theorem module_total_for_arguments (module : CheckedModule)
    (typed : ModuleWellTyped module) (ordered : Dependency.ModuleOrdered module)
    (function : CheckedFunction) (member : function ∈ module.functions)
    (world : World) (env : Environment) (context : ContextHasType world env function.params) :
    ∃ value, Eval module.functions env function.body value ∧
      ValueHasType world value function.returnType :=
  function_total_for_arguments module.functions function (typed.2.2 function member).1
    (function_brands_unique module typed.2.1 function member)
    (allocations_local _ _ _ (typed.2.2 function member).2.1)
    (module_total_and_typed module typed ordered function member) world env context

/-- Actual public checker acceptance implies termination and preservation for
all well-typed arguments, without a caller freshness or injectivity hypothesis. -/
theorem checkModule_total_for_arguments (raw : RawModule) (requireMain : Bool)
    (certified : CertifiedModule) (accepted : checkModule raw requireMain = .ok certified)
    (function : CheckedFunction) (member : function ∈ certified.val.functions)
    (world : World) (env : Environment) (context : ContextHasType world env function.params) :
    ∃ value, Eval certified.val.functions env function.body value ∧
      ValueHasType world value function.returnType := by
  obtain ⟨_, _, typed, ordered⟩ := checkModule_typed_and_ordered raw requireMain certified accepted
  exact module_total_for_arguments certified.val typed ordered function member world env context

end VastitasOracle.ActivationSafety
