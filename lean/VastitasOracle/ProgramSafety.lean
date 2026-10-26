import VastitasOracle.ModuleSafety
import VastitasOracle.EvaluationSafety
import VastitasOracle.ArgumentSafety
import VastitasOracle.AllocationSafety

namespace VastitasOracle.ProgramSafety
open VastitasKernel VastitasKernel.Typing VastitasKernel.Semantics

/-- Evaluation lookup and the checked signature index refer to the same unique
declaration. The evaluator does not consult a frontend-provided target. -/
theorem lookupFunction_member (functions : List CheckedFunction)
    (unique : (functions.map (·.id)).Nodup) (function : CheckedFunction)
    (member : function ∈ functions) :
    lookupFunction functions function.id = some function := by
  induction functions with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with equal | member
    · subst function
      simp [lookupFunction]
    · have different : head.id ≠ function.id := by
        intro equal
        apply unique.1
        rw [equal]
        exact List.mem_map.mpr ⟨function, member, rfl⟩
      simpa [lookupFunction, List.find?_cons, different] using ih unique.2 member

theorem function_brands_unique (module : CheckedModule)
    (fresh : FreshModule module) (function : CheckedFunction)
    (member : function ∈ module.functions) :
    (parameterRefs function.params ++ allocatedRefs function.body).Nodup := by
  unfold FreshModule at fresh
  generalize equality : module.functions = functions at fresh member
  clear equality
  induction functions with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.flatMap_cons] at fresh
    have parts := List.nodup_append.mp fresh
    rcases List.mem_cons.mp member with equal | member
    · subst function; exact parts.1
    · exact ih parts.2.1 member

theorem value_type_of_agreement (before after : World) (value : Value) (ty : Ty)
    (agree : ∀ ref ∈ ty.refs, interpretRef before ref = interpretRef after ref)
    (typed : ValueHasType after value ty) : ValueHasType before value ty := by
  cases value <;> cases ty <;>
    simp_all [ValueHasType, Ty.refs, RefDenotes]

/-- Returning to the caller discards fresh brands. The declared result can
mention only the parameters, whose interpretation evaluation preserves. -/
theorem function_safe_of_evaluation (functions : List CheckedFunction)
    (function : CheckedFunction)
    (resultType : function.body.ty = function.returnType)
    (resultScope : function.returnType.Scoped (parameterRefs function.params))
    (unique : (parameterRefs function.params ++ allocatedRefs function.body).Nodup)
    (evaluate : ∀ world env, ContextHasType world env function.params →
      WorldFreshFor world (allocatedRefs function.body) →
      TermOutcome functions world env function.body) :
    FunctionSafe functions function := by
  intro world env context fresh
  obtain ⟨after, value, evaluated, typed, _, unchanged⟩ := evaluate world env context fresh
  refine ⟨value, evaluated, value_type_of_agreement world after value function.returnType ?_ ?_⟩
  · intro ref member
    cases ref with
    | base base => rfl
    | «local» base id =>
      have parameter : ObjectRef.local base id ∈ parameterRefs function.params :=
        resultScope _ member
      have absent : ObjectRef.local base id ∉ allocatedRefs function.body := by
        intro allocated
        exact (List.nodup_append.mp unique).2.2 _ parameter _ allocated rfl
      exact (unchanged _ absent).symm
  · rw [← resultType]
    exact typed.1

/-- Induction over the checked topological order. Once earlier declarations
have semantic contracts, a local preservation theorem supplies the next one. -/
theorem ordered_functions_safe (module : CheckedModule)
    (extend : ∀ function ∈ module.functions,
      (∀ id ∈ function.body.callIds,
        ∃ callee ∈ module.functions, callee.id = id ∧ FunctionSafe module.functions callee) →
      FunctionSafe module.functions function)
    (ordered : Dependency.ModuleOrdered module) :
    ∀ function ∈ module.functions, FunctionSafe module.functions function := by
  have visit : ∀ (remaining : List CheckedFunction) (known : List Nat),
      (∀ function ∈ remaining, function ∈ module.functions) →
      Dependency.OrderedFrom known
        (remaining.map fun function =>
          ⟨function.id, function.body.callIds, function.span⟩) →
      (∀ id ∈ known,
        ∃ function ∈ module.functions, function.id = id ∧ FunctionSafe module.functions function) →
      ∀ function ∈ remaining, FunctionSafe module.functions function := by
    intro remaining
    induction remaining with
    | nil => intros; simp_all
    | cons head rest ih =>
      intro known included order previous
      cases order with
      | cons _ dependencies tailOrder =>
        have headMember : head ∈ module.functions := included head (by simp)
        have headSafe : FunctionSafe module.functions head :=
          extend head headMember (fun id member => previous id (dependencies id member))
        have tailSafe := ih (head.id :: known)
          (fun function member => included function (by simp [member])) tailOrder
          (by
            intro id member
            rcases List.mem_cons.mp member with equal | member
            · exact ⟨head, headMember, equal.symm, headSafe⟩
            · exact previous id member)
        intro function member
        rcases List.mem_cons.mp member with equal | member
        · simpa only [equal] using headSafe
        · exact tailSafe function member
  exact visit module.functions [] (fun _ member => member) ordered (by simp)

/-- Full checked-language termination and preservation: induction follows the
verified call order, then the actual expression syntax. No evaluator fuel or
semantic assumption about callees remains in the resulting contract. -/
theorem module_total_and_typed (module : CheckedModule)
    (typed : ModuleWellTyped module) (ordered : Dependency.ModuleOrdered module) :
    ∀ function ∈ module.functions, FunctionSafe module.functions function := by
  apply ordered_functions_safe module _ ordered
  intro function member callees
  have functionTyped := typed.2.2 function member
  have unique := function_brands_unique module typed.2.1 function member
  apply function_safe_of_evaluation module.functions function
    functionTyped.2.2.1 functionTyped.2.2.2 unique
  intro world env context fresh
  apply Safety.evaluation_total_and_typed module.functions (moduleSignatures module)
    function.params world env function.body _ functionTyped.2.1 context
    (List.nodup_append.mp unique).2.1 fresh
  intro id called
  obtain ⟨callee, declared, sameId, safe⟩ := callees id called
  apply ArgumentSafety.callSafe_returns
  refine ⟨callee, ?_, ?_, (typed.2.2 callee declared).1,
    function_brands_unique module typed.2.1 callee declared,
    Safety.allocations_local _ _ _ (typed.2.2 callee declared).2.1, safe⟩
  · rw [← sameId]
    exact lookupFunction_member module.functions typed.1 callee declared
  · rw [← sameId]
    exact SignatureLookup.module_lookup_member module typed.1 callee declared

/-- The actual public checker establishes the hypotheses of the full semantic
safety theorem; the legacy annotation subtype is not used as a substitute. -/
theorem checkModule_total_and_typed (raw : RawModule) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkModule raw requireMain = .ok certified) :
    ∀ function ∈ certified.val.functions,
      FunctionSafe certified.val.functions function := by
  obtain ⟨_, _, typed, ordered⟩ := checkModule_typed_and_ordered raw requireMain certified accepted
  exact module_total_and_typed certified.val typed ordered

end VastitasOracle.ProgramSafety
