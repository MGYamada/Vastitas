import VastitasOracle.IndexedFunctionSafety
import VastitasOracle.IndexedArgumentSafety
import VastitasOracle.IndexedSignatures

/-! Typed totality for the actual checked indexed Core. The checked dependency
order discharges every semantic callee contract; no evaluator success or
ambient world freshness is assumed. This is not a native-toolchain theorem. -/
namespace VastitasOracle.IndexedProgramSafety
open VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics VastitasKernel.Indexed.Core.Typing
open VastitasOracle.IndexedSemantics VastitasOracle.IndexedWorld
open VastitasOracle.IndexedValueSafety VastitasOracle.IndexedCallTransport
open VastitasOracle.IndexedArgumentSafety VastitasOracle.IndexedEvaluation
open VastitasOracle.IndexedEvaluationSafety VastitasOracle.IndexedFunctionSafety

theorem function_lookup {functions : List Function} (unique : (functions.map Function.id).Nodup)
    {function : Function} (member : function ∈ functions) :
    functions.find? (fun candidate => candidate.id == function.id) = some function := by
  induction functions with
  | nil => contradiction
  | cons head rest ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with equal | member
    · subst function; simp
    · have different : head.id ≠ function.id := fun equal =>
        unique.1 (equal ▸ List.mem_map.mpr ⟨function, member, rfl⟩)
      simpa [List.find?_cons, different] using ih unique.2 member

theorem function_call_returns (checked : CheckedModule requireMain) (function : Function)
    (member : function ∈ checked.module.functions) (returns : FunctionReturns checked.module function) :
    CallReturns checked.module (signatures checked.module) function.id := by
  intro world arguments operands substitution result rule resultValid argumentsTyped fresh
  have signatureFound := IndexedCore.signatures_member checked.module checked.typed.uniqueFunctions function member
  simp only [CallTyping, signatureFound, signatureOf] at rule
  have functionTyped := checked.typed.functions function member
  obtain ⟨activation, bound, context, transport⟩ := call_activation functionTyped.1 rule.2.1 argumentsTyped
  obtain ⟨value, evaluated, valueTyped⟩ := returns (objectWorld activation) activation context
  have called : Called checked.module function.id operands value :=
    ⟨function, activation, function_lookup checked.typed.uniqueFunctions member, bound, evaluated⟩
  have returnTransport : ∀ ref ∈ function.returnType.refs, ∀ object,
      RefDenotes checked.module.declarations.indexed (objectWorld activation) ref object →
      RefDenotes checked.module.declarations.indexed world (renameRef substitution ref) object := by
    intro ref refMember object denotes
    cases ref with
    | global _ => exact denotes
    | «local» type brand =>
      exact (transport (.local type brand) (functionTyped.2.2.2.2 _ refMember) object).mp denotes
  have returnRule := rule.2.2.2
  cases returnType : function.returnType with
  | object type =>
    rw [returnType] at valueTyped returnRule
    have callerType : ValueHasType checked.module.declarations world value (.object type) :=
      value_agreement (by simp [DataType.refs]) valueTyped
    obtain ⟨after, typed, extension, frame⟩ := local_result_total returnRule callerType fresh
    exact ⟨after, value, called, typed, extension, frame⟩
  | pure _ | indexed _ | package _ =>
    rw [returnType] at returnRule
    subst result
    refine ⟨world, value, called, ⟨?_, trivial⟩, worldExtends_refl world, unchanged_refl world _⟩
    rw [returnType] at valueTyped returnTransport
    exact value_rename_forward resultValid.1 returnTransport valueTyped

/-- Structural induction over the exact order accepted by `Dependency.audit`.
All targets are actual unique members, and both the signature table and runtime
lookup resolve to the same function. -/
theorem ordered_functions_return (checked : CheckedModule requireMain)
    (extend : ∀ function ∈ checked.module.functions,
      (∀ id ∈ function.body.callIds, ∃ callee ∈ checked.module.functions,
        callee.id = id ∧ FunctionReturns checked.module callee) →
      FunctionReturns checked.module function) :
    ∀ function ∈ checked.module.functions, FunctionReturns checked.module function := by
  have visit : ∀ (remaining : List Function) (known : List Nat),
      (∀ function ∈ remaining, function ∈ checked.module.functions) →
      VastitasKernel.Dependency.OrderedFrom known
        (remaining.map fun function => ⟨function.id, function.body.callIds, function.span⟩) →
      (∀ id ∈ known, ∃ function ∈ checked.module.functions,
        function.id = id ∧ FunctionReturns checked.module function) →
      ∀ function ∈ remaining, FunctionReturns checked.module function := by
    intro remaining
    induction remaining with
    | nil => intros; simp_all
    | cons head rest ih =>
      intro known included order previous
      cases order with
      | cons _ dependencies tailOrder =>
        have headMember := included head (List.mem_cons_self)
        have headReturns := extend head headMember (fun id member => previous id (dependencies id member))
        have tailReturns := ih (head.id :: known)
          (fun function member => included function (List.mem_cons_of_mem _ member)) tailOrder
          (by
            intro id member
            rcases List.mem_cons.mp member with equal | member
            · exact ⟨head, headMember, equal.symm, headReturns⟩
            · exact previous id member)
        intro function member
        rcases List.mem_cons.mp member with equal | member
        · exact equal ▸ headReturns
        · exact tailReturns function member
  exact visit checked.module.functions [] (fun _ member => member)
    (IndexedCore.checked_module_ordered checked) (by simp)

/-- Every function in an actually checked indexed module evaluates to a value
of its declared type for every typed activation. Evaluation has a finite bound
and the same result at every larger fuel. Callee safety and fresh allocations
are consequences of the actual module audits, not additional assumptions. -/
theorem checked_functions_total_and_typed (checked : CheckedModule requireMain) :
    ∀ function ∈ checked.module.functions, FunctionReturns checked.module function := by
  apply ordered_functions_return checked
  intro function member previous
  apply checked_function_returns_under_calls checked function member
  intro id called
  obtain ⟨callee, member, equal, returns⟩ := previous id called
  exact equal ▸ function_call_returns checked callee member returns

theorem checked_call_returns (checked : CheckedModule requireMain) (id : Nat)
    (present : id ∈ checked.module.functions.map Function.id) :
    CallReturns checked.module (signatures checked.module) id := by
  obtain ⟨function, member, equal⟩ := List.mem_map.mp present
  exact equal ▸ function_call_returns checked function member
    (checked_functions_total_and_typed checked function member)

/-- The checked main has no parameters and an exact Int result. Its body
terminates in the actual indexed evaluator without a fuel-success premise. -/
theorem checked_main_total (checked : CheckedModule true) :
    ∃ id function result,
      checked.module.main = some id ∧
      checked.module.functions.find? (fun function => function.id == id) = some function ∧
      Evaluates checked.module (fun _ => none) function.body (.integer result) := by
  have entry := checked.entry
  unfold MainValid at entry
  cases main : checked.module.main with
  | none => simp [main] at entry
  | some id =>
    simp only [main] at entry
    cases found : checked.module.functions.find? (fun function => function.id == id) with
    | none => simp [found] at entry
    | some function =>
      simp only [found] at entry
      obtain ⟨value, evaluated, typed⟩ := checked_functions_total_and_typed checked function
        (List.mem_of_find?_eq_some found) (fun _ => none) (fun _ => none)
        (by simp [ContextHasType, entry.1])
      rw [entry.2] at typed
      cases value <;> try exact False.elim typed
      case integer result => exact ⟨id, function, result, rfl, found, evaluated⟩

end VastitasOracle.IndexedProgramSafety
