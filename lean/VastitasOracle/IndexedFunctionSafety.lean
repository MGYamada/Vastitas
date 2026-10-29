import VastitasOracle.IndexedEvaluationSafety

/-! Function-level consequences of the actual indexed Core audit. The callee
contracts are explicit until dependent argument transport discharges them. -/
namespace VastitasOracle.IndexedFunctionSafety
open VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics VastitasKernel.Indexed.Core.Typing
open VastitasOracle.IndexedSemantics VastitasOracle.IndexedWorld
open VastitasOracle.IndexedEvaluation VastitasOracle.IndexedEvaluationSafety

def FunctionReturns (module : Module) (function : Function) : Prop :=
  ∀ world values, ContextHasType module.declarations world values function.parameters →
    ∃ value, Evaluates module values function.body value ∧
      ValueHasType module.declarations world value function.returnType

/-- A checked function needs no freshness premise on the ambient world. Its
activation keeps precisely the parameter slots; the actual allocation audit
makes every body allocation fresh. The return-scope audit then permits dropping
those new slots while preserving the declared result and nominal endpoints. -/
theorem checked_function_returns_under_calls (checked : CheckedModule requireMain) (function : Function)
    (member : function ∈ checked.module.functions)
    (calls : ∀ id ∈ function.body.callIds, CallReturns checked.module (signatures checked.module) id) :
    FunctionReturns checked.module function := by
  intro world values context
  have functionTyped := checked.typed.functions function member
  have unique := function_slots_unique checked.typed member
  obtain ⟨activationTyped, activationFresh, _⟩ := checked_function_activation checked function member world values context
  obtain ⟨after, value, evaluated, typed, _, frame⟩ := evaluation_total_and_typed checked.typed.declarations calls
    functionTyped.2.1 activationTyped (List.nodup_append.mp unique).2.1 activationFresh
  refine ⟨value, evaluated, value_agreement ?_ (value_compatible functionTyped.2.2.2.1 typed.1)⟩
  intro ref inResult
  cases ref with
  | global _ => rfl
  | «local» type slot =>
    have inParameters := functionTyped.2.2.2.2 (.local type slot) inResult
    have slotMember := parameters_supported functionTyped.1 (.local type slot) inParameters slot rfl
    have absent : slot ∉ allocatedSerials checked.module.declarations function.body :=
      fun allocated => (List.nodup_append.mp unique).2.2 slot slotMember slot allocated rfl
    change world slot = after slot
    rw [frame slot absent]
    simp [restrictWorld, slotMember]

/-- In the call-free case the checked body has no outstanding semantic callee
premise. This includes arbitrary typed branches, primitives and nested package
openings, and still requires no ambient dynamic-freshness premise. -/
theorem checked_call_free_function_returns (checked : CheckedModule requireMain) (function : Function)
    (member : function ∈ checked.module.functions) (callFree : function.body.callIds = []) :
    FunctionReturns checked.module function :=
  checked_function_returns_under_calls checked function member (by simp [callFree])

end VastitasOracle.IndexedFunctionSafety
