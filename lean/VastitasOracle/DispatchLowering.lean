import VastitasKernel.DispatchChecker
import VastitasOracle.Dispatch
import VastitasOracle.ActivationSafety

/-! Finite target choices of the dispatch checker retain the real checker
equation and row equation, so their unique optimality is established by the
independently specified dispatch selection relation. The structural audit of
the old Core fixes the result of a Pair call to the selected signature.

This does not prove the Rust parser, source correspondence, or Lean/C/native
code generation. The public composition is in `IndexedDispatch` and
`IndexedAuthority`. -/
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
signature. No expected type or other candidate result participates. It does
not claim raw-lowering correspondence. -/
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

end VastitasOracle.DispatchLowering
