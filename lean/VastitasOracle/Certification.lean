import VastitasKernel.Checker

/-!
The actual compiler's final audit supplies a proof in every successful result.
The audited predicate covers endpoint-base compatibility for every retained
type annotation and agreement of each function body with its result type. It
is deliberately not a claim of complete elaborator or native-code correctness.
-/
namespace VastitasOracle

open VastitasKernel

theorem certifyModule_sound (module : CheckedModule) (certified : CertifiedModule)
    (accepted : certifyModule module = .ok certified) :
    certified.val = module ∧ module.TypesWellFormed := by
  unfold certifyModule at accepted
  split at accepted
  · rename_i invariant
    cases accepted
    exact ⟨rfl, invariant⟩
  · contradiction

theorem checkModule_returns_type_certificate (raw : RawModule) (requireMain : Bool)
    (certified : CertifiedModule)
    (_accepted : checkModule raw requireMain = .ok certified) :
    certified.val.TypesWellFormed := certified.property

theorem accepted_function_result (certified : CertifiedModule) (function : CheckedFunction)
    (member : function ∈ certified.val.functions) :
    function.body.ty = function.returnType := (certified.property function member).1

theorem accepted_intermediate_type (certified : CertifiedModule) (function : CheckedFunction)
    (member : function ∈ certified.val.functions) (ty : Ty)
    (annotated : ty ∈ function.body.annotatedTypes) : ty.WellFormed := by
  apply (certified.property function member).2 ty
  simp [annotated]

end VastitasOracle
