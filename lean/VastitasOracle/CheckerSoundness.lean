import VastitasKernel.TypeAudit
import VastitasKernel.Checker

/-!
Soundness of independent validation of the actual checked language. The typing
judgment does not mention checker execution. Successful validation establishes
all its rules, including intermediate terms, dependent argument substitution,
scoped parameters, and distinct generative brands.
-/
namespace VastitasOracle.CheckerSoundness
open VastitasKernel VastitasKernel.Typing

/-- The hash-set implementation validates mathematical list distinctness. -/
theorem distinctFrom_sound {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (seen : Std.HashSet α) (items : List α)
    (accepted : distinctFrom seen items = true) :
    items.Nodup ∧ ∀ value ∈ items, value ∉ seen :=
  (Finite.distinctFrom_iff seen items).mp accepted

/-- Every actual function body has a derivation of the independent rules. -/
theorem auditBodies_sound (module : CheckedModule) (accepted : auditBodies module = true) :
    ∀ function ∈ module.functions,
      FunctionWellTyped (moduleSignatures module) function := by
  simpa [auditBodies] using accepted

/-- Full typing and freshness follow from the executable checked-term audit. -/
theorem auditModule_sound (module : CheckedModule) (accepted : auditModule module = true) :
    ModuleWellTyped module := by
  simp only [auditModule, Bool.and_eq_true] at accepted
  exact ⟨(distinctFrom_sound _ _ accepted.1.1).1,
    (distinctFrom_sound _ _ accepted.1.2).1, auditBodies_sound module accepted.2⟩

end VastitasOracle.CheckerSoundness
