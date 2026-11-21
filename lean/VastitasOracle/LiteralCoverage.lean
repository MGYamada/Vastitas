import VastitasKernel.MidIR.Lower
import VastitasOracle.MidIR

set_option autoImplicit false

namespace VastitasOracle.MidIR
open VastitasKernel VastitasKernel.Indexed VastitasKernel.MidIR
open VastitasKernel.Indexed.Core.Semantics

/-- The exact Core literal emits a nullary SSA opcode. Both phases give the
Core value for any call resolver and store, and reject an unexpected operand. -/
theorem literal_constructor_coverage (module : Core.Module) (values : Values) (fuel : Nat)
    (lit : Literal) (resolver : Resolver) (unexpected : Value) (rest : List Value) :
    AppendsLiteral lit ∧ lit.registryRow ∈ literalRegistry ∧
    (lit.opcode .optimization).execute module.declarations.indexed = some (lit.opcode .execution) ∧
    ∀ phase, let op := lit.opcode phase
      op.valid module.declarations.indexed = true ∧ op.operands = [] ∧
      Ty.ofCore lit.term.result.type = some op.result ∧
      denote module.declarations.indexed op [] resolver = eval module (fuel + 1) values lit.term ∧
      denote module.declarations.indexed op (unexpected :: rest) resolver = none := by
  refine ⟨appends_literal lit, lit.registered, ?_, ?_⟩
  · cases lit <;> rfl
  · intro phase
    cases lit <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end VastitasOracle.MidIR
