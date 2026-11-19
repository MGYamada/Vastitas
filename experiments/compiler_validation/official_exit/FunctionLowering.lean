import CompilerInputs

/-! Both compiler passes inspect the signed literal, its origin and all geometry references. -/
namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed FunctionSource
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

def intType : Indexed.Core.DataType := .pure .int
def compiledMain : Indexed.Core.Function := ⟨0,ExitFixture.owner,[],intType,
  .scope (.unary .neg (.integer 340282366920938463463374607431768211457) ⟨intType,none⟩),mainSpan⟩
def compiledModule : Indexed.Core.Module := ⟨accumulated,[compiledMain],some 0⟩
def functionPass : Compiler.Pass := {
  module := compiledModule,origins := #[⟨0,[]⟩],emittedCalls := [],
  calls := [],staticUses := [],references := (geometryNames.map (ref ·)).reverse,elaborationWork := 4}

attribute [local cbv_opaque] accumulated idx geometry

theorem checkedLower (audit : Bool) : Compiler.lowerPass readyCompiler audit = .ok functionPass := by
  cases audit <;> cbv
end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.checkedLower
