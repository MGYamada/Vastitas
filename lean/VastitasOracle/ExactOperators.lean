import VastitasKernel.OperatorProfile
import VastitasKernel.ExactOperators

set_option autoImplicit false

namespace VastitasOracle.ExactOperators

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Typing
open VastitasKernel.Indexed.ExactOperators (Selection selection?)

/-- Filter the actual protected package by receipt owner and operand key.
The result type plays no part in this selection. -/
def methodResults (s : Selection) : List DataType :=
  let pkg := OperatorProfile.package [s.family.owner.name]
  pkg.modules.flatMap fun m =>
    if s.family.owner.scope == ⟨pkg.id, m.module.path⟩ then
      m.methods.filterMap fun method =>
        if method.target.path == [s.family.owner.name] &&
            method.params.map (·.ty) == s.scalarKey.map (fun n => Surface.TypeExpr.data (.named n)) then
          some (.pure method.result)
        else none
    else []

/-- For every checked arithmetic instruction, its receipt identifies exactly
one method of the protected family at the actual operand types. The result
is checked as a consequence of Core typing, never used to select a key. -/
theorem selection_in_profile {env : Declarations} {sigs : Signatures} {ctx : Context}
    (t : Core.Term) (s : Selection) (typed : HasType env sigs ctx t) (selected : selection? t = some s) :
    methodResults s = [t.result.type] := by
  cases t <;> try (solve | cases selected)
  case unary op arg result =>
    cases op <;> simp [selection?] at selected
    subst s
    obtain ⟨ha, hr⟩ := typed.2.2
    change methodResults _ = [result.type]
    rw [ha, hr]
    decide
  case binary op a b result =>
    have operand := typed.2.2.2
    cases op <;> simp [selection?] at selected <;> subst s
    all_goals change methodResults _ = [result.type]
    case div =>
      rcases operand with ⟨ha, hb, hr⟩ | ⟨ha, hb, hr⟩ | ⟨ha, hb, hr⟩ | ⟨ha, hb, hr⟩ <;>
        rw [ha, hb, hr] <;> decide
    all_goals
      obtain ⟨eq, ha, hr⟩ := operand
      rcases ha with ha | ha <;> rw [← eq, hr, ha] <;> decide

end VastitasOracle.ExactOperators
