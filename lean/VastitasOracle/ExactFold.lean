import VastitasKernel.MidIR.ExactFold
import VastitasOracle.IndexedEvaluation

set_option autoImplicit false

namespace VastitasOracle.ExactFold
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core.Semantics
open VastitasKernel.MidIR.ExactFold (Scalar Folded Bindings)
open IndexedEvaluation (Evaluates)

def scalarValue : Scalar → Value
  | .int n => .integer n
  | .nat n => .natural n

private theorem literal_evaluates (m : Core.Module) (env : Values) {t v}
    (h : MidIR.ExactFold.Literal t v) : Evaluates m env t (scalarValue v) := by
  induction h with
  | nat n => exact IndexedEvaluation.natural m env n
  | int l => cases l with
    | integer n => exact IndexedEvaluation.integer m env n
    | negated n => exact IndexedEvaluation.unary (IndexedEvaluation.integer m env n) rfl
  | ascribe _ ih => exact IndexedEvaluation.ascribe _ ih

/-- Exact literal comparisons have the same Boolean result in every caller,
including comparisons whose operands share a machine word or exit status. -/
theorem literal_comparison_evaluates (m : Core.Module) (env : Values)
    {op left right b} (r : Core.Result)
    (folded : MidIR.ExactFold.literalComparison op left right = some b) :
    Evaluates m env (.binary op left right r) (.boolean b) := by
  simp only [MidIR.ExactFold.literalComparison, bind, Option.bind_eq_some_iff] at folded
  obtain ⟨_, _, a, _, c, _, cmp⟩ := folded
  apply IndexedEvaluation.binary (literal_evaluates m env a.property) (literal_evaluates m env c.property)
  obtain ⟨a, _⟩ := a
  obtain ⟨c, _⟩ := c
  cases a <;> cases c <;> cases op <;> simp [Scalar.compare] at cmp <;> subst b <;> rfl

def bindings (ctx : Bindings) : Values := fun n => (ctx.lookup n).map scalarValue

private theorem bindings_cons (n : Nat) (x : Scalar) (ctx : Bindings) :
    bindings ((n,x)::ctx) = bindValue (bindings ctx) n (scalarValue x) := by
  funext k
  by_cases eq : k = n
  · subst k
    simp [bindings, bindValue]
  · have test : (k == n) = false := by simpa using eq
    simp [bindings, bindValue, List.lookup_cons, eq, test]

private theorem binary_sound {op : BinaryOp} {x y v : Scalar} (h : Scalar.binary op x y = some v) :
    evalBinary op (scalarValue x) (scalarValue y) = some (scalarValue v) := by
  cases x <;> cases y <;> cases op <;> simp [Scalar.binary] at h <;> subst v <;> rfl

/-- Induction over a successful fold gives an observation for every larger
fuel in the independent Core evaluator, including unused let initializers. -/
theorem evaluates (m : Core.Module) {ctx : Bindings} {t : Core.Term} {v : Scalar}
    (h : Folded ctx t v) : Evaluates m (bindings ctx) t (scalarValue v) := by
  induction h with
  | nat => exact IndexedEvaluation.natural ..
  | int => exact IndexedEvaluation.integer ..
  | var found => exact IndexedEvaluation.variable_value (by simp [bindings, found])
  | neg _ ih => exact IndexedEvaluation.unary ih rfl
  | binary _ _ operation left right => exact IndexedEvaluation.binary left right (binary_sound operation)
  | convert _ ih => exact IndexedEvaluation.natToInt ih
  | ascribe _ ih => exact IndexedEvaluation.ascribe _ ih
  | scope _ ih => exact IndexedEvaluation.scope ih
  | bind _ _ init body =>
    rw [bindings_cons] at body
    exact IndexedEvaluation.letE init body

end VastitasOracle.ExactFold
