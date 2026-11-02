import VastitasKernel.ScalarFuel
import VastitasOracle.LeastFuel
import VastitasOracle.IndexedProgramSafety

/-! Universal terminal stability and least-fuel meaning for a finite, actually
checked scalar Core profile. No native, stateful or general CF claim is made. -/
namespace VastitasOracle.ScalarFuel
open VastitasKernel.Indexed.Core
open Semantics VastitasKernel.Indexed.Core.ScalarFuel

namespace Outcome
/-- Preserve *every* terminal outcome, including operational errors. -/
def Extends (before after : EvalOutcome α) : Prop :=
  before ≠ .outOfFuel → after = before

theorem refl (result : EvalOutcome α) : Extends result result := fun _ => rfl

theorem bind_extends {a a' : EvalOutcome α} {f g : α → EvalOutcome β}
    (ha : Extends a a') (hf : ∀ x, Extends (f x) (g x)) :
    Extends (a.bind f) (a'.bind g) := by
  cases a with
  | outOfFuel => simp [Extends, EvalOutcome.bind]
  | failure error =>
      have same := ha (by intro h; cases h)
      simp [same, Extends, EvalOutcome.bind]
  | success value =>
      have same := ha (by intro h; cases h)
      simpa [same, EvalOutcome.bind] using hf value

@[simp] theorem toOption_ofOption (error : Failure) (value : Option α) :
    (EvalOutcome.ofOption error value).toOption = value := by
  cases value <;> rfl

@[simp] theorem toOption_bind (result : EvalOutcome α) (next : α → EvalOutcome β) :
    (result.bind next).toOption = result.toOption.bind (fun x => (next x).toOption) := by
  cases result <;> rfl

theorem toOption_eq_some {result : EvalOutcome α} :
    result.toOption = some value ↔ result = .success value := by
  cases result <;> simp [EvalOutcome.toOption]

theorem success_value (result : EvalOutcome α) (successful : result.IsSuccess) :
    result = .success (result.value successful) := by
  cases result with
  | outOfFuel | failure _ => exact False.elim successful
  | success _ => rfl
end Outcome

/-- No typing or success hypothesis: errors are stable too, for all larger
fuel, the same environment and the same term. Unsupported forms are terminal
observer rejections, not claims about the semantics of those forms. -/
theorem evalFuel_extends (small large : Nat) (enough : small ≤ large)
    (values : Values) (term : Term) :
    Outcome.Extends (evalFuel small values term) (evalFuel large values term) := by
  induction small generalizing large values term with
  | zero => simp [evalFuel, Outcome.Extends]
  | succ small ih =>
      cases large with
      | zero => omega
      | succ large =>
          have step := ih large (by omega)
          cases term <;> simp only [evalFuel]
          all_goals first
            | exact Outcome.refl _
            | exact step _ _
            | apply Outcome.bind_extends (step _ _)
          all_goals intro value
          all_goals first
            | exact Outcome.refl _
            | exact step _ _
            | (apply Outcome.bind_extends (step _ _); intro other; exact Outcome.refl _)
            | (cases value <;> first | exact Outcome.refl _ | exact step _ _)

theorem evalFuel_terminal {small large : Nat} (enough : small ≤ large)
    (observed : evalFuel small values term = result) (terminal : result ≠ .outOfFuel) :
    evalFuel large values term = result := by
  have stable := evalFuel_extends small large enough values term
  rw [observed] at stable
  exact stable terminal

/-- The depth-fuel budget for actual Core `letE` sequencing. The second budget
may depend on the intermediate value/environment, and its terminal outcome may
be failure. This does not prove closure of accepted arrows under composition. -/
theorem letE_budget
    (first : evalFuel leftFuel values valueTerm = .success intermediate)
    (second : evalFuel rightFuel (bindValue values symbol intermediate) body = result)
    (terminal : result ≠ .outOfFuel)
    (enough : max leftFuel rightFuel + 1 ≤ fuel) :
    evalFuel fuel values (.letE symbol valueTerm body) = result := by
  have left := evalFuel_terminal (Nat.le_max_left leftFuel rightFuel) first
    (by intro impossible; cases impossible)
  have right := evalFuel_terminal (Nat.le_max_right leftFuel rightFuel) second terminal
  have combined : evalFuel (max leftFuel rightFuel + 1) values
      (.letE symbol valueTerm body) = result := by
    simp only [evalFuel, left, EvalOutcome.bind, right]
  exact evalFuel_terminal enough combined terminal

/-- Exact at *every* fuel; failures and exhaustion both erase to the old `none`.
The actual Core and existing primitive operations are retained. -/
theorem evalFuel_erases (module : Module) (fuel : Nat) (values : Values)
    (term : Term) (profile : supported term = true) :
    (evalFuel fuel values term).toOption = Semantics.eval module fuel values term := by
  induction fuel generalizing values term with
  | zero => rfl
  | succ fuel ih =>
      cases term <;> simp only [supported, Bool.and_eq_true] at profile
      all_goals try contradiction
      all_goals simp only [evalFuel, Semantics.eval]
      all_goals try simp only [Outcome.toOption_bind, Outcome.toOption_ofOption]
      all_goals first
        | rfl
        | exact ih _ _ profile
        | rw [ih _ _ profile]
        | rw [ih _ _ profile.1]
        | rw [ih _ _ profile.1.1]
      all_goals try simp only [Bind.bind, Pure.pure]
      all_goals first
        | rfl
        | (congr 1; funext value; rw [ih _ _ profile.2])
        | (congr 1; funext value; cases value <;> rfl)
        | (congr 1; funext value; exact ih _ _ profile.2)
        | (congr 1; funext value; cases value <;> try rfl
           rename_i choice
           cases choice
           · exact ih _ _ profile.2
           · exact ih _ _ profile.1.2)

end VastitasOracle.ScalarFuel
