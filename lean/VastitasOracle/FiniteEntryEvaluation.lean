import VastitasKernel.LLVM.FiniteCost
import VastitasOracle.IndexedEvaluation

set_option autoImplicit false

namespace VastitasOracle.FiniteEntryEvaluation
open VastitasKernel.Indexed VastitasKernel.Indexed.Core VastitasKernel.Indexed.Core.Semantics
open VastitasKernel.LLVM

private def Extends {α : Type} (x y : Option α) : Prop := ∀ v, x = some v → y = some v

private theorem same {α : Type} (x : Option α) : Extends x x := fun _ h => h

private theorem bind_extends {α β : Type} {a b : Option α} {f g : α → Option β}
    (ab : Extends a b) (fg : ∀ x, Extends (f x) (g x)) :
    Extends (a >>= f) (b >>= g) := by
  intro v h
  obtain ⟨x,found,res⟩ := Option.bind_eq_some_iff.mp h
  exact Option.bind_eq_some_iff.mpr ⟨x,ab _ found,fg _ _ res⟩

private theorem map_extends {α β : Type} (xs : List α) {f g : α → Option β}
    (fg : ∀ x, Extends (f x) (g x)) : Extends (xs.mapM f) (xs.mapM g) := by
  induction xs with
  | nil => exact same _
  | cons x xs ih =>
    simp only [List.mapM_cons]
    apply bind_extends (fg x)
    intro _
    apply bind_extends ih
    intro _
    exact same _

/-- A successful evaluation at one fuel remains the same at higher fuel,
including calls that enter the actual callee's own parameter environment. -/
private theorem one_step (m : Module) (k : Nat) :
    ∀ (rho : Values) (t : Term), Extends (eval m k rho t) (eval m (k+1) rho t) := by
  induction k with
  | zero => intro _ _ _ h; simp [eval] at h
  | succ k ih =>
    intro rho t
    cases t <;> (conv => lhs; unfold eval) <;> (conv => rhs; unfold eval) <;>
      repeat' first
      | exact same _
      | exact ih _ _
      | apply map_extends
      | apply bind_extends
      | split
      | intro x

theorem stable {m : Module} {k : Nat} {rho : Values} {t : Term} {value : Value}
    (observed : eval m k rho t = some value) :
    IndexedEvaluation.Evaluates m rho t value := by
  refine ⟨k, fun n le => ?_⟩
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le le
  clear le
  induction d with
  | zero => exact observed
  | succ d ih => exact one_step m (k+d) rho t _ ih

theorem entry_stable (m : Module) (r : FiniteCost.Observation m) (fuel : Nat)
    (enough : r.fuel ≤ fuel) : FiniteCost.coreEntry m fuel = some (.integer r.value) := by
  have h := r.evaluated
  simp only [FiniteCost.coreEntry, bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨id, entry, f, found, args, bound, result⟩ := h
  refine ⟨id,entry,f,found,args,bound,?_⟩
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le enough
  clear enough
  induction d with
  | zero => exact result
  | succ d ih => exact one_step m (r.fuel+d) args f.body _ ih

end VastitasOracle.FiniteEntryEvaluation
