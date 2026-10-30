import VastitasOracle.Coordinates
import VastitasOracle.AbstractTypes
import VastitasOracle.ModuleEffects

/-! Kernel-checked semantic edge cases for the Mathlib-free migration.
No native reflection or new axiom is used. -/
namespace VastitasOracle.CoreMigrationRegression
open VastitasKernel VastitasOracle.Coordinates VastitasOracle.AbstractTypes

-- Keep the rational type and signed integer embedding, not a float model.
example (n : Nat) (value : Int) (i : Fin n) :
    integerConstant n value i = (value : Rat) := rfl

example {left right : Int} (same : integerConstant 1 left = integerConstant 1 right) :
    left = right := integerConstant_injective 1 (by decide) same

-- The nonempty-dimension premise is essential: all empty coordinates coincide.
example : ¬ Function.Injective (integerConstant 0) := by
  intro injective
  have same : integerConstant 0 (0 : Int) = integerConstant 0 (1 : Int) := by
    funext i
    exact Fin.elim0 i
  have impossible : (0 : Int) = 1 := injective same
  contradiction

private def named (name : String) : RawAbstractType :=
  { name, parents := [], span := default }

-- Sorting preserves duplicate declarations and uses the same String order.
example : Abstract.canonicalNames [named "β", named "a", named "a"] =
    Abstract.builtins ++ ["a", "a", "β"] := by
  have sorted : (["a", "a", "β"] : List String).Pairwise
      (fun a b => decide (a ≤ b) = true) := by decide
  calc
    Abstract.canonicalNames [named "β", named "a", named "a"] =
        Abstract.canonicalNames [named "a", named "β", named "a"] :=
      canonical_names_permutation _ _ (List.Perm.swap _ _ _)
    _ = Abstract.canonicalNames [named "a", named "a", named "β"] :=
      canonical_names_permutation _ _ (List.Perm.cons _ (List.Perm.swap _ _ _))
    _ = Abstract.builtins ++ ["a", "a", "β"] := by
      simpa only [Abstract.canonicalNames, named, List.map_cons, List.map_nil] using
        congrArg (Abstract.builtins ++ ·) (List.mergeSort_of_pairwise sorted)

example : Abstract.canonicalNames [] = Abstract.builtins := by
  simp [Abstract.canonicalNames]

example : Abstract.canonicalNames [named "a", named "a"] ≠
    Abstract.canonicalNames [named "a"] := by
  intro same
  have lengths := congrArg List.length same
  simp [Abstract.canonicalNames] at lengths

example : Abstract.canonicalNames [named "β", named "a", named "a"] =
    Abstract.canonicalNames [named "a", named "β", named "a"] :=
  canonical_names_permutation _ _ (List.Perm.swap _ _ _)

open VastitasOracle.Elaboration

-- The replacement relation preserves equal length and positions, rather than
-- merely relating the sets of members (which would allow loss or reordering).
example {α β : Type} {relation : α → β → Prop} {values : List α} {results : List β}
    (related : Forall₂ relation values results) : values.length = results.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simpa using congrArg Nat.succ ih

example {values results : List Nat} : Forall₂ Eq values results ↔ values = results := by
  constructor
  · intro related
    induction related with
    | nil => rfl
    | cons same _ ih => cases same; cases ih; rfl
  · intro same
    subst results
    induction values with
    | nil => exact .nil
    | cons value values ih => exact .cons rfl ih

example : ¬ Forall₂ (fun (_ _ : Nat) => True) [1, 2] [1] := by
  intro related
  cases related with
  | cons _ tail => cases tail

example : ¬ Forall₂ Eq [1, 2] [2, 1] := by
  intro related
  cases related with
  | cons same _ => contradiction

end VastitasOracle.CoreMigrationRegression
