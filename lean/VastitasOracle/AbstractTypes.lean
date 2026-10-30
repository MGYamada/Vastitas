import VastitasKernel.Abstract
import VastitasOracle.DispatchLowering
import Init.Data.List.Sort.Lemmas

/-! The actual finite hierarchy construction and the evidence retained by its
validator. No geometry, inhabitants beyond the four scalars, or value coercions
are asserted by these declarations. -/
namespace VastitasOracle.AbstractTypes
open VastitasKernel VastitasKernel.Abstract

theorem accepted_hierarchy_valid (checked : Abstract.Checked) :
    Dispatch.hierarchyValid checked.hierarchy = true := checked.valid

theorem accepted_builtin_relations (checked : Abstract.Checked) :
    preservesBuiltins checked.hierarchy = true := checked.preserved

theorem accepted_concrete_values (checked : Abstract.Checked) :
    checked.hierarchy.concrete = [0, 1, 2, 3] := checked.concrete

theorem accepted_capability_facts (checked : Abstract.Checked) :
    checked.hierarchy.facts = Dispatch.publicHierarchy.facts := checked.facts

theorem canonical_names_permutation (left right : List RawAbstractType)
    (permutation : left.Perm right) : canonicalNames left = canonicalNames right := by
  unfold canonicalNames
  congr 1
  have sorted (names : List String) :
      (names.mergeSort (· ≤ ·)).Pairwise (fun a b => a ≤ b) := by
    simpa only [decide_eq_true_eq] using
      (List.pairwise_mergeSort (le := fun a b : String => decide (a ≤ b))
        (fun a b c ab bc => by
          have ab' : a ≤ b := by simpa using ab
          have bc' : b ≤ c := by simpa using bc
          simpa using Std.le_trans ab' bc')
        (fun a b => by simpa using (Std.le_total : a ≤ b ∨ b ≤ a)) names)
  apply List.Perm.eq_of_pairwise (le := fun a b : String => a ≤ b)
    (fun _ _ _ _ ab ba => Std.le_antisymm ab ba)
    (sorted _) (sorted _)
  exact (List.mergeSort_perm _ _).trans ((permutation.map (·.name)).trans
    (List.mergeSort_perm _ _).symm)

theorem hierarchy_edges_permutation (names : List String) (left right : List (Nat × Nat))
    (permutation : left.Perm right) : hierarchy names left = hierarchy names right := by
  have edges : ∀ edge, left.contains edge = right.contains edge := fun _ => permutation.contains_eq
  simp only [hierarchy, edges]

/-- Declaration and membership order do not alter the actual hierarchy passed
into checkWith. Duplicate/cyclic/unauthorized inputs are separately rejected. -/
theorem build_order_independent (left right : List RawAbstractType)
    (members₁ members₂ : List RawSubtype) (declarations : left.Perm right)
    (memberships : members₁.Perm members₂) : build left members₁ = build right members₂ := by
  unfold build
  rw [canonical_names_permutation left right declarations]
  apply hierarchy_edges_permutation
  apply List.Perm.append
  · exact List.Perm.flatMap_right _ declarations
  · exact memberships.map _

/-- The selected method is optimal in the validated nominal hierarchy, rather
than in the current inhabitant sets of its selectors. -/
theorem selected_nominal_target (family : DispatchChecker.Family) (key : Dispatch.Key)
    (target : DispatchChecker.Target family key) :
    Dispatch.Selection family.nominals.hierarchy family.checked.methods key (some target.method) :=
  (DispatchLowering.selected_target_sound family key target).2

end VastitasOracle.AbstractTypes
