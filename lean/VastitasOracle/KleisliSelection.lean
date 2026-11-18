import VastitasOracle.FiniteHom

/-! The nominal path from an accepted Kleisli view to the one Monad whose laws
supply its operations. All three referenced declarations are actual members
of the same checked environment. -/
namespace VastitasOracle.KleisliSelection
open VastitasKernel VastitasKernel.Indexed
open VastitasOracle.FiniteCategoryExecution (lookup_of_view lookup_member)

theorem member_lookup {env : Environment} {e : Entry}
    (unique : (env.map Entry.id).Nodup) (member : e ∈ env) :
    lookup env e.id = some e.declaration := by
  induction env with
  | nil => simp at member
  | cons x xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | present
    · simp [lookup]
    · have different : x.id ≠ e.id := by
        intro same
        exact fresh (same ▸ List.mem_map_of_mem present)
      simpa [lookup, different] using ih tail present

theorem of_member {env : Environment} (good : env.Valid)
    (member : ⟨owner, .finiteKleisli kind schema monad⟩ ∈ env) :
    KleisliViews.selected (FiniteCategories.view env) kind owner = some monad ∧
    ∃ base fields, ⟨schema, .kleisliSchema kind base⟩ ∈ env ∧ ⟨base, .monadSchema⟩ ∈ env ∧
      ⟨monad, .finiteMonad base fields⟩ ∈ env := by
  have admitted := good.declarations _ member
  change KleisliViews.valid (FiniteCategories.view env) kind schema monad = true at admitted
  have self := member_lookup good.unique member
  change lookup env owner = some (.finiteKleisli kind schema monad) at self
  have named : FiniteCategories.view env owner = some (.finiteKleisli kind schema monad) := by
    simp [FiniteCategories.view, self]
  refine ⟨by simp [KleisliViews.selected, named, admitted, guard], ?_⟩
  unfold KleisliViews.valid at admitted
  split at admitted
  · rename_i schemaKind base monadSchema fields schemaFound monadFound
    obtain ⟨⟨rfl,rfl⟩, baseFound⟩ := (by
      simpa only [Bool.and_eq_true, beq_iff_eq, KleisliViews.validSchema] using admitted :
        (schemaKind = kind ∧ monadSchema = base) ∧ FiniteCategories.view env base = some .monadSchema)
    exact ⟨_, _, lookup_member (lookup_of_view schemaFound), lookup_member (lookup_of_view baseFound),
      lookup_member (lookup_of_view monadFound)⟩
  · contradiction

end VastitasOracle.KleisliSelection
