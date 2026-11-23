import VastitasKernel.ExactOperators
import VastitasKernel.IndexedTypeAudit

set_option autoImplicit false

namespace VastitasKernel.Indexed.ExactOperators

/-- Every exact arithmetic operation in a well-typed Core term selects
one method of its canonical family, with the same result type as Core. -/
theorem typed_operator_method {env : Core.Declarations} {functions : Core.Typing.Signatures}
    {ctx : Core.Typing.Context} {t : Core.Term} {s : Selection}
    (typed : Core.Typing.HasType env functions ctx t) (site : selection? t = some s) :
    ∃ ordinal, candidates s = [(ordinal, t.result.type)] := by
  cases t <;> try (simp [selection?] at site)
  case unary op a result =>
    cases op <;> simp at site
    subst s
    rw [Core.Typing.HasType.eq_def] at typed
    obtain ⟨ha, hr⟩ := typed.2.2
    change ∃ ordinal, candidates ⟨_, [a.result.type]⟩ = [(ordinal, result.type)]
    rw [ha, hr]
    exact ⟨0, rfl⟩
  case binary op a b result =>
    cases op <;> simp at site
    all_goals subst s
    all_goals
      rw [Core.Typing.HasType.eq_def] at typed
      have types := typed.2.2.2
      change ∃ ordinal, candidates ⟨_, [a.result.type, b.result.type]⟩ = [(ordinal, result.type)]
    all_goals first
      | (obtain ⟨same, h | h, out⟩ := types <;> rw [out, ← same, h] <;> exact ⟨_, rfl⟩)
      | (rcases types with h | h | h | h <;> obtain ⟨left, right, out⟩ := h <;>
         rw [left, right, out] <;> exact ⟨_, rfl⟩)

private def Resolved (sites : List Selection) : Prop :=
  ∀ s ∈ sites, ∃ ordinal result, candidates s = [(ordinal, result)]

private theorem no_sites : Resolved [] := fun _ h => by simp at h

private theorem joined {xs ys} (a : Resolved xs) (b : Resolved ys) : Resolved (xs ++ ys) :=
  fun s member => (List.mem_append.mp member).elim (a s) (b s)

private theorem node {env functions ctx t} {children : List Selection}
    (typed : Core.Typing.HasType env functions ctx t) (rest : Resolved children) :
    Resolved ((selection? t).toList ++ children) := by
  apply joined _ rest
  intro s member
  have h : selection? t = some s := by
    cases e : selection? t <;> simp_all
  obtain ⟨i, single⟩ := typed_operator_method typed h
  exact ⟨i, t.result.type, single⟩

private theorem all_sites {env functions ctx} {t : Core.Term}
    (typed : Core.Typing.HasType env functions ctx t) : Resolved (collect t) := by
  induction t using Core.Term.rec (motive_2 := fun ts =>
      ∀ {ctx}, Core.Typing.ArgsTyped env functions ctx ts → Resolved (ts.flatMap collect)) generalizing ctx
  case nil => exact no_sites
  case cons t ts head tail ctx typed =>
    rw [Core.Typing.ArgsTyped.eq_def] at typed
    exact joined (head typed.1) (tail typed.2)
  all_goals rw [collect]; apply node typed; rw [Core.Typing.HasType.eq_def] at typed
  all_goals try exact no_sites
  case unary _ _ _ ih => exact ih typed.2.1
  case project _ _ _ ih => exact ih typed.2.1
  case scope _ ih => exact ih typed.2.1
  case ascribe _ _ ih => exact ih typed.2.1
  case natToInt _ ih => exact ih typed.2.1
  case binary _ _ _ _ l r => exact joined (l typed.2.1) (r typed.2.2.1)
  case pair _ _ _ l r => exact joined (l typed.2.1) (r typed.2.2.1)
  case letE _ _ _ v b => exact joined (v typed.2.1) (b typed.2.2.2)
  case call _ _ _ _ ih => exact ih typed.2.1
  case primitive _ _ _ ih => exact ih typed.2.1
  case branch _ _ _ _ c y n => exact joined (joined (c typed.2.1) (y typed.2.2.2.1)) (n typed.2.2.2.2.1)
  case pack _ _ _ w fs => exact joined (w typed.2.1) (fs typed.2.2.1)
  case unpack _ _ p b hp hb =>
    apply joined (hp typed.2.1)
    have inner := typed.2.2.2.2.2
    split at inner <;> try contradiction
    split at inner <;> try contradiction
    exact hb inner.2.1


/-- Every operator reported by an accepted Core module resolves to exactly one
protected method in its defining family. The key includes the operand order. -/
theorem module_method {m : Core.Module} (typed : Core.Typing.ModuleTyped m) (site : Nat × Selection)
    (member : site ∈ selections m) : ∃ ordinal result, candidates site.2 = [(ordinal, result)] := by
  obtain ⟨f, hf, mapped⟩ := List.mem_flatMap.mp member
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp mapped
  exact all_sites (typed.functions f hf).2.1 s hs

/-- The head is total because the checked module supplies a unique method.
Its ordinal is relative to its own family's immutable method list. -/
def methodAt {m : Core.Module} (typed : Core.Typing.ModuleTyped m) (site : Nat × Selection)
    (member : site ∈ selections m) : Nat × Core.DataType :=
  (candidates site.2).head (by
    obtain ⟨i, t, same⟩ := module_method typed site member
    simp [same])

theorem methodAt_sole {m : Core.Module} (typed : Core.Typing.ModuleTyped m) (site : Nat × Selection)
    (member : site ∈ selections m) : candidates site.2 = [methodAt typed site member] := by
  obtain ⟨i, t, same⟩ := module_method typed site member
  simp [methodAt, same]

end VastitasKernel.Indexed.ExactOperators
