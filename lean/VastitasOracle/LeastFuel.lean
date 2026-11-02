/-! Mathlib-free constructive least-witness search. The existence certificate
stays in Prop; well-founded recursion uses it only to prove termination. -/
namespace VastitasOracle.LeastFuel

private def Later (p : Nat → Prop) (next current : Nat) : Prop :=
  next = current + 1 ∧ ¬ p current

private theorem accessible (p : Nat → Prop) (witness : ∃ n, p n) :
    Acc (Later p) 0 := by
  obtain ⟨n, hn⟩ := witness
  have visit : ∀ k, ∀ i, i + k = n → Acc (Later p) i := by
    intro k
    induction k with
    | zero =>
        intro i equal
        apply Acc.intro
        intro next step
        have same : i = n := by omega
        exact False.elim (step.2 (same ▸ hn))
    | succ k ih =>
        intro i equal
        apply Acc.intro
        intro next step
        exact ih next (by rcases step with ⟨rfl, _⟩; omega)
  exact visit n 0 (Nat.zero_add n)

private noncomputable def search (p : Nat → Prop) [DecidablePred p] (start : Nat)
    (access : Acc (Later p) start) :
    {n : Nat // p n ∧ start ≤ n ∧ ∀ k, start ≤ k → k < n → ¬ p k} := by
  induction access with
  | intro start _ ih =>
      by_cases h : p start
      · exact ⟨start, h, Nat.le_refl _, by omega⟩
      · let next := ih (start + 1) ⟨rfl, h⟩
        refine ⟨next.val, next.property.1, ?_, ?_⟩
        · have := next.property.2.1; omega
        · intro k lower upper
          by_cases same : k = start
          · simpa [same] using h
          · exact next.property.2.2 k (by omega) upper

/-- Specification-level Nat.find-style search, using Lean core accessibility
recursion, no choice and no Mathlib. No compiled implementation is asserted. -/
noncomputable def least (p : Nat → Prop) [DecidablePred p] (witness : ∃ n, p n) : Nat :=
  (search p 0 (accessible p witness)).val

theorem least_spec (p : Nat → Prop) [DecidablePred p] (witness : ∃ n, p n) :
    p (least p witness) := (search p 0 (accessible p witness)).property.1

theorem least_minimal (p : Nat → Prop) [DecidablePred p] (witness : ∃ n, p n)
    {n : Nat} (holds : p n) : least p witness ≤ n := by
  have minimal := (search p 0 (accessible p witness)).property.2.2
  by_cases lower : least p witness ≤ n
  · exact lower
  · exact False.elim (minimal n (Nat.zero_le _) (by unfold least at lower; omega) holds)

end VastitasOracle.LeastFuel
