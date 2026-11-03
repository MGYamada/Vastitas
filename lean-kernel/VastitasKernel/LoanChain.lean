import VastitasKernel.Distinct

/-! A finite child-to-root loan chain, reconstructed from the actual loan list.
Distinct names make each lookup the original list's first match. -/
namespace VastitasKernel.Finite.LoanChain

def adjacent (name : α → Nat) (parent : α → Option Nat) : List α → Bool
  | [] => true
  | first :: rest => parent first == rest.head?.map name && adjacent name parent rest

def check (name : α → Nat) (parent : α → Option Nat) (loans : List α) : Bool :=
  adjacent name parent loans && distinct (loans.map name)

def walk (parent : α → Option Nat) (lookup : Nat → Option α) : Nat → Nat → α → Bool
  | 0, _, _ => false
  | fuel + 1, key, loan => match parent loan with
    | none => false
    | some id => if key == id then true else
      match lookup id with
      | none => false
      | some next => walk parent lookup fuel key next

private theorem find_member (name : α → Nat) {loans : List α}
    (unique : (loans.map name).Nodup) {x : α} (member : x ∈ loans) :
    loans.find? (fun l => name l == name x) = some x := by
  induction loans with
  | nil => contradiction
  | cons first rest ih =>
    obtain ⟨fresh, unique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with same | later
    · subst x; simp
    · have ne : name first ≠ name x := fun equal =>
        fresh (List.mem_map.mpr ⟨x, later, equal.symm⟩)
      simp [ne, ih unique later]

private theorem adjacent_cons {name : α → Nat} {parent : α → Option Nat} {x rest}
    (h : adjacent name parent (x :: rest) = true) :
    parent x = rest.head?.map name ∧ adjacent name parent rest = true := by
  simpa only [adjacent, Bool.and_eq_true, beq_iff_eq] using h

/-- With first-match lookup established for each surviving loan, the bounded
parent walk sees exactly the indicated prefix of the suffix after the loan. -/
private theorem walk_tail (name : α → Nat) (parent : α → Option Nat) (lookup : Nat → Option α)
    (fuel key : Nat) (x : α) (rest : List α) (linked : adjacent name parent (x :: rest) = true)
    (found : ∀ y ∈ rest, lookup (name y) = some y) :
    walk parent lookup fuel key x = (rest.take fuel).any (fun y => key == name y) := by
  induction fuel generalizing x rest with
  | zero => simp [walk]
  | succ fuel ih =>
    have h := adjacent_cons linked
    cases rest with
    | nil => simp [walk, show parent x = none from h.1]
    | cons y ys =>
      have head : parent x = some (name y) := h.1
      have next := ih y ys h.2 (fun z hz => found z (List.mem_cons_of_mem y hz))
      simp only [walk, head, found y (by simp), List.take_succ_cons, List.any_cons]
      by_cases same : key = name y <;> simp [same, next]

private theorem suffix_comparable (name : α → Nat) (parent : α → Option Nat)
    (lookup : Nat → Option α) (fuel : Nat) (loans : List α)
    (linked : adjacent name parent loans = true) (bounded : loans.length ≤ fuel)
    (found : ∀ y ∈ loans, lookup (name y) = some y) :
    ∀ x ∈ loans, ∀ y ∈ loans, name x = name y ∨
      walk parent lookup fuel (name x) y = true ∨ walk parent lookup fuel (name y) x = true := by
  induction loans with
  | nil => simp
  | cons first rest ih =>
    have tailFound := fun y (hy : y ∈ rest) => found y (List.mem_cons_of_mem first hy)
    have bound : rest.length ≤ fuel := by simpa using Nat.le_trans (Nat.le_succ rest.length) bounded
    have reaches (y : α) (hy : y ∈ rest) : walk parent lookup fuel (name y) first = true := by
      rw [walk_tail name parent lookup fuel _ first rest linked tailFound, List.take_of_length_le bound]
      exact List.any_eq_true.mpr ⟨y, hy, by simp⟩
    intro x hx y hy
    rcases List.mem_cons.mp hx with headX | laterX
    · subst x
      rcases List.mem_cons.mp hy with headY | laterY
      · exact Or.inl (congrArg name headY.symm)
      · exact Or.inr (Or.inr (reaches y laterY))
    · rcases List.mem_cons.mp hy with headY | laterY
      · subst y
        exact Or.inr (Or.inl (reaches x laterX))
      · exact ih (adjacent_cons linked).2 bound tailFound x laterX y laterY

private theorem suffix_acyclic (name : α → Nat) (parent : α → Option Nat)
    (lookup : Nat → Option α) (fuel : Nat) (loans : List α)
    (linked : adjacent name parent loans = true) (unique : (loans.map name).Nodup)
    (found : ∀ y ∈ loans, lookup (name y) = some y) :
    ∀ child ∈ loans, ∀ id p, parent child = some id → lookup id = some p →
      walk parent lookup fuel (name child) p = false := by
  induction loans with
  | nil => simp
  | cons first rest ih =>
    have h := adjacent_cons linked
    obtain ⟨fresh, unique⟩ := List.nodup_cons.mp unique
    have tailFound := fun y (hy : y ∈ rest) => found y (List.mem_cons_of_mem first hy)
    intro child member id p edge resolved
    rcases List.mem_cons.mp member with rfl | later
    · cases rest with
      | nil => simp [h.1] at edge
      | cons next tail =>
        have sameId : id = name next := Option.some.inj (edge.symm.trans h.1)
        subst id
        have same : p = next := Option.some.inj (resolved.symm.trans (tailFound next (by simp)))
        subst p
        rw [walk_tail name parent lookup fuel _ next tail h.2 (fun z hz => tailFound z (by simp [hz]))]
        apply List.any_eq_false.mpr
        intro z hz
        have ne : name child ≠ name z := fun equal =>
          fresh (List.mem_map.mpr ⟨z, List.mem_cons_of_mem next (List.mem_of_mem_take hz), equal.symm⟩)
        simp [ne]
    · exact ih h.2 unique tailFound child later id p edge resolved

theorem comparable {name : α → Nat} {parent : α → Option Nat} {loans : List α}
    (checked : check name parent loans = true) {x y} (hx : x ∈ loans) (hy : y ∈ loans) :
    name x = name y ∨
      walk parent (fun id => loans.find? (fun l => name l == id)) loans.length (name x) y = true ∨
      walk parent (fun id => loans.find? (fun l => name l == id)) loans.length (name y) x = true := by
  have h : adjacent name parent loans = true ∧ distinct (loans.map name) = true := by
    simpa only [check, Bool.and_eq_true] using checked
  exact suffix_comparable name parent _ _ loans h.1 (Nat.le_refl _) (fun _ hmem =>
    find_member name ((distinct_iff _).mp h.2) hmem) x hx y hy

theorem acyclic {name : α → Nat} {parent : α → Option Nat} {loans : List α}
    (checked : check name parent loans = true) {child id p} (hc : child ∈ loans)
    (edge : parent child = some id) (resolved : loans.find? (fun l => name l == id) = some p)
    (fuel : Nat) :
    walk parent (fun id => loans.find? (fun l => name l == id)) fuel (name child) p = false := by
  have h : adjacent name parent loans = true ∧ distinct (loans.map name) = true := by
    simpa only [check, Bool.and_eq_true] using checked
  have unique := (distinct_iff _).mp h.2
  exact suffix_acyclic name parent _ fuel loans h.1 unique
    (fun _ hmem => find_member name unique hmem) child hc id p edge resolved

end VastitasKernel.Finite.LoanChain
