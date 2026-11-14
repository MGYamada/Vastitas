set_option autoImplicit false

/-! Generic facts about `Except.bind` and `List.mapM` in the `Except` and
`Option` monads, which several oracle modules use. They mention no Vastitas
type, so this module imports no kernel module; core Lean has none of them. -/
namespace VastitasOracle.Support

universe u v w

section Except

variable {ε : Type u} {α : Type v} {β : Type w}

/-- A successful `Except.bind`: both steps succeed. -/
theorem bind_success {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action.bind next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error problem => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Every output of a successful `List.mapM` is the image of an input. -/
theorem mapM_ok_mem {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, accepted, y, member => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst accepted
    cases member
  | x :: xs, ys, accepted, y, member => by
    rw [List.mapM_cons] at accepted
    obtain ⟨head, first, accepted⟩ := bind_success accepted
    obtain ⟨tail, rest, accepted⟩ := bind_success accepted
    simp only [pure, Except.pure, Except.ok.injEq] at accepted
    subst accepted
    rcases List.mem_cons.mp member with equal | member
    · exact ⟨x, List.mem_cons_self, equal ▸ first⟩
    · obtain ⟨source, sourceMember, lowered⟩ := mapM_ok_mem rest y member
      exact ⟨source, List.mem_cons_of_mem _ sourceMember, lowered⟩

/-- Every input of a successful `List.mapM` has an output among the results. -/
theorem mapM_ok_of_mem {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ x ∈ xs, ∃ y ∈ ys, f x = .ok y
  | [], _, _, _, member => by cases member
  | x :: xs, ys, accepted, z, member => by
    rw [List.mapM_cons] at accepted
    obtain ⟨head, first, accepted⟩ := bind_success accepted
    obtain ⟨tail, rest, accepted⟩ := bind_success accepted
    simp only [pure, Except.pure, Except.ok.injEq] at accepted
    subst accepted
    rcases List.mem_cons.mp member with equal | member
    · subst equal
      exact ⟨head, List.mem_cons_self, first⟩
    · obtain ⟨result, belongs, lowered⟩ := mapM_ok_of_mem rest z member
      exact ⟨result, List.mem_cons_of_mem _ belongs, lowered⟩

/-- The output of a successful `List.mapM` at an index is the image of the
input at that index. -/
theorem mapM_ok_getElem? {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys →
      ∀ {index : Nat} {y : β}, ys[index]? = some y → ∃ x, xs[index]? = some x ∧ f x = .ok y
  | [], ys, accepted, _, _, selected => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst accepted
    simp at selected
  | x :: xs, ys, accepted, index, y, selected => by
    rw [List.mapM_cons] at accepted
    obtain ⟨head, first, accepted⟩ := bind_success accepted
    obtain ⟨tail, rest, accepted⟩ := bind_success accepted
    simp only [pure, Except.pure, Except.ok.injEq] at accepted
    subst accepted
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
      subst selected
      exact ⟨x, rfl, first⟩
    | succ index =>
      simp only [List.getElem?_cons_succ] at selected ⊢
      exact mapM_ok_getElem? rest selected

end Except

section Option

variable {α : Type u} {β : Type v}

/-- Every output of a successful `List.mapM` in `Option` is the image of an input. -/
theorem mapM_some_mem {f : α → Option β} : ∀ {as : List α} {bs : List β},
    as.mapM f = some bs → ∀ b ∈ bs, ∃ a ∈ as, f a = some b
  | [], bs, mapped, b, member => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at mapped
    subst mapped
    cases member
  | a :: as, bs, mapped, b, member => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at mapped
    obtain ⟨head, found, rest, mappedRest, rfl⟩ := mapped
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨a, List.mem_cons_self, found⟩
    · obtain ⟨a', member', found'⟩ := mapM_some_mem mappedRest b member
      exact ⟨a', List.mem_cons_of_mem a member', found'⟩

/-- A successful `List.mapM` in `Option` keeps the length and maps each index. -/
theorem mapM_some_index {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → r.length = l.length ∧ ∀ i : Nat, l[i]?.bind f = r[i]?
  | [], r, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases fa : f a with
    | none => simp [fa] at h
    | some b =>
      cases fl : l.mapM f with
      | none => simp [fa, fl] at h
      | some bs =>
        simp only [fa, fl, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        obtain ⟨length, each⟩ := mapM_some_index fl
        refine ⟨by simp [length], fun i => ?_⟩
        cases i with
        | zero => simp [fa]
        | succ i => simpa using each i

/-- The input of a successful `List.mapM` in `Option` at an index has its
output at the same index. -/
theorem mapM_some_getElem? {f : α → Option β} {as : List α} {bs : List β}
    (mapped : as.mapM f = some bs) {index : Nat} {a : α} (found : as[index]? = some a) :
    ∃ b, bs[index]? = some b ∧ f a = some b := by
  obtain ⟨length, each⟩ := mapM_some_index mapped
  have image := each index
  rw [found] at image
  change f a = bs[index]? at image
  cases image' : f a with
  | none =>
    rw [image'] at image
    obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp found
    have outside := List.getElem?_eq_none_iff.mp image.symm
    omega
  | some b => exact ⟨b, by rw [← image, image'], rfl⟩

end Option

end VastitasOracle.Support
