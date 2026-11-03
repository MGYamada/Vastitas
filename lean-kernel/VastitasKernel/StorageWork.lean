import VastitasKernel.Limits
import VastitasKernel.LoanChain

/-! Deterministic admission units for resource checking. A unit counts metadata
visits or comparisons; no clock, byte payload or floating-point result is an input. -/
namespace VastitasKernel.Storage.Work

abbrev Total := Fin (Limits.resourceWork + 1)

def zero : Total := ⟨0, Nat.zero_lt_succ _⟩

def add (used : Total) (amount : Nat) : Option Total :=
  let next := used.val + amount
  if h : next < Limits.resourceWork + 1 then some ⟨next, h⟩ else none

theorem add_exact {used next : Total} {amount : Nat} (ok : add used amount = some next) :
    next.val = used.val + amount ∧ next.val ≤ Limits.resourceWork := by
  unfold add at ok
  dsimp only at ok
  split at ok
  · cases ok
    exact ⟨rfl, by omega⟩
  · contradiction

private def loanCounts (parent : α → Option Nat) (writes : α → Bool) :
    List α → Nat → Nat → Nat → Nat × Nat × Nat
  | [], count, writers, children => (count, writers, children)
  | loan :: rest, count, writers, children =>
    loanCounts parent writes rest (count + 1) (writers + (writes loan).toNat)
      (children + (parent loan).isSome.toNat)

/-- The general audit compares every writer with live loans in both directions.
A parent walk is bounded by the live count. Flat loans have no such walk, and
the proved single-chain path skips pair comparisons and general ancestry. -/
def frame (names allocations regions dependencies : Nat) (loans : List α)
    (name : α → Nat) (parent : α → Option Nat) (writes : α → Bool) : Nat :=
  let (count, writers, children) := loanCounts parent writes loans 0 0 0
  let base := 1 + names + allocations + regions * (1 + count) + dependencies + count
  if count < 2 || (writers == 0 && children == 0) || Finite.LoanChain.check name parent loans then base
  else base + count * (2 * writers + children)

/-- Sum the costs of completed probes as they return. A failed debit stops
before the next probe. The resulting list is the unmodified all-body map. -/
def collect (check : α → Except ε β) (cost : β → Nat) (exhausted : ε) :
    List α → Total → Except ε (List β × Total)
  | [], used => .ok ([], used)
  | first :: rest, used => do
    let item ← check first
    let some next := add used (cost item) | throw exhausted
    let (items, final) ← collect check cost exhausted rest next
    return (item :: items, final)

theorem collect_exact {check : α → Except ε β} {cost : β → Nat} {exhausted : ε}
    {inputs : List α} {used final : Total} {items : List β}
    (ok : collect check cost exhausted inputs used = .ok (items, final)) :
    inputs.mapM check = .ok items ∧ final.val = used.val + (items.map cost).sum := by
  induction inputs generalizing used items with
  | nil =>
    simp only [collect, Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨rfl, rfl⟩ := ok
    exact ⟨rfl, by simp⟩
  | cons first rest ih =>
    cases firstResult : check first with
    | error e => simp [collect, firstResult, bind, Except.bind] at ok
    | ok item =>
      cases debit : add used (cost item) with
      | none => simp [collect, firstResult, debit, bind, Except.bind, throw] at ok
      | some next =>
        cases tailResult : collect check cost exhausted rest next with
        | error e => simp [collect, firstResult, debit, tailResult, bind, Except.bind] at ok
        | ok pair =>
          rcases pair with ⟨tail, remaining⟩
          simp [collect, firstResult, debit, tailResult, bind, Except.bind, pure, Except.pure] at ok
          obtain ⟨rfl, rfl⟩ := ok
          obtain ⟨mapped, total⟩ := ih tailResult
          refine ⟨?_, ?_⟩
          · simp [List.mapM_cons, firstResult, mapped, bind, Except.bind, pure, Except.pure]
          · have step := (add_exact debit).1
            simp only [List.map_cons, List.sum_cons]
            omega

end VastitasKernel.Storage.Work
