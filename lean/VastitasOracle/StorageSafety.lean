import VastitasOracle.StorageRegions
import VastitasKernel.StorageProtocol

/-! Safety facts extracted from the actual resource audit. They describe
logical allocations and byte footprints; they do not establish native allocator
liveness, actual writes, cleanup on runtime failure, or numerical correctness. -/
namespace VastitasOracle.StorageSafety
open VastitasKernel.Storage StorageRegions

theorem ancestor_child {loans : List Loan} {fuel name : Nat} {loan : Loan}
    (live : loan ∈ loans) (found : ancestor loans fuel name loan = true) :
    ∃ child ∈ loans, child.parent = some name := by
  induction fuel generalizing loan with
  | zero => simp [ancestor] at found
  | succ fuel ih =>
    simp only [ancestor] at found
    split at found
    · contradiction
    next parent parentLink =>
      split at found
      next equal =>
        have same : name = parent := by simpa only [beq_iff_eq] using equal
        exact ⟨loan, live, same.symm ▸ parentLink⟩
      next different =>
        split at found
        · contradiction
        next parentLoan lookup => exact ih (List.mem_of_find?_eq_some lookup) found

theorem active_not_ancestor {state : State} {name : Symbol} {loan : Loan} {fuel : Nat}
    (live : loan ∈ state.loans) (active : state.suspended name = false) :
    ancestor state.loans fuel name loan = false := by
  apply Bool.eq_false_iff.mpr
  intro found
  obtain ⟨child, childLive, parent⟩ := ancestor_child live found
  have member : child ∈ state.children name := List.mem_filter.mpr ⟨childLive, by simp [parent]⟩
  have empty : state.children name = [] := by simpa [State.suspended] using active
  simp [empty] at member

/-- Two distinct active loans to the same allocation cannot access the same
byte when either writes. Suspended ancestor permissions are explicitly removed
before interpreting the pairwise compatibility audit. -/
theorem active_loans_disjoint {state : State} {left right : Loan} {allocation : Allocation}
    (audited : auditState state = true)
    (leftLive : left ∈ state.loans) (rightLive : right ∈ state.loans)
    (different : left.name ≠ right.name)
    (sameAllocation : left.allocation = right.allocation)
    (lookup : state.allocation? left.allocation = some allocation)
    (leftActive : state.suspended left.name = false) (rightActive : state.suspended right.name = false)
    (writes : left.access.writes = true ∨ right.access.writes = true)
    {byte : Nat} (first : ContainsByte left.layout allocation.scalar byte) :
    ¬ ContainsByte right.layout allocation.scalar byte := by
  have pairs : state.loans.all (fun l => state.loans.all (loansCompatible state l)) = true := by
    simp only [auditState, Bool.and_eq_true] at audited
    exact audited.2
  have compatible := List.all_eq_true.mp (List.all_eq_true.mp pairs left leftLive) right rightLive
  have notLeft := active_not_ancestor (fuel := state.loans.length) rightLive leftActive
  have notRight := active_not_ancestor (fuel := state.loans.length) leftLive rightActive
  have rightLookup : state.allocation? right.allocation = some allocation := sameAllocation ▸ lookup
  have disjoint : left.layout.disjoint right.layout allocation.scalar = true := by
    rcases writes with leftWrites | rightWrites <;>
      simpa [loansCompatible, different, sameAllocation, notLeft, notRight, rightLookup, *] using compatible
  exact disjoint_bytes disjoint first

/-- Read permissions in an audited environment entail initialized actual bytes
in its logical write history, including reads through a transpose. -/
theorem read_initialization {state : State} {loan : Loan} {allocation : Allocation}
    (audited : auditState state = true) (live : loan ∈ state.loans)
    (lookup : state.allocation? loan.allocation = some allocation)
    (reads : loan.access.reads = true) {byte : Nat}
    (inside : ContainsByte loan.layout allocation.scalar byte) :
    Initialized allocation.scalar byte allocation.initialization := by
  have loans : state.loans.all (fun l => state.loans.countP (·.name == l.name) == 1 && l.valid state) = true := by
    simp only [auditState, Bool.and_eq_true] at audited
    exact audited.1.2
  have valid : loan.valid state = true := by
    have both := List.all_eq_true.mp loans loan live
    simp only [Bool.and_eq_true] at both
    exact both.2
  have covered : allocation.initialization.covers allocation.scalar loan.layout = true := by
    simp only [Loan.valid, lookup, reads, Bool.not_true, Bool.false_or, Bool.and_eq_true] at valid
    exact valid.1.2
  exact initialization_bytes covered inside

theorem action_audits {state after : State} {action : Action}
    (accepted : checkAction state action = .ok after) : auditState state = true ∧ auditState after = true := by
  cases before : auditState state with
  | false => simp [checkAction, before] at accepted
  | true =>
    cases operation : executeAction state action with
    | error diagnostic => simp [checkAction, before, operation] at accepted
    | ok result =>
      cases next : auditState result with
      | false => simp [checkAction, before, operation, next] at accepted
      | true =>
        simp [checkAction, before, operation, next] at accepted
        subst after
        exact ⟨rfl, next⟩

/-- The decoder certificate keeps acceptance tied to these exact statements;
there is no alternate serialized checked state or trusted initialization flag. -/
theorem decoded_plan {json : Lean.Json} (checked : Wire.CheckedInput json) :
    Wire.plan json = .ok checked.input ∧
    run 4096 {} checked.input = .ok checked.checked.finalState ∧
    auditState checked.checked.finalState = true ∧
    checked.checked.finalState.allocations = [] ∧ checked.checked.finalState.loans = [] :=
  ⟨checked.decoded, checked.checked.accepted, checked.checked.valid, checked.checked.closed⟩

end VastitasOracle.StorageSafety
