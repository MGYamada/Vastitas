import VastitasKernel.StorageCodegen
import VastitasOracle.StorageSafety

/-! Exact reconstruction at the resource code-generation boundary. These facts
do not model the C heap, IO failures, emitted Lean text or native execution. -/
namespace VastitasOracle.StorageCodegen
attribute [local simp] Except.bind Except.map Except.pure
attribute [local simp] bind pure Functor.map
open VastitasKernel.Storage

/-- Every successful lowering follows the actual checker state transitions,
including both branch arms and their distinct allocation counters. -/
theorem lowered_state {fuel : Nat} {state after : State} {input : List Statement}
    {instructions : List Native.Instruction}
    (accepted : Native.lower fuel state input = .ok (after, instructions)) :
    run fuel state input = .ok after := by
  induction fuel generalizing state after input instructions with
  | zero =>
    cases input with
    | nil => simpa [Native.lower, run] using congrArg (Except.map Prod.fst) accepted
    | cons first rest => simp [Native.lower] at accepted
  | succ fuel ih =>
    cases input with
    | nil => simpa [Native.lower, run] using congrArg (Except.map Prod.fst) accepted
    | cons first rest =>
      cases first with
      | action operation =>
        cases step : checkAction state operation with
        | error diagnostic => simp [Native.lower, step] at accepted
        | ok intermediate =>
          cases emitted : Native.action state operation with
          | error diagnostic => simp [Native.lower, step, emitted] at accepted
          | ok code =>
            cases tail : Native.lower fuel intermediate rest with
            | error diagnostic => simp [Native.lower, step, emitted, tail] at accepted
            | ok result =>
              rcases result with ⟨last, more⟩
              have equal : last = after := by
                simpa [Native.lower, step, emitted, tail] using
                  (congrArg (Except.map Prod.fst) accepted)
              simpa [run, step, equal] using ih tail
      | branch condition yes no =>
        cases left : Native.lower fuel state yes with
        | error diagnostic => simp [Native.lower, left] at accepted
        | ok leftResult =>
          rcases leftResult with ⟨leftState, leftCode⟩
          cases right : Native.lower fuel {state with nextAllocation := leftState.nextAllocation} no with
          | error diagnostic => simp [Native.lower, left, right] at accepted
          | ok rightResult =>
            rcases rightResult with ⟨rightState, rightCode⟩
            cases joined : join leftState rightState with
            | error diagnostic => simp [Native.lower, left, right, joined] at accepted
            | ok intermediate =>
              cases tail : Native.lower fuel intermediate rest with
              | error diagnostic => simp [Native.lower, left, right, joined, tail] at accepted
              | ok result =>
                rcases result with ⟨last, more⟩
                have equal : last = after := by
                  simpa [Native.lower, left, right, joined, tail] using
                    (congrArg (Except.map Prod.fst) accepted)
                simpa [run, ih left, ih right, joined, equal] using ih tail

theorem unique_instructions {first second : Native.Plan}
    (a : Native.Checked first) (b : Native.Checked second) (same : first.input = second.input) :
    first.instructions = second.instructions := by
  have equality := a.lowered.symm.trans ((congrArg (Native.lower 4096 {}) same).trans b.lowered)
  exact congrArg Prod.snd (Except.ok.inj equality)

/-- Lowering erases self-copy rather than relying on a native alias special
case. `lowered_state` connects the surrounding lowering to `checkAction`, where
the original loan permissions and initialization are still checked. -/
theorem self_copy_erased {state : State} {name : Symbol} {instructions : List Native.Instruction}
    (accepted : Native.action state (.copy name name) = .ok instructions) : instructions = [] := by
  cases found : state.loan? name with
  | none =>
    simp [Native.action, found] at accepted
    cases accepted
  | some loan => simpa [Native.action, found] using accepted.symm

/-- Even direct callers supplying an untrusted native plan must obtain the
actual source checker certificate and exact lowering before any text is returned. -/
theorem generated_checked {plan : Native.Plan} {report : Bool} {budget : Nat} {text : String}
    (generated : Native.generate plan report budget = .ok text) : Nonempty (Native.Checked plan) := by
  cases checked : Native.audit plan with
  | error diagnostic => simp [Native.generate, checked] at generated
  | ok certificate => exact ⟨certificate⟩

theorem checked_closed {plan : Native.Plan} (checked : Native.Checked plan) :
    run 4096 {} plan.input = .ok checked.source.finalState ∧
    auditState checked.source.finalState = true ∧
    checked.source.finalState.allocations = [] ∧ checked.source.finalState.loans = [] :=
  ⟨lowered_state checked.lowered, checked.source.valid, checked.source.closed⟩

end VastitasOracle.StorageCodegen
