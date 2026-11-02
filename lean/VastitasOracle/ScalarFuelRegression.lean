import VastitasOracle.ScalarTotality

/-! Kernel-checked edge cases; no native_decide or external evaluation oracle.
The chosen branch changes the actual least depth-fuel, so a fixed bound cannot
silently stand in for least fuel. -/
namespace VastitasOracle.ScalarFuel.Regression
open VastitasKernel.Indexed.Core
open Semantics VastitasKernel.Indexed.Core.ScalarFuel

private def empty : Values := fun _ => none
private def result (t : PureType) : Result := ⟨.pure t, none⟩
private def inputVar (t : PureType) : Term := .variable 0 (result t)
private def branchTerm : Term :=
  .branch (inputVar .bool) (.integer 7) (.natToInt (.natural 9)) (result .int)
private def branchFunction : Function := {
  id := 0
  definition := ⟨⟨⟨"/scalar-fuel", "scalar-fuel", "1"⟩, []⟩, "choose"⟩
  parameters := [parameter .bool]
  returnType := .pure .int
  body := branchTerm }
private def fixture : Module := ⟨⟨[], [], []⟩, [branchFunction], none⟩
private theorem fixture_typed : Typing.ModuleTyped fixture := by
  constructor
  · exact (Typing.validDeclarations_iff _).mp (by decide)
  · decide
  · simp [Typing.freshSerials, fixture, branchFunction, branchTerm, inputVar,
      Typing.allocatedSerials, Typing.resultSerials, parameter, result, Term.result]
  · intro function member
    have same : function = branchFunction := by simpa [fixture] using member
    subst function
    simp [Typing.FunctionTyped, fixture, branchFunction, parameter, Typing.ParametersValid,
      Result.Valid, DataType.Valid, DataType.Scoped, DataType.refs, Typing.lookup,
      Typing.HasType, branchTerm, inputVar, result, Term.result, Typing.BranchTyping,
      Typing.Compatible]

private theorem fixture_ordered :
    VastitasKernel.Dependency.audit (Typing.dependencyEntries fixture) = true := by
  simp [VastitasKernel.Dependency.audit, VastitasKernel.Dependency.auditFrom,
    Typing.dependencyEntries, fixture, branchFunction, branchTerm, inputVar, Term.callIds]
private def checked : Typing.CheckedModule false :=
  ⟨fixture, fixture_typed, fixture_ordered, rfl⟩
private theorem checked_actual : Typing.checkModule fixture false = .ok checked := by
  simp only [Typing.checkModule, dite_eq_left fixture_typed, dite_eq_left fixture_ordered,
    dite_eq_left (show Typing.MainValid fixture false from rfl)]
  rfl
private def chosen : AcceptedHom .bool .int :=
  ⟨fixture, checked, checked_actual, 0, branchFunction, rfl, rfl, rfl, rfl⟩

-- Actual checker acceptance and exact retained Core, using kernel-checked
-- evidence rather than attempting to kernel-reduce the opaque hash primitive
-- used internally by the existing finite distinctness audit.
example : stage fixture 0 .bool .int = .ok chosen := by
  unfold stage
  split
  · rename_i problem rejected
    rw [checked_actual] at rejected
    cases rejected
  · rename_i other accepted
    have same : other = checked := Except.ok.inj (accepted.symm.trans checked_actual)
    subst other
    simp [checked, fixture, branchFunction, parameter, chosen, supported, branchTerm, inputVar, List.find?]
example : chosen.input = fixture := rfl
example : chosen.function.body = branchTerm := rfl
example : chosen.checked.module = fixture := accepted_actual_core chosen

-- Runtime regression checks do not supply proof authority.
private def check (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError "scalar fuel regression failed")
#eval check (stage fixture 0 .bool .int).isOk
#eval check (!(stage {fixture with functions := [{branchFunction with
    body := .branch (inputVar .bool) (.integer 7) (.variable 99 (result .int)) (result .int)}]}
    0 .bool .int).isOk)
#eval check (!(stage fixture 99 .bool .int).isOk)
#eval check (!(stage fixture 0 .nat .int).isOk)
#eval check (!(stage fixture 0 .bool .bool).isOk)
private def calledFixture : Module := {fixture with functions :=
  [branchFunction, {branchFunction with id := 1, body := .call 0 [inputVar .bool] [] (result .int)}]}
#eval check (Typing.checkModule calledFixture false).isOk
#eval check (!(stage calledFixture 1 .bool .int).isOk)
example : supported (.branch (.boolean true) (.integer 0)
    (.call 0 [] [] (result .int)) (result .int)) = false := rfl

-- Operational failures, exhaustion and successes are distinct observations.
example : evalFuel 0 empty (inputVar .int) = .outOfFuel := rfl
example : evalFuel 1 empty (inputVar .int) = .failure (.missingVariable 0) := rfl
example (fuel : Nat) (enough : 1 ≤ fuel) :
    evalFuel fuel empty (inputVar .int) = .failure (.missingVariable 0) :=
  evalFuel_terminal enough rfl (by intro impossible; cases impossible)
example : evalFuel 2 empty (.natToInt (.boolean true)) = .failure .invalidOperand := rfl
example : evalFuel 1 empty (.natToInt (.boolean true)) = .outOfFuel := rfl
example : evalFuel 2 empty (.branch (.boolean true) (.integer 7)
    (.natToInt (.boolean false)) (result .int)) = .success (.integer 7) := rfl

-- Let binding and pair projections preserve the real scalar operations.
example : evalFuel 4 empty (.letE 0 (.pair .nat (.natural 2) (.natural 5))
    (.project .nat false (inputVar (.pair .nat)))) = .success (.natural 5) := rfl
example : evalFuel 2 empty (.binary .sub (.natural 2) (.natural 5) (result .nat)) =
    .success (.natural 0) := rfl
example : evalFuel 2 empty (.binary .add (.natural 2) (.integer 5) (result .int)) =
    .failure .invalidOperand := rfl

example : leastFuel (certify chosen) true = 2 := by
  apply leastFuel_eq_of _ _ (by decide)
  intro n before
  match n with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => omega

example : leastFuel (certify chosen) false = 3 := by
  apply leastFuel_eq_of _ _ (by decide)
  intro n before
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => omega

example (x : Bool) : denoteTotal (certify chosen) x = (if x then (7 : Int) else 9) := by
  apply Eq.symm
  apply successful_value_unique (certify chosen) x (fuel := 3)
  cases x <;> rfl

-- Supply different Prop certificates for the same actual accepted function.
example (h : Totality chosen) (x : Bool) :
    denoteTotal ⟨chosen, h⟩ x = denoteTotal (certify chosen) x := rfl

-- The least-witness construction is not restricted to positive fuel.
example (h : ∃ n : Nat, n = 0) : LeastFuel.least (· = 0) h = 0 :=
  LeastFuel.least_spec _ h

end VastitasOracle.ScalarFuel.Regression
