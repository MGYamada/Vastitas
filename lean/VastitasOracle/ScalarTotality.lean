import VastitasOracle.ScalarFuel

/-! The first #350 TotalHom instance: an actual accepted call-free scalar body
plus a Prop totality certificate. Meaning is derived from its least successful
evaluation, never supplied as an independent mathematical function. -/
namespace VastitasOracle.ScalarFuel
open VastitasKernel.Indexed.Core
open Semantics VastitasKernel.Indexed.Core.ScalarFuel

theorem accepted_actual_core (f : AcceptedHom a b) : f.checked.module = f.input := by
  have accepted := f.accepted
  unfold Typing.checkModule at accepted
  split at accepted
  · split at accepted
    · split at accepted
      · exact (congrArg Typing.CheckedModule.module (Except.ok.inj accepted)).symm
      · contradiction
    · contradiction
  · contradiction

theorem encode_typed (type : PureType) (x : El type) (env : Declarations) (world : World) :
    ValueHasType env world (encode type x) (.pure type) := by
  cases type with
  | pair element => cases element <;> trivial
  | nat | int | bool | unit => trivial

theorem typed_encoded (type : PureType) (value : Value)
    (typed : ValueHasType env world value (.pure type)) :
    ∃ x : El type, value = encode type x := by
  cases type with
  | pair element =>
      cases element <;> cases value <;> simp_all [ValueHasType, El, encode]
  | nat | int | bool | unit =>
      cases value <;> simp_all [ValueHasType, El, encode]

@[simp] theorem decode_encode (type : PureType) (x : El type) :
    decode type (encode type x) = .success x := by
  cases type with
  | pair element => cases element <;> rfl
  | unit => cases x; rfl
  | nat | int | bool => rfl

theorem decode_success (type : PureType) (value : Value) (x : El type)
    (decoded : decode type value = .success x) : value = encode type x := by
  cases type with
  | pair element =>
      cases element <;> cases value <;> simp_all [decode, encode]
      all_goals cases (EvalOutcome.success.inj decoded) <;> simp
  | nat | int | bool | unit =>
      cases value <;> simp_all [decode, encode]
      all_goals cases (EvalOutcome.success.inj decoded) <;> rfl

theorem evalAccepted_extends (f : AcceptedHom a b) (x : El a)
    (small large : Nat) (enough : small ≤ large) :
    Outcome.Extends (evalAccepted f small x) (evalAccepted f large x) :=
  Outcome.bind_extends (evalFuel_extends small large enough _ _) (fun _ => Outcome.refl _)

/-- An exact bridge in both directions at each fuel, including the decoded
codomain. No alternative body or assumed mathematical denotation occurs. -/
theorem evalAccepted_success_iff (f : AcceptedHom a b) (x : El a) (fuel : Nat) (y : El b) :
    evalAccepted f fuel x = .success y ↔
      Semantics.eval f.checked.module fuel (inputValues a x) f.function.body =
        some (encode b y) := by
  have erased := evalFuel_erases f.checked.module fuel (inputValues a x) f.function.body f.profile
  rw [← erased, Outcome.toOption_eq_some]
  unfold evalAccepted
  cases observed : evalFuel fuel (inputValues a x) f.function.body with
  | outOfFuel | failure _ => simp [EvalOutcome.bind]
  | success value =>
      simp only [EvalOutcome.bind, EvalOutcome.success.injEq]
      constructor
      · exact decode_success b value y
      · intro same; rw [same, decode_encode]

def Totality (f : AcceptedHom a b) : Prop :=
  ∀ x : El a, ∃ fuel, (evalAccepted f fuel x).IsSuccess

/-- Reuses existing checked whole-program typed totality. Thus the certificate
for this finite profile is proved from acceptance, not postulated by the user. -/
theorem accepted_total (f : AcceptedHom a b) : Totality f := by
  intro x
  have context : ContextHasType f.checked.module.declarations (fun _ => none)
      (inputValues a x) f.function.parameters := by
    intro p member
    rw [f.parameters] at member
    have same : p = parameter a := by simpa using member
    subst p
    exact ⟨encode a x, by simp [inputValues, bindValue, parameter],
      encode_typed a x _ _, trivial⟩
  obtain ⟨value, evaluated, typed⟩ :=
    IndexedProgramSafety.checked_functions_total_and_typed f.checked f.function
      (List.mem_of_find?_eq_some f.found) (fun _ => none) (inputValues a x) context
  rw [f.result] at typed
  obtain ⟨y, rfl⟩ := typed_encoded b value typed
  obtain ⟨fuel, observed⟩ := IndexedEvaluation.evaluates_observed evaluated
  exact ⟨fuel, by rw [(evalAccepted_success_iff f x fuel y).mpr observed]; trivial⟩

abbrev TotalHom (a b : PureType) := {f : AcceptedHom a b // Totality f}

def certify (f : AcceptedHom a b) : TotalHom a b := ⟨f, accepted_total f⟩

noncomputable def leastFuel (f : TotalHom a b) (x : El a) : Nat :=
  LeastFuel.least (fun fuel => (evalAccepted f.val fuel x).IsSuccess) (f.property x)

theorem leastFuel_success (f : TotalHom a b) (x : El a) :
    (evalAccepted f.val (leastFuel f x) x).IsSuccess :=
  LeastFuel.least_spec _ (f.property x)

theorem leastFuel_minimal (f : TotalHom a b) (x : El a)
    (successful : (evalAccepted f.val fuel x).IsSuccess) : leastFuel f x ≤ fuel :=
  LeastFuel.least_minimal _ (f.property x) successful

noncomputable def denoteTotal (f : TotalHom a b) (x : El a) : El b :=
  (evalAccepted f.val (leastFuel f x) x).value (leastFuel_success f x)

theorem denoteTotal_at_least (f : TotalHom a b) (x : El a) :
    evalAccepted f.val (leastFuel f x) x = .success (denoteTotal f x) :=
  Outcome.success_value _ (leastFuel_success f x)

/-- Universal sufficient-fuel agreement, with no existential weakening. -/
theorem denoteTotal_agrees (f : TotalHom a b) (x : El a)
    (enough : leastFuel f x ≤ fuel) :
    evalAccepted f.val fuel x = .success (denoteTotal f x) := by
  have stable := evalAccepted_extends f.val x (leastFuel f x) fuel enough
  rw [denoteTotal_at_least] at stable
  exact stable (by intro impossible; cases impossible)

theorem denoteTotal_actual_core (f : TotalHom a b) (x : El a)
    (enough : leastFuel f x ≤ fuel) :
    Semantics.eval f.val.checked.module fuel (inputValues a x) f.val.function.body =
      some (encode b (denoteTotal f x)) :=
  (evalAccepted_success_iff f.val x fuel _).mp (denoteTotal_agrees f x enough)

theorem successful_value_unique (f : TotalHom a b) (x : El a)
    (observed : evalAccepted f.val fuel x = .success y) : y = denoteTotal f x := by
  have minimal := leastFuel_minimal f x (by rw [observed]; trivial)
  exact EvalOutcome.success.inj (observed.symm.trans (denoteTotal_agrees f x minimal))

theorem before_least_outOfFuel (f : TotalHom a b) (x : El a)
    (before : fuel < leastFuel f x) : evalAccepted f.val fuel x = .outOfFuel := by
  cases observed : evalAccepted f.val fuel x with
  | outOfFuel => rfl
  | success y =>
      have := leastFuel_minimal f x (by rw [observed]; trivial)
      omega
  | failure problem =>
      have stable := evalAccepted_extends f.val x fuel (leastFuel f x) (by omega)
      rw [observed] at stable
      have equal := stable (by intro impossible; cases impossible)
      rw [denoteTotal_at_least] at equal
      cases equal

theorem leastFuel_eq_of (f : TotalHom a b) (x : El a)
    (successful : (evalAccepted f.val fuel x).IsSuccess)
    (earlier : ∀ n, n < fuel → evalAccepted f.val n x = .outOfFuel) :
    leastFuel f x = fuel := by
  have upper := leastFuel_minimal f x successful
  by_cases smaller : leastFuel f x < fuel
  · have failed := earlier (leastFuel f x) smaller
    have succeeded := denoteTotal_at_least f x
    rw [failed] at succeeded
    cases succeeded
  · omega

/-- Definitional proof irrelevance, deliberately an `rfl` regression. -/
example (f : AcceptedHom a b) (h₁ h₂ : Totality f) (x : El a) :
    denoteTotal ⟨f, h₁⟩ x = denoteTotal ⟨f, h₂⟩ x := rfl

end VastitasOracle.ScalarFuel
