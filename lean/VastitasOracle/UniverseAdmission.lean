import VastitasKernel.UniverseAdmission
import VastitasOracle.StorageShapes
import VastitasOracle.StorageNumerical

/-! Local facts for the partial #350 model. These do not change CS/MS/CF,
prove frontend staging/erasure, or identify native storage with the mathematical
coordinate functions in El. No new assumptions or proof authority are added. -/
namespace VastitasOracle.UniverseAdmission
open VastitasKernel VastitasKernel.UniverseAdmission
open VastitasKernel.Indexed.Core VastitasKernel.Storage

theorem scalar_has_existing_type (type : PureType) (value : ScalarEl type)
    (declarations : Declarations) (world : Semantics.World) :
    Semantics.ValueHasType declarations world (scalarValue type value) (.pure type) := by
  cases type with
  | pair element => cases element <;> trivial
  | nat | int | bool | unit => trivial

/-- Every accepted specialization returns exactly the module passed to the
existing independent audit, not another semantically similar Core. -/
theorem stage_actual_core (operation : CoreHom a b) (checked : Typing.CheckedModule false)
    (accepted : stage operation = .ok checked) : checked.module = operation.module := by
  unfold stage Typing.checkModule at accepted
  split at accepted
  · split at accepted
    · split at accepted
      · cases accepted; rfl
      · contradiction
    · contradiction
  · contradiction

/-- Universal input facts about the existing bounded Core evaluator for this
closed profile, not just sampled numerical observations. -/
theorem identity_denotation (type : PureType) (value : ScalarEl type) (fuel : Nat) :
    Semantics.eval (CoreHom.identity type).module (fuel + 1)
      (Semantics.bindValue (fun _ => none) 0 (scalarValue type value))
      (CoreHom.identity type).term = some (scalarValue type value) := by
  simp [CoreHom.term, parameter, Semantics.eval, Semantics.bindValue]

theorem natToInt_denotation (value fuel : Nat) :
    Semantics.eval CoreHom.natToInt.module (fuel + 2)
      (Semantics.bindValue (fun _ => none) 0 (.natural value)) CoreHom.natToInt.term =
      some (scalarValue .int (denote CoreHom.natToInt value)) := by
  simp [CoreHom.term, parameter, Semantics.eval, Semantics.bindValue, scalarValue, denote]

theorem booleanNot_denotation (value : Bool) (fuel : Nat) :
    Semantics.eval CoreHom.booleanNot.module (fuel + 2)
      (Semantics.bindValue (fun _ => none) 0 (.boolean value)) CoreHom.booleanNot.term =
      some (scalarValue .bool (denote CoreHom.booleanNot value)) := by
  simp [CoreHom.term, parameter, Semantics.eval, Semantics.bindValue,
    Semantics.evalUnary, scalarValue, denote]

theorem no_missing_representation : ¬ Nonempty (Admitted target context type none) := by
  rintro ⟨accepted⟩
  cases accepted.supplied

theorem nonnegative_denotation (value : Int) (fuel : Nat) :
    Semantics.eval CoreHom.nonnegative.module (fuel + 2)
      (Semantics.bindValue (fun _ => none) 0 (.integer value)) CoreHom.nonnegative.term =
      some (scalarValue .bool (denote CoreHom.nonnegative value)) := by
  simp [CoreHom.term, parameter, Semantics.eval, Semantics.bindValue,
    Semantics.evalBinary, Semantics.evalIntBinary, scalarValue, denote]

theorem supplied_representation_unique
    (left right : Admitted target context type request) :
    left.representation = right.representation := by
  exact Option.some.inj (left.supplied.symm.trans right.supplied)

/-- Only this model's observation is proof-insensitive. This does not establish
proof erasure through source elaboration, caches, code generation or native IO. -/
theorem realization_proof_irrelevant
    (left right : Admitted target context (.tensorShape shape) (some (.tensorShape scalar elements)))
    (values : Shapes.Valuation) : realizeShape left values = realizeShape right values := rfl

theorem shape_uses_existing_checker
    (admitted : Admitted target context (.tensorShape shape) (some (.tensorShape scalar elements))) :
    ∃ checked, Shapes.check context.slots {} [.allocate 0 scalar elements shape] = .ok checked := by
  cases target
  have same := Option.some.inj admitted.supplied.symm
  have layout := admitted.layout
  rw [same] at layout
  change (Shapes.check context.slots {} [.allocate 0 scalar elements shape]).isOk = true at layout
  cases result : Shapes.check context.slots {} [.allocate 0 scalar elements shape] with
  | error problem =>
    have impossible : (false : Bool) = true := by
      simpa only [result, Except.isOk, Except.toBool] using layout
    exact Bool.noConfusion impossible
  | ok checked => exact ⟨checked, rfl⟩

/-- Reuse the production shape-to-storage theorem with all its guard premises.
The existential schedule is the actual interpreter of the accepted allocation. -/
theorem shape_realizes_existing_storage
    (admitted : Admitted target context (.tensorShape shape) (some (.tensorShape scalar elements)))
    (values : Shapes.Valuation)
    (guards : ∀ checked, Shapes.check context.slots {} [.allocate 0 scalar elements shape] = .ok checked →
      Shapes.guardsHold values checked.guards) :
    ∃ checked concrete,
      Shapes.check context.slots {} [.allocate 0 scalar elements shape] = .ok checked ∧
      Shapes.instantiate values 4096 {} [.allocate 0 scalar elements shape] = .ok concrete ∧
      Storage.run 4096 {} concrete = .ok (checked.after.eval values) ∧
      auditState (checked.after.eval values) = true := by
  obtain ⟨checked, accepted⟩ := shape_uses_existing_checker admitted
  obtain ⟨concrete, instantiated, executed, audited⟩ :=
    StorageShapes.checked_realizes values _ {} _ checked
      (by simp [Shapes.guardsHold, Shapes.Frame.guards]) (guards checked accepted)
  exact ⟨checked, concrete, accepted, instantiated, executed, audited⟩

theorem owned_representation_obligations
    (admitted : Admitted target context (.ownedMap source destination) (some (.ownedMap name))) :
    Numerical.Valid context.environment context.numerical ∧ auditState context.resources = true ∧
    ∃ view, Numerical.value? context.numerical name = some (.ownedMap view) ∧
      view.source = source ∧ view.target = destination ∧
      view.Live context.resources ∧ view.Initialized context.resources := by
  cases target
  have same := Option.some.inj admitted.supplied.symm
  have layout := admitted.layout
  rw [same] at layout
  unfold Layoutable layoutable at layout
  cases found : Numerical.value? context.numerical name with
  | none => simp [found] at layout
  | some value =>
    cases value <;> simp [found] at layout
    exact ⟨layout.1.1, layout.1.2, _, rfl, layout.2⟩

/-- The existing receipt supplies the actual state transition and complete
metadata. Payload preservation by a native backend remains a separate duty. -/
theorem owned_transfer_actual (receipt : OwnedTransfer) :
    checkAction receipt.before (.move receipt.view.owner receipt.target) = .ok receipt.after ∧
    Numerical.value? receipt.values receipt.target =
      some (.ownedMap {receipt.view with owner := receipt.target}) :=
  StorageNumerical.owned_transfer receipt

end VastitasOracle.UniverseAdmission
