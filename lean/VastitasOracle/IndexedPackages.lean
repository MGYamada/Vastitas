import VastitasKernel.IndexedContractAudit
import VastitasOracle.Indexed

namespace VastitasOracle.Indexed
open VastitasKernel.Indexed

export VastitasKernel.Indexed.Audit
  (validPackageShape_iff validPackagePayload_iff validPackageOpening_iff)

theorem checked_package_shape_valid {env : CheckedEnvironment} (shape : CheckedPackageShape env) :
    shape.shape.Valid env.environment := (validPackageShape_iff _ _).mp shape.accepted

theorem checked_package_payload_valid {env : CheckedEnvironment} {shape : CheckedPackageShape env}
    (payload : CheckedPackagePayload shape) : payload.payload.Valid env.environment shape.shape :=
  (validPackagePayload_iff _ _ _).mp payload.accepted

theorem checked_package_opening_valid {env : CheckedEnvironment} {shape : CheckedPackageShape env}
    {allowed : List ObjectRef} {brand : Nat} (opening : CheckedPackageOpening shape allowed brand) :
    opening.opening.Valid env.environment shape.shape allowed brand :=
  (validPackageOpening_iff _ _ _ _ _).mp opening.accepted

/-- Instantiation cannot introduce another free local reference: only the
explicitly bound witness can occur in a field's type indices. -/
theorem instantiated_field_refs (field : BoundApplication) (witness ref : ObjectRef)
    (occurs : ref ∈ (field.instantiate witness).refs) :
    ref = witness ∨ ∃ id, ref = .global id := by
  simp only [BoundApplication.instantiate, Application.refs] at occurs
  obtain ⟨index, member, equation⟩ := List.mem_filterMap.mp occurs
  obtain ⟨bound, _, rfl⟩ := List.mem_map.mp member
  cases bound with
  | witness =>
    have equal : witness = ref := by simpa [BoundIndex.instantiate] using equation
    exact Or.inl equal.symm
  | global id =>
    have equal : ObjectRef.global id = ref := by simpa [BoundIndex.instantiate] using equation
    exact Or.inr ⟨id, equal.symm⟩
  | domain | marker | natural => simp [BoundIndex.instantiate] at equation

theorem instantiated_field_scoped (field : BoundApplication) (witness : ObjectRef) (allowed : List ObjectRef) :
    (field.instantiate witness).Scoped (witness :: allowed) := by
  intro ref occurs
  rcases instantiated_field_refs field witness ref occurs with rfl | ⟨id, rfl⟩
  · cases ref <;> simp [ObjectRef.Scoped]
  · trivial

theorem payload_field_association {env : CheckedEnvironment} {shape : CheckedPackageShape env}
    (payload : CheckedPackagePayload shape) (field : Application) (member : field ∈ payload.payload.fields) :
    ∃ template ∈ shape.shape.fields, field = template.instantiate payload.payload.witness := by
  have associated := (checked_package_payload_valid payload).2.1
  rw [associated] at member
  simp only [PackageShape.instantiate, List.mem_map] at member
  obtain ⟨template, present, equality⟩ := member
  exact ⟨template, present, equality.symm⟩

theorem payload_has_only_bound_or_global_refs {env : CheckedEnvironment} {shape : CheckedPackageShape env}
    (payload : CheckedPackagePayload shape) (field : Application) (member : field ∈ payload.payload.fields)
    (ref : ObjectRef) (occurs : ref ∈ field.refs) :
    ref = payload.payload.witness ∨ ∃ id, ref = .global id := by
  obtain ⟨template, _, rfl⟩ := payload_field_association payload field member
  exact instantiated_field_refs template payload.payload.witness ref occurs

theorem opening_witness {env : CheckedEnvironment} {shape : CheckedPackageShape env}
    {allowed : List ObjectRef} {brand : Nat} (opening : CheckedPackageOpening shape allowed brand) :
    opening.opening.witness = .local shape.shape.witnessType brand :=
  (checked_package_opening_valid opening).2.1

theorem opening_fresh {env : CheckedEnvironment} {shape : CheckedPackageShape env}
    {allowed : List ObjectRef} {brand : Nat} (opening : CheckedPackageOpening shape allowed brand)
    (type : ObjectType) (existing : Nat) (member : ObjectRef.local type existing ∈ allowed) :
    existing ≠ brand := (checked_package_opening_valid opening).1 _ member

theorem reopening_distinct {env : CheckedEnvironment} {shape : CheckedPackageShape env}
    {allowed₁ allowed₂ : List ObjectRef} {brand₁ brand₂ : Nat}
    (first : CheckedPackageOpening shape allowed₁ brand₁)
    (second : CheckedPackageOpening shape allowed₂ brand₂)
    (retained : first.opening.witness ∈ allowed₂) : first.opening.witness ≠ second.opening.witness := by
  have firstWitness := opening_witness first
  rw [firstWitness] at retained
  have distinct := opening_fresh second _ _ retained
  rw [firstWitness, opening_witness second]
  intro equal
  exact distinct (ObjectRef.local.inj equal).2

theorem opening_field_scoped {env : CheckedEnvironment} {shape : CheckedPackageShape env}
    {allowed : List ObjectRef} {brand : Nat} (opening : CheckedPackageOpening shape allowed brand)
    (field : Application) (member : field ∈ opening.opening.fields) :
    field.Scoped (opening.opening.witness :: allowed) :=
  ((checked_package_opening_valid opening).2.2.2 field member).2

end VastitasOracle.Indexed
