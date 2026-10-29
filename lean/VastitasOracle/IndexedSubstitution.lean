import VastitasOracle.IndexedPackages

namespace VastitasOracle.IndexedSubstitution
open VastitasKernel.Indexed

/-- A proof helper for mapping actual indexed applications. Operational call
substitutions must additionally satisfy their own authority/freshness contracts. -/
def mapIndexRefs (mapping : ObjectRef → ObjectRef) : Index → Index
  | .object ref => .object (mapping ref)
  | index => index

theorem parameter_map {env : Environment} (mapping : ObjectRef → ObjectRef)
    (types : ∀ ref, (mapping ref).type? env = ref.type? env)
    {parameter : Parameter} {index : Index} (accepted : parameter.Accepts env index) :
    parameter.Accepts env (mapIndexRefs mapping index) := by
  cases parameter <;> cases index <;> simp only [mapIndexRefs, Parameter.Accepts] at accepted ⊢
  all_goals first | exact accepted | simpa only [types] using accepted

theorem mapped_object_index (mapping : ObjectRef → ObjectRef) {indices : List Index} {position : Nat}
    {ref : ObjectRef} (found : indices[position]? = some (.object ref)) :
    (indices.map (mapIndexRefs mapping))[position]? = some (.object (mapping ref)) := by
  simp [List.getElem?_map, found, mapIndexRefs]

theorem constraint_map {env : Environment} (mapping : ObjectRef → ObjectRef)
    (types : ∀ ref, (mapping ref).type? env = ref.type? env)
    {indices : List Index} {constraint : Constraint} (holds : constraint.Holds env indices) :
    constraint.Holds env (indices.map (mapIndexRefs mapping)) := by
  cases constraint with
  | sameObject left right =>
      obtain ⟨l, r, leftFound, rightFound, equal⟩ := holds
      subst r
      exact ⟨mapping l, mapping l, mapped_object_index mapping leftFound,
        mapped_object_index mapping rightFound, rfl⟩
  | sameBase left right =>
      obtain ⟨l, r, lt, rt, leftFound, rightFound, leftType, rightType, marker⟩ := holds
      exact ⟨mapping l, mapping r, lt, rt, mapped_object_index mapping leftFound,
        mapped_object_index mapping rightFound, (types l).trans leftType, (types r).trans rightType, marker⟩
  | over object marker =>
      obtain ⟨ref, type, id, found, markerFound, typeFound, equal⟩ := holds
      exact ⟨mapping ref, type, id, mapped_object_index mapping found,
        by simp [List.getElem?_map, markerFound, mapIndexRefs], (types ref).trans typeFound, equal⟩

theorem application_map {env : Environment} (mapping : ObjectRef → ObjectRef)
    (types : ∀ ref, (mapping ref).type? env = ref.type? env)
    {application : Application} (valid : application.Valid env) :
    Application.Valid env ⟨application.family, application.indices.map (mapIndexRefs mapping)⟩ := by
  obtain ⟨family, found, arity, parameters, constraints⟩ := valid
  refine ⟨family, found, by simpa using arity, ?_, ?_⟩
  · intro pair member
    rw [List.zip_map_right] at member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact parameter_map mapping types (parameters original originalMember)
  · intro constraint member
    exact constraint_map mapping types (constraints constraint member)

def rebrand (brand : Nat) : ObjectRef → ObjectRef
  | .global id => .global id
  | .local type _ => .local type brand

theorem rebrand_type (env : Environment) (brand : Nat) (ref : ObjectRef) :
    (rebrand brand ref).type? env = ref.type? env := by cases ref <;> rfl

theorem bound_rebrand (field : BoundApplication) (type : ObjectType) (old new : Nat) :
    field.instantiate (.local type new) =
      ⟨field.family, (field.instantiate (.local type old)).indices.map (mapIndexRefs (rebrand new))⟩ := by
  unfold BoundApplication.instantiate
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro index _
  cases index <;> rfl

theorem bound_application_rebrand {env : Environment} {field : BoundApplication} {type : ObjectType}
    {old : Nat} (new : Nat) (valid : (field.instantiate (.local type old)).Valid env) :
    (field.instantiate (.local type new)).Valid env := by
  rw [bound_rebrand field type old new]
  exact application_map (rebrand new) (rebrand_type env new) valid

theorem valid_opening_of_shape {env : Environment} {shape : PackageShape}
    (valid : shape.Valid env) {allowed : List ObjectRef} {brand : Nat} (fresh : FreshBrand allowed brand) :
    PackageOpening.Valid env shape allowed brand
      ⟨.local shape.witnessType brand, shape.instantiate (.local shape.witnessType brand)⟩ := by
  refine ⟨fresh, rfl, rfl, ?_⟩
  intro application member
  obtain ⟨field, fieldMember, rfl⟩ := List.mem_map.mp member
  exact ⟨bound_application_rebrand brand (valid.2.2 _ (List.mem_map.mpr ⟨field, fieldMember, rfl⟩)),
    VastitasOracle.Indexed.instantiated_field_scoped field _ allowed⟩

/-- A valid checked package shape plus the actual allocation context always
passes the real generated-opening audit when the requested serial is fresh. -/
theorem openPackage_success {env : CheckedEnvironment} (shape : CheckedPackageShape env)
    (allowed : List ObjectRef) (brand : Nat) (fresh : FreshBrand allowed brand) :
    ∃ opening, openPackage shape allowed brand = .ok opening ∧
      opening.opening = ⟨.local shape.shape.witnessType brand,
        shape.shape.instantiate (.local shape.shape.witnessType brand)⟩ := by
  have valid := valid_opening_of_shape (VastitasOracle.Indexed.checked_package_shape_valid shape) fresh
  have accepted := (VastitasKernel.Indexed.Audit.validPackageOpening_iff _ _ _ _ _).mpr valid
  unfold openPackage checkPackageOpening
  rw [dite_eq_left accepted]
  exact ⟨_, rfl, rfl⟩

end VastitasOracle.IndexedSubstitution
