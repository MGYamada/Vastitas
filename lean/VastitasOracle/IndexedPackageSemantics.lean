import VastitasOracle.IndexedSemantics
import VastitasOracle.IndexedSubstitution

/-! Actual existential payloads retain their witness association when packaged
or opened under a new nominal brand. These lemmas use the real bound templates
and runtime values; full evaluation/activation preservation remains separate. -/
namespace VastitasOracle.IndexedPackageSemantics
open VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasOracle.IndexedSemantics

theorem point_shape {env : Environment} {world : World} {point : Point} {application : Application}
    (typed : IndexedHasType env world (.point point) application) :
    familyRepresentation env application.family = some .point ∧
      ∃ target source, application.indices = [.object target, .object source] ∧
        RefDenotes env world target point.target ∧ RefDenotes env world source point.source := by
  have shape := typed.2
  split at shape <;> simp_all
  exact ⟨_, _, ⟨rfl, rfl⟩, shape⟩

theorem morphism_shape {env : Environment} {world : World} {map : Morphism} {application : Application}
    (typed : IndexedHasType env world (.morphism map) application) :
    familyRepresentation env application.family = some .morphism ∧
      ∃ source target, application.indices = [.object source, .object target] ∧
        RefDenotes env world source map.source ∧ RefDenotes env world target map.target := by
  have shape := typed.2
  split at shape <;> simp_all
  exact ⟨_, _, ⟨rfl, rfl⟩, shape⟩

theorem map_two {f : α → β} {xs : List α} {a b : β} (equal : xs.map f = [a, b]) :
    ∃ x y, xs = [x, y] ∧ f x = a ∧ f y = b := by
  obtain ⟨x, rest, rfl, rfl, tailOne⟩ := List.map_eq_cons_iff.mp equal
  obtain ⟨y, rest, rfl, rfl, tailTwo⟩ := List.map_eq_cons_iff.mp tailOne
  have empty : rest = [] := List.map_eq_nil_iff.mp tailTwo
  subst rest
  exact ⟨x, y, rfl, rfl, rfl⟩

/-- This transport follows the bound template, not a textual replacement of
references. A global witness may equal an explicitly named global field index;
opening must replace only the witness occurrence and keep the explicit global. -/
theorem bound_reference_transport {env : Environment} {before after : World}
    {old new : ObjectRef} {witness value : Object}
    (oldDenotes : RefDenotes env before old witness) (newDenotes : RefDenotes env after new witness)
    (index : BoundIndex) {reference : ObjectRef}
    (instantiated : index.instantiate old = .object reference)
    (denotes : RefDenotes env before reference value) :
    ∃ reference', index.instantiate new = .object reference' ∧ RefDenotes env after reference' value := by
  cases index with
  | witness =>
      cases instantiated
      have same := denotes_unique oldDenotes denotes
      subst value
      exact ⟨new, rfl, newDenotes⟩
  | global id =>
      cases instantiated
      exact ⟨.global id, rfl, denotes⟩
  | domain | marker | natural => contradiction

theorem bound_token_transport {env : Environment} {before after : World}
    {old new : ObjectRef} {witness : Object} (newDenotes : RefDenotes env after new witness)
    (field : BoundApplication)
    (known : ∀ ref ∈ (field.instantiate old).refs, ∃ object, RefDenotes env before ref object) :
    ∀ ref ∈ (field.instantiate new).refs, ∃ object, RefDenotes env after ref object := by
  intro ref member
  obtain ⟨index, indexMember, projection⟩ := List.mem_filterMap.mp member
  obtain ⟨bound, boundMember, rfl⟩ := List.mem_map.mp indexMember
  cases bound with
  | witness =>
      simp only [BoundIndex.instantiate, Option.some.injEq] at projection
      subst ref
      exact ⟨witness, newDenotes⟩
  | global id =>
      simp only [BoundIndex.instantiate, Option.some.injEq] at projection
      subst ref
      obtain ⟨object, denotes⟩ := known (.global id) (by
        apply List.mem_filterMap.mpr
        exact ⟨.object (.global id), List.mem_map.mpr ⟨.global id, boundMember, rfl⟩, rfl⟩)
      exact ⟨object, denotes⟩
  | domain | marker | natural => simp [BoundIndex.instantiate] at projection

theorem bound_field_transport {env : Environment} {before after : World}
    {old new : ObjectRef} {witness : Object}
    (oldDenotes : RefDenotes env before old witness) (newDenotes : RefDenotes env after new witness)
    (field : BoundApplication) (value : IndexedValue)
    (valid : (field.instantiate new).Valid env)
    (typed : IndexedHasType env before value (field.instantiate old)) :
    IndexedHasType env after value (field.instantiate new) := by
  cases value with
  | token =>
      have representation : familyRepresentation env field.family = some .token := by
        cases found : familyRepresentation env field.family <;> simp [IndexedHasType, BoundApplication.instantiate, found] at typed
        case some rep => cases rep <;> simp_all [BoundApplication.instantiate]
      refine ⟨valid, ?_⟩
      simp only [BoundApplication.instantiate, representation]
      apply bound_token_transport newDenotes field
      simpa only [BoundApplication.instantiate, representation] using typed.2
  | point point =>
      obtain ⟨representation, target, source, indices, targetDenotes, sourceDenotes⟩ := point_shape typed
      change familyRepresentation env field.family = some .point at representation
      obtain ⟨first, second, fields, fstIndex, sndIndex⟩ := map_two indices
      obtain ⟨target', fstNew, targetNew⟩ := bound_reference_transport oldDenotes newDenotes first fstIndex targetDenotes
      obtain ⟨source', sndNew, sourceNew⟩ := bound_reference_transport oldDenotes newDenotes second sndIndex sourceDenotes
      refine ⟨valid, ?_⟩
      simpa only [BoundApplication.instantiate, fields, List.map_cons, List.map_nil, fstNew, sndNew, representation]
        using And.intro targetNew sourceNew
  | morphism map =>
      obtain ⟨representation, source, target, indices, sourceDenotes, targetDenotes⟩ := morphism_shape typed
      change familyRepresentation env field.family = some .morphism at representation
      obtain ⟨first, second, fields, fstIndex, sndIndex⟩ := map_two indices
      obtain ⟨source', fstNew, sourceNew⟩ := bound_reference_transport oldDenotes newDenotes first fstIndex sourceDenotes
      obtain ⟨target', sndNew, targetNew⟩ := bound_reference_transport oldDenotes newDenotes second sndIndex targetDenotes
      refine ⟨valid, ?_⟩
      simpa only [BoundApplication.instantiate, fields, List.map_cons, List.map_nil, fstNew, sndNew, representation]
        using And.intro sourceNew targetNew

theorem bound_fields_transport {env : Environment} {before after : World}
    {old new : ObjectRef} {witness : Object}
    (oldDenotes : RefDenotes env before old witness) (newDenotes : RefDenotes env after new witness)
    (fields : List BoundApplication) (values : List IndexedValue)
    (valid : ∀ field ∈ fields, (field.instantiate new).Valid env)
    (typed : FieldsHaveTypes env before values (fields.map (BoundApplication.instantiate old))) :
    FieldsHaveTypes env after values (fields.map (BoundApplication.instantiate new)) := by
  induction fields generalizing values with
  | nil => cases values <;> exact typed
  | cons field fields ih =>
      cases values with
      | nil => contradiction
      | cons value values =>
          exact ⟨bound_field_transport oldDenotes newDenotes field value (valid field (by simp)) typed.1,
            ih values (fun field member => valid field (by simp [member])) typed.2⟩


theorem witness_fits_object {env : Environment} {world : World} {expected : ObjectType}
    {reference : ObjectRef} {object : Object} (fits : WitnessFits env expected reference)
    (denotes : RefDenotes env world reference object) : ObjectHasType env object expected := by
  obtain ⟨expectedValid, type, found, _, _, subset⟩ := fits
  obtain ⟨actual, actualFound, actualTyped⟩ := denotes.2
  have equal : actual = type := Option.some.inj (actualFound.symm.trans found)
  subst actual
  exact ⟨expectedValid, subset _ actualTyped.2⟩

theorem pack_payload_semantics {env : Declarations} {world : World} {application : Application}
    {shape : PackageShape} {payload : PackagePayload} {witness : Object} {fields : List IndexedValue}
    (found : env.package? application = some shape) (validShape : shape.Valid env.indexed)
    (validPayload : payload.Valid env.indexed shape)
    (denotes : RefDenotes env.indexed world payload.witness witness)
    (typedFields : FieldsHaveTypes env.indexed world fields payload.fields) :
    ValueHasType env world (.package witness fields) (.package application) := by
  have typedWitness := witness_fits_object validPayload.1 denotes
  refine ⟨shape, found, typedWitness, ?_⟩
  rw [validPayload.2.1] at typedFields
  exact bound_fields_transport denotes
    (bindLocal_denotes env.indexed (fun _ => none) 0 witness shape.witnessType typedWitness)
    shape.fields fields (fun field member => validShape.2.2 _ (List.mem_map.mpr ⟨field, member, rfl⟩)) typedFields

/-- An accepted opening preserves the actual ordered runtime fields and the
payload's witness under its exact new reference, including non-geometric token
families. It does not infer freshness of an arbitrary ambient world. -/
theorem opening_fields_semantics {env : CheckedEnvironment} {shape : CheckedPackageShape env}
    {allowed : List ObjectRef} {brand : Nat} (opening : CheckedPackageOpening shape allowed brand)
    (world : World) (witness : Object) (fields : List IndexedValue)
    (typedWitness : ObjectHasType env.environment witness shape.shape.witnessType)
    (typedFields : FieldsHaveTypes env.environment (witnessWorld witness) fields
      (shape.shape.instantiate shape.shape.representative)) :
    RefDenotes env.environment (bindLocal world brand witness) opening.opening.witness witness ∧
      FieldsHaveTypes env.environment (bindLocal world brand witness) fields opening.opening.fields := by
  have valid := VastitasOracle.Indexed.checked_package_opening_valid opening
  have newDenotes : RefDenotes env.environment (bindLocal world brand witness) opening.opening.witness witness := by
    rw [valid.2.1]
    exact bindLocal_denotes env.environment world brand witness shape.shape.witnessType typedWitness
  refine ⟨newDenotes, ?_⟩
  rw [valid.2.2.1]
  exact bound_fields_transport
    (bindLocal_denotes env.environment (fun _ => none) 0 witness shape.shape.witnessType typedWitness)
    newDenotes shape.shape.fields fields
    (fun field member => (valid.2.2.2 _ (by rw [valid.2.2.1]; exact List.mem_map.mpr ⟨field, member, rfl⟩)).1)
    typedFields

theorem opening_preserves_prior_bindings {env : CheckedEnvironment} {shape : CheckedPackageShape env}
    {allowed : List ObjectRef} {brand : Nat} (opening : CheckedPackageOpening shape allowed brand)
    (world : World) (witness : Object) (fresh : world brand = none) :
    WorldExtends world (bindLocal world brand witness) ∧
      opening.opening.witness = .local shape.shape.witnessType brand :=
  ⟨bindLocal_fresh_extends world brand witness fresh, VastitasOracle.Indexed.opening_witness opening⟩

/-- A field's declared global occurrence is fixed even when it initially
coincides with the witness. This is why generic nominal substitution alone is
insufficient for existential packing/opening. -/
theorem global_witness_keeps_explicit_global (family global : DeclId) (type : ObjectType) (brand : Nat) :
    (BoundApplication.instantiate (.local type brand) ⟨family, [.witness, .global global]⟩).indices =
      [.object (.local type brand), .object (.global global)] := rfl


theorem package_lookup_valid {env : Declarations} (valid : env.Valid)
    {application : Application} {shape : PackageShape} (found : env.package? application = some shape) :
    shape.Valid env.indexed := by
  unfold Declarations.package? at found
  simp only [Bind.bind, Option.bind] at found
  split at found
  · split at found
    · contradiction
    · rename_i declaration declared
      have declarationValid := valid.packages declaration (List.mem_of_find?_eq_some declared)
      exact declarationValid.2.2.2 shape (List.mem_of_find?_eq_some found)
  · contradiction

theorem core_pack_semantics {env : Declarations} {functions : Typing.Signatures} {ctx : Typing.Context}
    {world : World} {application : Application} {witnessTerm : Term} {fieldTerms : List Term}
    {shape : PackageShape} {reference : ObjectRef} {applications : List Application}
    {witnessValue : Value} {fields : List IndexedValue}
    (valid : env.Valid) (found : env.package? application = some shape)
    (witnessRef : witnessTerm.result.reference = some reference)
    (fieldTypes : Typing.indexedFields (fieldTerms.map Term.result) = some applications)
    (accepted : Typing.HasType env functions ctx (.pack application witnessTerm fieldTerms))
    (typedWitness : ValueHasResult env world witnessValue witnessTerm.result)
    (typedFields : FieldsHaveTypes env.indexed world fields applications) :
    ∃ witness, witnessValue = .object witness ∧
      ValueHasType env world (.package witness fields) (.package application) := by
  have relation := IndexedCore.typed_package_association env functions ctx application witnessTerm fieldTerms
    shape reference applications found witnessRef fieldTypes accepted
  have denotes := typedWitness.2
  rw [witnessRef] at denotes
  obtain ⟨witness, equal, denotes⟩ := denotes
  exact ⟨witness, equal, pack_payload_semantics found (package_lookup_valid valid found) relation denotes typedFields⟩

/-- This uses the actual accepted unpack node, its exact package case and its
actual runtime payload. The source of dynamic slot freshness and preservation
through the unpack body belong to the later whole-term theorem. -/
theorem core_opening_semantics {env : Declarations} {functions : Typing.Signatures} {ctx : Typing.Context}
    {world : World} {witnessSymbol : Nat} {fieldSymbols : List Nat} {package body : Term}
    {application : Application} {shape : PackageShape} {witness : Object} {fields : List IndexedValue}
    (valid : env.Valid) (packageType : package.result.type = .package application)
    (found : env.package? application = some shape)
    (accepted : Typing.HasType env functions ctx (.unpack witnessSymbol fieldSymbols package body))
    (typed : ValueHasType env world (.package witness fields) package.result.type)
    (fresh : world witnessSymbol = none) :
    WorldExtends world (bindLocal world witnessSymbol witness) ∧
      RefDenotes env.indexed (bindLocal world witnessSymbol witness) (.local shape.witnessType witnessSymbol) witness ∧
      FieldsHaveTypes env.indexed (bindLocal world witnessSymbol witness) fields
        (shape.instantiate (.local shape.witnessType witnessSymbol)) := by
  rw [packageType] at typed
  obtain ⟨actual, actualFound, typedWitness, typedFields⟩ := typed
  have equal : actual = shape := Option.some.inj (actualFound.symm.trans found)
  subst actual
  let checkedEnv : CheckedEnvironment := ⟨env.indexed, (VastitasKernel.Indexed.Audit.validEnvironment_iff _).mpr valid.indexed⟩
  let checkedShape : CheckedPackageShape checkedEnv :=
    ⟨shape, (VastitasKernel.Indexed.Audit.validPackageShape_iff _ _).mpr (package_lookup_valid valid found)⟩
  have freshBrand : FreshBrand (Typing.contextRefs ctx) witnessSymbol := accepted.2.2.2.2.1
  obtain ⟨opening, _, exactOpening⟩ := IndexedSubstitution.openPackage_success checkedShape _ _ freshBrand
  have payload := opening_fields_semantics opening world witness fields typedWitness typedFields
  rw [exactOpening] at payload
  exact ⟨bindLocal_fresh_extends world witnessSymbol witness fresh, payload⟩

end VastitasOracle.IndexedPackageSemantics
