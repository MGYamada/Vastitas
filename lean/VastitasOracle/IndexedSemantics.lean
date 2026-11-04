import VastitasKernel.IndexedSemantics
import VastitasOracle.IndexedCore
import VastitasOracle.IndexedPrimitives
import VastitasOracle.IndexedAssociations
import VastitasOracle.SmoothPrimitives
import VastitasOracle.SmoothFibers
import VastitasOracle.SmoothMetricForms

/-! Runtime-value obligations for the actual indexed Core and its closed
primitive registry. These lemmas do not yet prove whole-term typed evaluation,
source refinement, native code generation or mathematical geometric axioms. -/
namespace VastitasOracle.IndexedSemantics
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics

theorem object_upcast {env : Indexed.Environment} {object : Object} {actual expected : ObjectType}
    (typed : ObjectHasType env object actual) (refines : actual.Refines env expected) :
    ObjectHasType env object expected := ⟨refines.2.1, refines.2.2.2 _ typed.2⟩

theorem denotes_unique {env : Indexed.Environment} {world : World} {ref : Indexed.ObjectRef} {left right : Object}
    (hl : RefDenotes env world ref left) (hr : RefDenotes env world ref right) : left = right :=
  Option.some.inj (hl.1.symm.trans hr.1)

theorem bindLocal_denotes (env : Indexed.Environment) (world : World) (brand : Nat)
    (object : Object) (type : ObjectType) (typed : ObjectHasType env object type) :
    RefDenotes env (bindLocal world brand object) (.local type brand) object :=
  ⟨by simp [interpretRef, bindLocal], type, rfl, typed⟩

theorem worldExtends_refl (world : World) : WorldExtends world world := fun _ _ found => found

theorem worldExtends_trans {first second third : World}
    (h₁ : WorldExtends first second) (h₂ : WorldExtends second third) : WorldExtends first third :=
  fun brand object found => h₂ brand object (h₁ brand object found)

theorem bindLocal_fresh_extends (world : World) (brand : Nat) (object : Object)
    (fresh : world brand = none) : WorldExtends world (bindLocal world brand object) := by
  intro other previous found
  by_cases equal : other = brand
  · subst other
    rw [fresh] at found
    contradiction
  · simpa only [bindLocal, ite_eq_right equal] using found

theorem denotes_of_worldExtends {env : Indexed.Environment} {before after : World}
    (extension : WorldExtends before after) {ref : Indexed.ObjectRef} {object : Object}
    (denotes : RefDenotes env before ref object) : RefDenotes env after ref object := by
  refine ⟨?_, denotes.2⟩
  cases ref with
  | global id => exact denotes.1
  | «local» type brand => exact extension brand object denotes.1

theorem indexed_of_worldExtends {env : Indexed.Environment} {before after : World}
    (extension : WorldExtends before after) {value : IndexedValue} {application : Application}
    (typed : IndexedHasType env before value application) : IndexedHasType env after value application := by
  rcases typed with ⟨valid, typed⟩
  refine ⟨valid, ?_⟩
  split at typed
  · intro ref member
    obtain ⟨object, denotes⟩ := typed ref member
    exact ⟨object, denotes_of_worldExtends extension denotes⟩
  · exact ⟨denotes_of_worldExtends extension typed.1, denotes_of_worldExtends extension typed.2⟩
  · exact ⟨denotes_of_worldExtends extension typed.1, denotes_of_worldExtends extension typed.2⟩
  · intro ref member
    obtain ⟨object, denotes⟩ := typed ref member
    exact ⟨object, denotes_of_worldExtends extension denotes⟩
  · exact typed
  · exact typed
  · exact typed
  · contradiction

theorem value_of_worldExtends {env : Declarations} {before after : World}
    (extension : WorldExtends before after) {value : Value} {type : DataType}
    (typed : ValueHasType env before value type) : ValueHasType env after value type := by
  unfold ValueHasType at typed ⊢
  split at typed <;> first | exact typed | exact indexed_of_worldExtends extension typed

theorem result_of_worldExtends {env : Declarations} {before after : World}
    (extension : WorldExtends before after) {value : Value} {result : Result}
    (typed : ValueHasResult env before value result) : ValueHasResult env after value result := by
  refine ⟨value_of_worldExtends extension typed.1, ?_⟩
  cases reference : result.reference with
  | none => trivial
  | some ref =>
      obtain ⟨object, equal, denotes⟩ := (show ValueHasRef env.indexed before value (some ref) from reference ▸ typed.2)
      exact ⟨object, equal, denotes_of_worldExtends extension denotes⟩

private theorem implementation_member {env : Indexed.Environment} {implementation base : DeclId}
    (marker : implementationMarker env implementation = some base) :
    implementation ∈ ObjectType.implementations env ⟨implementation, base⟩ := by
  unfold implementationMarker at marker
  cases concrete : Indexed.lookup env implementation <;> simp only [concrete] at marker <;> try contradiction
  case some decl =>
    cases decl <;> simp only at marker <;> try contradiction
    case implementation coefficient representation capabilities =>
      cases marker
      simp [ObjectType.implementations, Indexed.domain, concrete, implementationMarker]

theorem global_denotes (env : Indexed.Environment) (world : World) (id : DeclId)
    (valid : ObjectRef.Valid env (.global id)) :
    ∃ object, globalObject env id = some object ∧ RefDenotes env world (.global id) object := by
  obtain ⟨type, found, typeValid⟩ := valid
  change ObjectRef.type? env (.global id) = some type at found
  unfold ObjectRef.type? at found
  cases impl : (Indexed.lookup env id).bind Declaration.objectImplementation? with
  | none => simp [impl] at found
  | some implementation =>
    cases marker : implementationMarker env implementation with
    | none => simp [impl, marker] at found
    | some base =>
      simp [impl, marker, Bind.bind, Pure.pure] at found
      subst found
      have object : globalObject env id = some ⟨implementation, IndexedRuntime.baseObject⟩ := by
        simp [globalObject, impl]
      refine ⟨_, object, by simp [interpretRef, object], ⟨implementation, base⟩, ?_, typeValid,
        implementation_member marker⟩
      simp [ObjectRef.type?, impl, marker]

theorem descriptor_typed {env : Indexed.Environment} {implementation : DeclId} {type : ObjectType}
    (found : implementationType env implementation = some type) (valid : type.Valid env) (dimension : Nat) :
    ObjectHasType env ⟨implementation, IndexedRuntime.descriptor dimension⟩ type := by
  unfold implementationType at found
  cases marker : implementationMarker env implementation <;> simp only [marker, Option.map_none, Option.map_some] at found
  · contradiction
  case some base =>
    cases found
    refine ⟨valid, ?_⟩
    unfold implementationMarker at marker
    cases entry : Indexed.lookup env implementation <;> simp only [entry] at marker <;> try contradiction
    case some declaration =>
      cases declaration <;> simp only at marker <;> try contradiction
      case implementation coefficient representation capabilities =>
        cases marker
        simp [ObjectType.implementations, Indexed.domain, entry, implementationMarker]


theorem application_ref_valid {env : Indexed.Environment} {application : Application}
    (valid : application.Valid env) {ref : Indexed.ObjectRef} (member : ref ∈ application.refs) :
    ref.Valid env := by
  obtain ⟨family, _, arity, accepted, _⟩ := valid
  obtain ⟨index, inIndices, projects⟩ := List.mem_filterMap.mp member
  cases index <;> simp only at projects <;> try contradiction
  case object actual =>
    cases projects
    have inMap : Index.object ref ∈ (family.parameters.zip application.indices).map Prod.snd := by
      rw [List.map_snd_zip (Nat.le_of_eq arity.symm)]
      exact inIndices
    obtain ⟨⟨parameter, index⟩, inZip, equal⟩ := List.mem_map.mp inMap
    dsimp at equal
    subst index
    have accepts := accepted (parameter, .object ref) inZip
    cases parameter <;> simp only [Indexed.Parameter.Accepts] at accepts <;> try contradiction
    case object domain =>
      obtain ⟨type, found, typed, _⟩ := accepts
      exact ⟨type, found, typed⟩

theorem primitive_nil {env : Indexed.Environment} {world : World} {values : List Value}
    (typed : PrimitiveValuesHaveTypes env world values []) : values = [] := by
  cases values <;> simp_all [PrimitiveValuesHaveTypes]

theorem primitive_single {env : Indexed.Environment} {world : World} {values : List Value} {type : ValueType}
    (typed : PrimitiveValuesHaveTypes env world values [type]) :
    ∃ value, values = [value] ∧ PrimitiveValueHasType env world value type := by
  cases values with
  | nil => contradiction
  | cons value rest =>
      have empty := primitive_nil typed.2
      exact ⟨value, by simp [empty], typed.1⟩

theorem primitive_pair {env : Indexed.Environment} {world : World} {values : List Value} {first second : ValueType}
    (typed : PrimitiveValuesHaveTypes env world values [first, second]) :
    ∃ left right, values = [left, right] ∧ PrimitiveValueHasType env world left first ∧
      PrimitiveValueHasType env world right second := by
  cases values with
  | nil => contradiction
  | cons left rest =>
      obtain ⟨right, equal, typedRight⟩ := primitive_single typed.2
      exact ⟨left, right, by simp [equal], typed.1, typedRight⟩

theorem primitive_natural {env : Indexed.Environment} {world : World} {value : Value}
    (typed : PrimitiveValueHasType env world value .natural) : ∃ n, value = .natural n := by
  cases value <;> simp_all [PrimitiveValueHasType]

theorem primitive_object {env : Indexed.Environment} {world : World} {value : Value}
    {type : ObjectType} {ref : Indexed.ObjectRef}
    (typed : PrimitiveValueHasType env world value (.object type ref)) :
    ∃ object, value = .object object ∧ ObjectHasType env object type ∧ RefDenotes env world ref object := by
  cases value <;> simp_all [PrimitiveValueHasType]

theorem primitive_point {env : Indexed.Environment} {world : World} {value : Value}
    {family : DeclId} {target source : Indexed.ObjectRef} (representation : familyRepresentation env family = some .point)
    (typed : PrimitiveValueHasType env world value (.indexed ⟨family, [.object target, .object source]⟩)) :
    ∃ point, value = .indexed (.point point) ∧ RefDenotes env world target point.target ∧ RefDenotes env world source point.source := by
  cases value <;> simp only [PrimitiveValueHasType] at typed <;> try contradiction
  case indexed value => cases value <;> simp_all [IndexedHasType]

theorem primitive_morphism {env : Indexed.Environment} {world : World} {value : Value}
    {family : DeclId} {source target : Indexed.ObjectRef} (representation : familyRepresentation env family = some .morphism)
    (typed : PrimitiveValueHasType env world value (.indexed ⟨family, [.object source, .object target]⟩)) :
    ∃ map, value = .indexed (.morphism map) ∧ RefDenotes env world source map.source ∧ RefDenotes env world target map.target := by
  cases value <;> simp only [PrimitiveValueHasType] at typed <;> try contradiction
  case indexed value => cases value <;> simp_all [IndexedHasType]

/-- Logical world update of the closed registry. Runtime execution does not
inspect these brands; the update records only a descriptor's declared fresh slot. -/
def primitiveWorld (world : World) (binding : PrimitiveBinding) (output : ValueType) (value : Value) : World :=
  match binding, output, value with
  | .descriptor _, .object _ (.local _ brand), .object object => bindLocal world brand object
  | _, _, _ => world

def PrimitiveOutcome (env : Indexed.Environment) (world : World) (binding : PrimitiveBinding)
    (values : List Value) (output : ValueType) : Prop :=
  ∃ after value, evalPrimitive env binding values = some value ∧ WorldExtends world after ∧
    PrimitiveValueHasType env after value output ∧ after = primitiveWorld world binding output value

theorem descriptor_total {env : Indexed.Environment} {world : World} {implementation : DeclId}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.descriptor implementation) allowed brand [.natural] output)
    (typed : PrimitiveValuesHaveTypes env world values [.natural]) (fresh : world brand = none) :
    PrimitiveOutcome env world (.descriptor implementation) values output := by
  obtain ⟨value, rfl, operandTyped⟩ := primitive_single typed
  obtain ⟨dimension, rfl⟩ := primitive_natural operandTyped
  obtain ⟨type, found, _, rfl⟩ := IndexedAssociations.descriptor_association.mp rule.association
  have valid : type.Valid env := rule.resultValid.1
  have objectTyped := descriptor_typed found valid dimension
  refine ⟨bindLocal world brand ⟨implementation, IndexedRuntime.descriptor dimension⟩,
    .object ⟨implementation, IndexedRuntime.descriptor dimension⟩, rfl,
    bindLocal_fresh_extends world brand _ fresh, ⟨objectTyped, ?_⟩, rfl⟩
  exact bindLocal_denotes env world brand _ type objectTyped

theorem global_total {env : Indexed.Environment} {world : World} {id : DeclId}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.global id) allowed brand [] output)
    (typed : PrimitiveValuesHaveTypes env world values []) :
    PrimitiveOutcome env world (.global id) values output := by
  have empty := primitive_nil typed
  subst values
  obtain ⟨type, found, rfl⟩ := IndexedAssociations.global_association.mp rule.association
  obtain ⟨object, computed, denotes⟩ := global_denotes env world id rule.bindingValid.2
  obtain ⟨actual, actualFound, objectTyped⟩ := denotes.2
  have equal : actual = type := Option.some.inj (actualFound.symm.trans found)
  subst actual
  exact ⟨world, .object object, by simp [evalPrimitive, computed], worldExtends_refl world, ⟨objectTyped, denotes⟩, rfl⟩

theorem origin_total {env : Indexed.Environment} {world : World} {expected actual : ObjectType}
    {family base : DeclId} {ref : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.origin expected family base) allowed brand [.object actual ref] output)
    (typed : PrimitiveValuesHaveTypes env world values [.object actual ref]) :
    PrimitiveOutcome env world (.origin expected family base) values output := by
  obtain ⟨value, rfl, operandTyped⟩ := primitive_single typed
  obtain ⟨object, rfl, _, denotes⟩ := primitive_object operandTyped
  obtain ⟨_, rfl⟩ := IndexedAssociations.origin_association.mp rule.association
  have baseValid := application_ref_valid rule.resultValid (ref := .global base) (by simp [Application.refs])
  obtain ⟨baseObject, computed, baseDenotes⟩ := global_denotes env world base baseValid
  refine ⟨world, .indexed (.point ⟨object, baseObject⟩), ?_, worldExtends_refl world, ?_, rfl⟩
  · simp [evalPrimitive, computed]
  · exact ⟨rule.resultValid, by simpa only [rule.bindingValid.2.1] using And.intro denotes baseDenotes⟩

theorem identity_total {env : Indexed.Environment} {world : World} {expected actual : ObjectType}
    {family : DeclId} {ref : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.identity expected family) allowed brand [.object actual ref] output)
    (typed : PrimitiveValuesHaveTypes env world values [.object actual ref]) :
    PrimitiveOutcome env world (.identity expected family) values output := by
  obtain ⟨value, rfl, operandTyped⟩ := primitive_single typed
  obtain ⟨object, rfl, _, denotes⟩ := primitive_object operandTyped
  obtain ⟨_, rfl⟩ := IndexedAssociations.identity_association.mp rule.association
  refine ⟨world, .indexed (.morphism ⟨object, object⟩), rfl, worldExtends_refl world, ⟨rule.resultValid, ?_⟩, rfl⟩
  simpa only [rule.bindingValid.2.1] using And.intro denotes denotes

theorem dimension_total {env : Indexed.Environment} {world : World} {expected actual : ObjectType}
    {ref : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.dimension expected) allowed brand [.object actual ref] output)
    (typed : PrimitiveValuesHaveTypes env world values [.object actual ref]) :
    PrimitiveOutcome env world (.dimension expected) values output := by
  obtain ⟨value, rfl, operandTyped⟩ := primitive_single typed
  obtain ⟨object, rfl, _, _⟩ := primitive_object operandTyped
  obtain ⟨_, rfl⟩ := IndexedAssociations.dimension_association.mp rule.association
  exact ⟨world, .natural object.descriptor.dimension, rfl, worldExtends_refl world, True.intro, rfl⟩

theorem compose_total {env : Indexed.Environment} {world : World} {family gf ff : DeclId}
    {middle target source other : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.compose family) allowed brand
      [.indexed ⟨gf, [.object middle, .object target]⟩, .indexed ⟨ff, [.object source, .object other]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨gf, [.object middle, .object target]⟩, .indexed ⟨ff, [.object source, .object other]⟩]) :
    PrimitiveOutcome env world (.compose family) values output := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := IndexedAssociations.compose_association.mp rule.association
  obtain ⟨left, right, rfl, leftTyped, rightTyped⟩ := primitive_pair typed
  obtain ⟨after, rfl, _, targetDenotes⟩ := primitive_morphism rule.bindingValid leftTyped
  obtain ⟨before, rfl, sourceDenotes, _⟩ := primitive_morphism rule.bindingValid rightTyped
  refine ⟨world, .indexed (.morphism ⟨before.source, after.target⟩), rfl, worldExtends_refl world, ⟨rule.resultValid, ?_⟩, rfl⟩
  have representation : familyRepresentation env ff = some .morphism := rule.bindingValid
  simpa only [representation] using And.intro sourceDenotes targetDenotes

theorem apply_total {env : Indexed.Environment} {world : World} {maps points mf pf : DeclId}
    {source target other test : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.apply maps points) allowed brand
      [.indexed ⟨mf, [.object source, .object target]⟩, .indexed ⟨pf, [.object other, .object test]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨mf, [.object source, .object target]⟩, .indexed ⟨pf, [.object other, .object test]⟩]) :
    PrimitiveOutcome env world (.apply maps points) values output := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := IndexedAssociations.apply_association.mp rule.association
  obtain ⟨left, right, rfl, leftTyped, rightTyped⟩ := primitive_pair typed
  obtain ⟨map, rfl, _, targetDenotes⟩ := primitive_morphism rule.bindingValid.1 leftTyped
  obtain ⟨point, rfl, _, testDenotes⟩ := primitive_point rule.bindingValid.2 rightTyped
  refine ⟨world, .indexed (.point ⟨map.target, point.source⟩), rfl, worldExtends_refl world, ⟨rule.resultValid, ?_⟩, rfl⟩
  simpa only [rule.bindingValid.2] using And.intro targetDenotes testDenotes

/-! ### Relative morphisms over a base (Stage 2)

A relative value is an exact pullback map. Its typing obligation is that
every object index denotes, as for tokens. The checked map identities live in
the declaration audit (`VastitasOracle.AffineMorphisms`). -/

theorem relative_family {env : Indexed.Environment} {family : DeclId}
    (relative : isRelativeFamily env family = true) : familyRepresentation env family = some .relative := by
  simpa [isRelativeFamily] using relative

theorem primitive_relative {env : Indexed.Environment} {world : World} {value : Value}
    {application : Application} (representation : familyRepresentation env application.family = some .relative)
    (typed : PrimitiveValueHasType env world value (.indexed application)) :
    ∃ map, value = .indexed (.relative map) ∧ application.Valid env ∧
      ∀ ref ∈ application.refs, ∃ object, RefDenotes env world ref object := by
  cases value <;> simp only [PrimitiveValueHasType] at typed <;> try contradiction
  case indexed value =>
    obtain ⟨valid, typed⟩ := typed
    cases value <;> simp only [representation] at typed <;> try contradiction
    case relative map => exact ⟨map, rfl, valid, typed⟩

theorem relative_typed {env : Indexed.Environment} {world : World} {application : Application}
    {map : AlgebraRuntime.Map} (representation : familyRepresentation env application.family = some .relative)
    (valid : application.Valid env) (denote : ∀ ref ∈ application.refs, ∃ object, RefDenotes env world ref object) :
    PrimitiveValueHasType env world (.indexed (.relative map)) (.indexed application) := by
  refine ⟨valid, ?_⟩
  simp only [representation]
  exact denote

/-- Global indices of a valid application denote in every world. -/
theorem global_refs_denote {env : Indexed.Environment} {world : World} {application : Application}
    (valid : application.Valid env) {ref : Indexed.ObjectRef} (member : ref ∈ application.refs)
    {id : DeclId} (global : ref = .global id) : ∃ object, RefDenotes env world ref object := by
  subst global
  obtain ⟨object, _, denotes⟩ := global_denotes env world id (application_ref_valid valid member)
  exact ⟨object, denotes⟩

theorem relativeConstant_indices {env : Indexed.Environment} {application : Application}
    {map : AlgebraRuntime.Map} (valid : relativeConstantValid env application map = true) :
    ∃ x y s, application.indices = [.object (.global x), .object (.global y), .object (.global s)] := by
  unfold relativeConstantValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨_, valid⟩ := valid
  split at valid
  · rename_i x y s indices
    exact ⟨x, y, s, indices⟩
  · simp at valid

theorem relativeConstant_total {env : Indexed.Environment} {world : World} {application : Application}
    {map : AlgebraRuntime.Map} {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType}
    {values : List Value}
    (rule : PrimitiveTyped env (.relativeConstant application map) allowed brand [] output)
    (typed : PrimitiveValuesHaveTypes env world values []) :
    PrimitiveOutcome env world (.relativeConstant application map) values output := by
  have empty := primitive_nil typed
  subst values
  have association : output = .indexed application := (IndexedAssociations.relativeConstant_association.mp rule.association).symm
  subst association
  have bindingValid : relativeConstantValid env application map = true := rule.bindingValid
  have relative : isRelativeFamily env application.family = true := by
    unfold relativeConstantValid at bindingValid
    simp only [Bool.and_eq_true] at bindingValid
    exact bindingValid.1.1
  obtain ⟨x, y, s, indices⟩ := relativeConstant_indices bindingValid
  have valid : application.Valid env := rule.resultValid
  refine ⟨world, .indexed (.relative map), rfl, worldExtends_refl world,
    relative_typed (relative_family relative) valid ?_, rfl⟩
  intro ref member
  have global : ref = .global x ∨ ref = .global y ∨ ref = .global s := by
    simpa [Application.refs, indices] using member
  rcases global with global | global | global <;> exact global_refs_denote valid member global

theorem relativeCompose_total {env : Indexed.Environment} {world : World} {family gf ff : DeclId}
    {middle target base source middle' base' : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.relativeCompose family) allowed brand
      [.indexed ⟨gf, [.object middle, .object target, .object base]⟩,
        .indexed ⟨ff, [.object source, .object middle', .object base']⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨gf, [.object middle, .object target, .object base]⟩,
        .indexed ⟨ff, [.object source, .object middle', .object base']⟩]) :
    PrimitiveOutcome env world (.relativeCompose family) values output := by
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := IndexedAssociations.relativeCompose_association.mp rule.association
  have relative := relative_family rule.bindingValid
  obtain ⟨left, right, rfl, leftTyped, rightTyped⟩ := primitive_pair typed
  obtain ⟨after, rfl, _, afterDenotes⟩ := primitive_relative relative leftTyped
  obtain ⟨before, rfl, _, beforeDenotes⟩ := primitive_relative relative rightTyped
  refine ⟨world, .indexed (.relative (AlgebraRuntime.Map.compose after before)), rfl, worldExtends_refl world,
    relative_typed relative rule.resultValid ?_, rfl⟩
  intro ref member
  simp only [Application.refs, List.filterMap_cons, List.filterMap_nil, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact beforeDenotes _ (by simp [Application.refs])
  · exact afterDenotes _ (by simp [Application.refs])
  · exact afterDenotes _ (by simp [Application.refs])

theorem relativeView_total {env : Indexed.Environment} {world : World} {family origin to f : DeclId}
    {source target base : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.relativeView family origin to) allowed brand
      [.indexed ⟨f, [.object source, .object target, .object base]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨f, [.object source, .object target, .object base]⟩]) :
    PrimitiveOutcome env world (.relativeView family origin to) values output := by
  obtain ⟨rfl, rfl, rfl⟩ := IndexedAssociations.relativeView_association.mp rule.association
  have relative := relative_family rule.bindingValid.1
  obtain ⟨value, rfl, valueTyped⟩ := primitive_single typed
  obtain ⟨map, rfl, _, denotes⟩ := primitive_relative relative valueTyped
  have valid := rule.resultValid
  refine ⟨world, .indexed (.relative map), rfl, worldExtends_refl world, relative_typed relative valid ?_, rfl⟩
  intro ref member
  have cases : ref = source ∨ ref = target ∨ ref = .global to := by
    simpa [Application.refs] using member
  rcases cases with rfl | rfl | global
  · exact denotes _ (by simp [Application.refs])
  · exact denotes _ (by simp [Application.refs])
  · exact global_refs_denote valid member global

theorem relativeEqual_total {env : Indexed.Environment} {world : World} {family : DeclId}
    {left right : Application} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.relativeEqual family) allowed brand [.indexed left, .indexed right] output)
    (typed : PrimitiveValuesHaveTypes env world values [.indexed left, .indexed right]) :
    PrimitiveOutcome env world (.relativeEqual family) values output := by
  obtain ⟨family_eq, _, rfl, rfl⟩ := IndexedAssociations.relativeEqual_association.mp rule.association
  have relative : familyRepresentation env left.family = some .relative :=
    family_eq ▸ relative_family (rule.bindingValid : isRelativeFamily env family = true)
  obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ := primitive_pair typed
  obtain ⟨a, rfl, _⟩ := primitive_relative relative firstTyped
  obtain ⟨b, rfl, _⟩ := primitive_relative relative secondTyped
  exact ⟨world, .boolean (AlgebraRuntime.Map.same a b), rfl, worldExtends_refl world, trivial, rfl⟩

theorem relativeCoefficient_total {env : Indexed.Environment} {world : World}
    {family source target f x y : DeclId} {coordinate : Nat} {monomial : List Nat}
    {base : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.relativeCoefficient family source target coordinate monomial) allowed brand
      [.indexed ⟨f, [.object (.global x), .object (.global y), .object base]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨f, [.object (.global x), .object (.global y), .object base]⟩]) :
    PrimitiveOutcome env world (.relativeCoefficient family source target coordinate monomial) values output := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := IndexedAssociations.relativeCoefficient_association.mp rule.association
  have relative := relative_family rule.bindingValid.1
  obtain ⟨value, rfl, valueTyped⟩ := primitive_single typed
  obtain ⟨map, rfl, _⟩ := primitive_relative relative valueTyped
  exact ⟨world, .pairInt (map.coefficient coordinate monomial).1 (map.coefficient coordinate monomial).2,
    rfl, worldExtends_refl world, trivial, rfl⟩

theorem integer_values {env : Indexed.Environment} {world : World} :
    ∀ {values : List Value} {count : Nat},
      PrimitiveValuesHaveTypes env world values ((List.range count).map fun _ => .integer) →
      ∃ coordinates, values.mapM Value.integer? = some coordinates
  | [], _, _ => ⟨[], rfl⟩
  | value :: rest, count, typed => by
    cases count with
    | zero => simp [PrimitiveValuesHaveTypes] at typed
    | succ n =>
      rw [List.range_succ_eq_map, List.map_cons, List.map_map] at typed
      obtain ⟨head, tail⟩ := typed
      cases value <;> simp only [PrimitiveValueHasType] at head
      case integer v =>
        have shifted : ((List.range n).map ((fun _ => ValueType.integer) ∘ Nat.succ)) =
            (List.range n).map fun _ => ValueType.integer := by simp [Function.comp_def]
        rw [shifted] at tail
        obtain ⟨coordinates, found⟩ := integer_values tail
        exact ⟨v :: coordinates, by simp [found, Value.integer?]⟩

theorem relativeIntPoint_total {env : Indexed.Environment} {world : World} {family object base : DeclId}
    {arguments : List ValueType} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.relativeIntPoint family object base) allowed brand arguments output)
    (typed : PrimitiveValuesHaveTypes env world values arguments) :
    PrimitiveOutcome env world (.relativeIntPoint family object base) values output := by
  obtain ⟨rfl, rfl⟩ := IndexedAssociations.relativeIntPoint_association.mp rule.association
  have relative := relative_family rule.bindingValid.1
  obtain ⟨coordinates, found⟩ := integer_values typed
  have valid := rule.resultValid
  refine ⟨world, .indexed (.relative (AlgebraRuntime.Map.intPoint coordinates)), ?_, worldExtends_refl world,
    relative_typed relative valid ?_, rfl⟩
  · simp [evalPrimitive, intPointValue, found]
  · intro ref member
    have cases : ref = .global base ∨ ref = .global object ∨ ref = .global base := by
      simpa [Application.refs] using member
    rcases cases with global | global | global <;> exact global_refs_denote valid member global

theorem relativePair_total {env : Indexed.Environment} {world : World} {family fiber lf rf : DeclId}
    {source left base source' right base' : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.relativePair family fiber) allowed brand
      [.indexed ⟨lf, [.object source, .object left, .object base]⟩,
        .indexed ⟨rf, [.object source', .object right, .object base']⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨lf, [.object source, .object left, .object base]⟩,
        .indexed ⟨rf, [.object source', .object right, .object base']⟩]) :
    PrimitiveOutcome env world (.relativePair family fiber) values output := by
  obtain ⟨rfl, rfl, rfl, rfl, _, rfl⟩ := IndexedAssociations.relativePair_association.mp rule.association
  have relative := relative_family rule.bindingValid.1
  obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ := primitive_pair typed
  obtain ⟨l, rfl, _, leftDenotes⟩ := primitive_relative relative firstTyped
  obtain ⟨r, rfl, _, _⟩ := primitive_relative relative secondTyped
  have valid := rule.resultValid
  refine ⟨world, .indexed (.relative (AlgebraRuntime.Map.pair l r)), rfl, worldExtends_refl world,
    relative_typed relative valid ?_, rfl⟩
  intro ref member
  have cases : ref = source ∨ ref = .global fiber ∨ ref = base := by
    simpa [Application.refs] using member
  rcases cases with rfl | global | rfl
  · exact leftDenotes _ (by simp [Application.refs])
  · exact global_refs_denote valid member global
  · exact leftDenotes _ (by simp [Application.refs])

/-- A smooth primitive leaves the world unchanged. -/
theorem smooth_outcome {env : Indexed.Environment} {world : World} {binding : PrimitiveBinding}
    {values : List Value} {output : ValueType}
    (unchanged : ∀ value, primitiveWorld world binding output value = world)
    (outcome : SmoothPrimitives.SmoothOutcome env world binding values output) :
    PrimitiveOutcome env world binding values output := by
  obtain ⟨value, evaluated, typed⟩ := outcome
  exact ⟨world, value, evaluated, worldExtends_refl world, typed, (unchanged value).symm⟩

/-- Every accepted registry operation has a typed runtime value. The only
world mutation is allocation of a fresh local object brand. Whole-term proofs
must establish that freshness from the module's allocation audit. -/
theorem primitive_total_and_typed {env : Indexed.Environment} {world : World} {binding : PrimitiveBinding}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {arguments : List ValueType} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env binding allowed brand arguments output)
    (typed : PrimitiveValuesHaveTypes env world values arguments) (fresh : PrimitiveFresh binding world brand) :
    PrimitiveOutcome env world binding values output := by
  cases binding with
  | descriptor implementation =>
    obtain rfl := IndexedAssociations.descriptor_shape rule.association
    exact descriptor_total rule typed fresh
  | global id =>
    obtain rfl := IndexedAssociations.global_shape rule.association
    exact global_total rule typed
  | origin domain family base =>
    obtain ⟨actual, ref, rfl⟩ := IndexedAssociations.origin_shape rule.association
    exact origin_total rule typed
  | identity domain family =>
    obtain ⟨actual, ref, rfl⟩ := IndexedAssociations.identity_shape rule.association
    exact identity_total rule typed
  | dimension domain =>
    obtain ⟨actual, ref, rfl⟩ := IndexedAssociations.dimension_shape rule.association
    exact dimension_total rule typed
  | compose family =>
    obtain ⟨middle, target, source, other, rfl⟩ := IndexedAssociations.compose_shape rule.association
    exact compose_total rule typed
  | apply maps points =>
    obtain ⟨source, target, other, test, rfl⟩ := IndexedAssociations.apply_shape rule.association
    exact apply_total rule typed
  | relativeConstant application map =>
    obtain rfl := IndexedAssociations.relativeConstant_shape rule.association
    exact relativeConstant_total rule typed
  | relativeCompose family =>
    obtain ⟨middle, target, base, source, middle', base', rfl⟩ :=
      IndexedAssociations.relativeCompose_shape rule.association
    exact relativeCompose_total rule typed
  | relativeView family origin to =>
    obtain ⟨source, target, rfl⟩ := IndexedAssociations.relativeView_shape rule.association
    exact relativeView_total rule typed
  | relativeEqual family =>
    obtain ⟨left, right, rfl⟩ := IndexedAssociations.relativeEqual_shape rule.association
    exact relativeEqual_total rule typed
  | relativeCoefficient family source target coordinate monomial =>
    obtain ⟨base, rfl⟩ := IndexedAssociations.relativeCoefficient_shape rule.association
    exact relativeCoefficient_total rule typed
  | relativeIntPoint family object base => exact relativeIntPoint_total rule typed
  | relativePair family fiber =>
    obtain ⟨source, left, base, source', right, base', rfl⟩ :=
      IndexedAssociations.relativePair_shape rule.association
    exact relativePair_total rule typed
  | relativeIso forward backward => exact absurd rule.association IndexedAssociations.relativeIso_association
  | relativeCartesian first second inverse fiber =>
    exact absurd rule.association IndexedAssociations.relativeCartesian_association
  | smoothConstant application map =>
    obtain rfl := IndexedAssociations.smoothConstant_shape rule.association
    exact smooth_outcome (fun _ => rfl) (SmoothPrimitives.smoothConstant_total rule typed)
  | smoothCompose family =>
    obtain ⟨middle, target, source, other, rfl⟩ := IndexedAssociations.smoothCompose_shape rule.association
    exact smooth_outcome (fun _ => rfl) (SmoothPrimitives.smoothCompose_total rule typed)
  | smoothEqual family =>
    obtain ⟨left, right, rfl⟩ := IndexedAssociations.smoothEqual_shape rule.association
    exact smooth_outcome (fun _ => rfl) (SmoothPrimitives.smoothEqual_total rule typed)
  | smoothIntPoint family object point =>
    exact smooth_outcome (fun _ => rfl) (SmoothPrimitives.smoothIntPoint_total rule typed)
  | smoothComposite family =>
    obtain ⟨application, rfl⟩ := IndexedAssociations.smoothComposite_shape rule.association
    exact smooth_outcome (fun _ => rfl) (SmoothPrimitives.smoothComposite_total rule typed)
  | fiberVector family smooth object =>
    obtain ⟨point, x, components, rfl⟩ := IndexedAssociations.fiberVector_shape rule.association
    exact smooth_outcome (fun _ => rfl) (SmoothFibers.fiberVector_total rule typed)
  | fiberAt family smooth =>
    obtain ⟨x, point, x', rfl⟩ := IndexedAssociations.fiberAt_shape rule.association
    exact smooth_outcome (fun _ => rfl) (SmoothFibers.fiberAt_total rule typed)
  | fiberEqual family =>
    obtain ⟨left, right, rfl⟩ := IndexedAssociations.fiberEqual_shape rule.association
    exact smooth_outcome (fun _ => rfl) (SmoothFibers.fiberEqual_total rule typed)
  | fiberComponent family object coordinate =>
    obtain rfl := IndexedAssociations.fiberComponent_shape rule.association
    exact smooth_outcome (fun _ => rfl) (SmoothFibers.fiberComponent_total rule typed)
  | fiberPairing cotangent tangent =>
    obtain ⟨x, x', rfl⟩ := IndexedAssociations.fiberPairing_shape rule.association
    exact smooth_outcome (fun _ => rfl) (SmoothFibers.fiberPairing_total rule typed)
  | cotangentPullback smooth cotangent mode =>
    obtain ⟨x, y, point, x', y', rfl⟩ := IndexedAssociations.cotangentPullback_shape rule.association
    exact smooth_outcome (fun _ => rfl) (SmoothFibers.cotangentPullback_total rule typed)
  | differential smooth cotangent line =>
    obtain ⟨x, point, x', rfl⟩ := IndexedAssociations.differential_shape rule.association
    exact smooth_outcome (fun _ => rfl) (SmoothFibers.differential_total rule typed)
  | linearize smooth tape =>
    obtain ⟨x, y, point, x', rfl⟩ := IndexedAssociations.linearize_shape rule.association
    exact smooth_outcome (fun _ => rfl) (SmoothFibers.linearize_total rule typed)
  | cotangentBackward tape cotangent =>
    obtain ⟨x, y, y', rfl⟩ := IndexedAssociations.cotangentBackward_shape rule.association
    exact smooth_outcome (fun _ => rfl) (SmoothFibers.cotangentBackward_total rule typed)
  | metricFlat metric object gram tangent cotangent =>
    obtain rfl := IndexedAssociations.metricFlat_shape rule.association
    exact smooth_outcome (fun _ => rfl) (SmoothMetricForms.metricFlat_total rule typed)
  | metricSharp metric evidence object gram inverse cotangent tangent =>
    obtain rfl := IndexedAssociations.metricSharp_shape rule.association
    exact smooth_outcome (fun _ => rfl) (SmoothMetricForms.metricSharp_total rule typed)

/-- This corollary consumes the real primitive checker's accepted record, with
the exact argument annotations and returned result. Runtime argument typing
and dynamic freshness remain explicit semantic premises. -/
theorem checked_primitive_semantics {env : CheckedEnvironment} {world : World}
    {binding : PrimitiveBinding} {allowed : List Indexed.ObjectRef} {brand : Nat} {arguments : List ValueType}
    (checked : CheckedPrimitive env binding allowed brand arguments) {values : List Value}
    (typed : PrimitiveValuesHaveTypes env.environment world values arguments)
    (fresh : PrimitiveFresh binding world brand) :
    PrimitiveOutcome env.environment world binding values checked.result :=
  primitive_total_and_typed (VastitasOracle.Indexed.checked_primitive_typed checked) typed fresh

/-- The operation theorem also applies to an actual well-typed Core node,
using that node's declaration lookup and operand/result conversions. -/
theorem core_primitive_semantics {env : Declarations} {functions : Typing.Signatures} {ctx : Typing.Context}
    {world : World} {id : DeclId} {arguments : List Core.Term} {result : Result} {binding : PrimitiveBinding}
    {operands : List ValueType} {output : ValueType} {values : List Value}
    (found : env.primitive? id = some binding)
    (input : (arguments.map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Typing.HasType env functions ctx (.primitive id arguments result))
    (typed : PrimitiveValuesHaveTypes env.indexed world values operands)
    (fresh : PrimitiveFresh binding world (Typing.primitiveBrand result)) :
    PrimitiveOutcome env.indexed world binding values output :=
  primitive_total_and_typed
    (IndexedCore.typed_primitive_contract env functions ctx id arguments result binding operands output
      found input outputType accepted) typed fresh

/-- Runtime endpoints agree at a checked composition boundary, even though
different static references may denote equal descriptors in a noninjective world. -/
theorem compose_middle_agrees {env : Indexed.Environment} {world : World}
    {family : DeclId} {middle target source : Indexed.ObjectRef} {after before : Morphism}
    (afterTyped : IndexedHasType env world (.morphism after) ⟨family, [.object middle, .object target]⟩)
    (beforeTyped : IndexedHasType env world (.morphism before) ⟨family, [.object source, .object middle]⟩) :
    after.source = before.target := by
  have representation : familyRepresentation env family = some .morphism := by
    cases found : familyRepresentation env family <;> simp [IndexedHasType, found] at afterTyped
    case some representation => cases representation <;> simp_all [IndexedHasType]
  have a := afterTyped.2
  have b := beforeTyped.2
  simp only [representation] at a b
  exact denotes_unique a.1 b.2

theorem global_object_descriptor {env : Indexed.Environment} {id : DeclId} {object : Object}
    (computed : globalObject env id = some object) : object.descriptor = IndexedRuntime.baseObject := by
  cases entry : Indexed.lookup env id with
  | none => simp [globalObject, entry] at computed
  | some declaration =>
      cases declaration <;> simp [globalObject, entry, Declaration.objectImplementation?] at computed
      case global implementation => cases computed; rfl
      case affine implementation data => cases computed; rfl
      case smoothAffine implementation coordinates => cases computed; rfl

theorem integers_erase : ∀ {values : List Value} {coordinates : List Int},
    values.mapM Value.integer? = some coordinates →
      ∃ inputs, values.mapM erasePrimitiveValue = some inputs ∧
        inputs.mapM PrimitiveRuntimeValue.integer? = some coordinates
  | [], coordinates, found => by
    simp at found
    subst found
    exact ⟨[], rfl, rfl⟩
  | value :: rest, coordinates, found => by
    cases value <;> simp [Value.integer?] at found
    case integer v =>
      cases tailFound : rest.mapM Value.integer? with
      | none => simp [tailFound] at found
      | some tail =>
        simp [tailFound] at found
        subst found
        obtain ⟨inputs, erased, runtime⟩ := integers_erase tailFound
        exact ⟨.integer v :: inputs, by simp [erasePrimitiveValue, erased],
          by simp [PrimitiveRuntimeValue.integer?, runtime]⟩

theorem intPoint_erasure {family object base : DeclId} {values : List Value} {value : Value}
    (evaluated : intPointValue values = some value) :
    ∃ inputs output, values.mapM erasePrimitiveValue = some inputs ∧
      erasePrimitiveValue value = some output ∧
      evalRuntimePrimitive (.relativeIntPoint family object base) inputs = some output := by
  unfold intPointValue at evaluated
  cases coordinates : values.mapM Value.integer? with
  | none => simp [coordinates] at evaluated
  | some list =>
    simp [coordinates] at evaluated
    subst evaluated
    obtain ⟨inputs, erased, runtime⟩ := integers_erase coordinates
    exact ⟨inputs, _, erased, rfl, by simp [evalRuntimePrimitive, intPointRuntime, runtime]⟩

/-- Successful logical registry evaluation erases to the actual IndexedRuntime
operations. This is an operation-level commuting theorem, not a proof about
generated source, Lean/C compilation, linking or hardware. -/
theorem primitive_runtime_erasure {env : Indexed.Environment} {binding : PrimitiveBinding}
    {values : List Value} {value : Value} (evaluated : evalPrimitive env binding values = some value) :
    ∃ inputs output, values.mapM erasePrimitiveValue = some inputs ∧
      erasePrimitiveValue value = some output ∧ evalRuntimePrimitive binding inputs = some output := by
  unfold evalPrimitive at evaluated
  split at evaluated
  · cases evaluated
    exact ⟨_, _, rfl, rfl, rfl⟩
  · rename_i id
    cases computed : globalObject env id with
    | none => simp [computed] at evaluated
    | some object =>
        simp only [computed, Option.map_some, Option.some.injEq] at evaluated
        subst value
        have descriptor := global_object_descriptor computed
        exact ⟨[], .object IndexedRuntime.baseObject, rfl, by simp [erasePrimitiveValue, descriptor], rfl⟩
  · rename_i domain family base object
    cases computed : globalObject env base with
    | none => simp [computed] at evaluated
    | some baseObject =>
        simp [computed] at evaluated
        subst value
        have descriptor := global_object_descriptor computed
        exact ⟨_, _, rfl, rfl, by simp [evalRuntimePrimitive, Point.erase, IndexedRuntime.origin, descriptor]⟩
  · cases evaluated
    exact ⟨_, _, rfl, rfl, rfl⟩
  · cases evaluated
    exact ⟨_, _, rfl, rfl, rfl⟩
  · cases evaluated
    exact ⟨_, _, rfl, rfl, rfl⟩
  · cases evaluated
    exact ⟨_, _, rfl, rfl, rfl⟩
  · cases evaluated
    exact ⟨_, _, rfl, rfl, rfl⟩
  · cases evaluated
    exact ⟨_, _, rfl, rfl, rfl⟩
  · cases evaluated
    exact ⟨_, _, rfl, rfl, rfl⟩
  · cases evaluated
    exact ⟨_, _, rfl, rfl, rfl⟩
  · cases evaluated
    exact ⟨_, _, rfl, rfl, rfl⟩
  · exact intPoint_erasure evaluated
  · cases evaluated
    exact ⟨_, _, rfl, rfl, rfl⟩
  · cases evaluated
    exact ⟨_, _, rfl, rfl, rfl⟩
  · cases evaluated
    exact ⟨_, _, rfl, rfl, rfl⟩
  · cases evaluated
    exact ⟨_, _, rfl, rfl, rfl⟩
  · exact SmoothPrimitives.smoothPoint_erasure evaluated
  · cases evaluated
    exact ⟨_, _, rfl, rfl, rfl⟩
  · exact SmoothFibers.fiberVector_erasure evaluated
  all_goals first
    | contradiction
    | (cases evaluated; exact ⟨_, _, rfl, rfl, rfl⟩)

end VastitasOracle.IndexedSemantics
