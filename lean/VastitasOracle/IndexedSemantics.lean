import VastitasKernel.IndexedSemantics
import VastitasOracle.IndexedCore
import VastitasOracle.IndexedPrimitives

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

theorem global_denotes (env : Indexed.Environment) (world : World) (id : DeclId)
    (valid : ObjectRef.Valid env (.global id)) :
    ∃ object, globalObject env id = some object ∧ RefDenotes env world (.global id) object := by
  obtain ⟨type, found, typeValid⟩ := valid
  change ObjectRef.type? env (.global id) = some type at found
  unfold ObjectRef.type? at found
  cases entry : Indexed.lookup env id <;> simp only [entry] at found
  · contradiction
  case some declaration =>
    cases declaration <;> try contradiction
    case global implementation =>
      simp only [Bind.bind, Option.bind, Pure.pure] at found
      cases marker : implementationMarker env implementation <;> simp only [marker] at found
      · contradiction
      case some base =>
        cases found
        refine ⟨⟨implementation, IndexedRuntime.baseObject⟩, by simp [globalObject, entry], ?_⟩
        refine ⟨by simp [interpretRef, globalObject, entry], ⟨implementation, base⟩, ?_, typeValid, ?_⟩
        · simp [ObjectRef.type?, entry, marker]
        · unfold implementationMarker at marker
          cases concrete : Indexed.lookup env implementation <;> simp only [concrete] at marker <;> try contradiction
          case some decl =>
            cases decl <;> simp only at marker <;> try contradiction
            case implementation coefficient representation capabilities =>
              cases marker
              simp [ObjectType.implementations, Indexed.domain, concrete, implementationMarker]

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

def PrimitiveOutcome (env : Indexed.Environment) (world : World) (binding : PrimitiveBinding)
    (values : List Value) (output : ValueType) : Prop :=
  ∃ after value, evalPrimitive env binding values = some value ∧ WorldExtends world after ∧
    PrimitiveValueHasType env after value output

theorem descriptor_total {env : Indexed.Environment} {world : World} {implementation : DeclId}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.descriptor implementation) allowed brand [.natural] output)
    (typed : PrimitiveValuesHaveTypes env world values [.natural]) (fresh : world brand = none) :
    PrimitiveOutcome env world (.descriptor implementation) values output := by
  obtain ⟨value, rfl, operandTyped⟩ := primitive_single typed
  obtain ⟨dimension, rfl⟩ := primitive_natural operandTyped
  obtain ⟨type, found, _, rfl⟩ := rule.association
  have valid : type.Valid env := rule.resultValid.1
  have objectTyped := descriptor_typed found valid dimension
  refine ⟨bindLocal world brand ⟨implementation, IndexedRuntime.descriptor dimension⟩,
    .object ⟨implementation, IndexedRuntime.descriptor dimension⟩, rfl,
    bindLocal_fresh_extends world brand _ fresh, objectTyped, ?_⟩
  exact bindLocal_denotes env world brand _ type objectTyped

theorem global_total {env : Indexed.Environment} {world : World} {id : DeclId}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.global id) allowed brand [] output)
    (typed : PrimitiveValuesHaveTypes env world values []) :
    PrimitiveOutcome env world (.global id) values output := by
  have empty := primitive_nil typed
  subst values
  obtain ⟨type, found, rfl⟩ := rule.association
  obtain ⟨object, computed, denotes⟩ := global_denotes env world id rule.bindingValid
  obtain ⟨actual, actualFound, objectTyped⟩ := denotes.2
  have equal : actual = type := Option.some.inj (actualFound.symm.trans found)
  subst actual
  exact ⟨world, .object object, by simp [evalPrimitive, computed], worldExtends_refl world, objectTyped, denotes⟩

theorem origin_total {env : Indexed.Environment} {world : World} {expected actual : ObjectType}
    {family base : DeclId} {ref : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.origin expected family base) allowed brand [.object actual ref] output)
    (typed : PrimitiveValuesHaveTypes env world values [.object actual ref]) :
    PrimitiveOutcome env world (.origin expected family base) values output := by
  obtain ⟨value, rfl, operandTyped⟩ := primitive_single typed
  obtain ⟨object, rfl, _, denotes⟩ := primitive_object operandTyped
  obtain ⟨_, rfl⟩ := rule.association
  have baseValid := application_ref_valid rule.resultValid (ref := .global base) (by simp [Application.refs])
  obtain ⟨baseObject, computed, baseDenotes⟩ := global_denotes env world base baseValid
  refine ⟨world, .indexed (.point ⟨object, baseObject⟩), ?_, worldExtends_refl world, ?_⟩
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
  obtain ⟨_, rfl⟩ := rule.association
  refine ⟨world, .indexed (.morphism ⟨object, object⟩), rfl, worldExtends_refl world, rule.resultValid, ?_⟩
  simpa only [rule.bindingValid.2.1] using And.intro denotes denotes

theorem dimension_total {env : Indexed.Environment} {world : World} {expected actual : ObjectType}
    {ref : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.dimension expected) allowed brand [.object actual ref] output)
    (typed : PrimitiveValuesHaveTypes env world values [.object actual ref]) :
    PrimitiveOutcome env world (.dimension expected) values output := by
  obtain ⟨value, rfl, operandTyped⟩ := primitive_single typed
  obtain ⟨object, rfl, _, _⟩ := primitive_object operandTyped
  obtain ⟨_, rfl⟩ := rule.association
  exact ⟨world, .natural object.descriptor.dimension, rfl, worldExtends_refl world, True.intro⟩

theorem compose_total {env : Indexed.Environment} {world : World} {family gf ff : DeclId}
    {middle target source other : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.compose family) allowed brand
      [.indexed ⟨gf, [.object middle, .object target]⟩, .indexed ⟨ff, [.object source, .object other]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨gf, [.object middle, .object target]⟩, .indexed ⟨ff, [.object source, .object other]⟩]) :
    PrimitiveOutcome env world (.compose family) values output := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := rule.association
  obtain ⟨left, right, rfl, leftTyped, rightTyped⟩ := primitive_pair typed
  obtain ⟨after, rfl, _, targetDenotes⟩ := primitive_morphism rule.bindingValid leftTyped
  obtain ⟨before, rfl, sourceDenotes, _⟩ := primitive_morphism rule.bindingValid rightTyped
  refine ⟨world, .indexed (.morphism ⟨before.source, after.target⟩), rfl, worldExtends_refl world, rule.resultValid, ?_⟩
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
  obtain ⟨rfl, rfl, rfl, rfl⟩ := rule.association
  obtain ⟨left, right, rfl, leftTyped, rightTyped⟩ := primitive_pair typed
  obtain ⟨map, rfl, _, targetDenotes⟩ := primitive_morphism rule.bindingValid.1 leftTyped
  obtain ⟨point, rfl, _, testDenotes⟩ := primitive_point rule.bindingValid.2 rightTyped
  refine ⟨world, .indexed (.point ⟨map.target, point.source⟩), rfl, worldExtends_refl world, rule.resultValid, ?_⟩
  simpa only [rule.bindingValid.2] using And.intro targetDenotes testDenotes

/-- Every accepted registry operation has a typed runtime value. The only
world mutation is allocation of a fresh local object brand. Whole-term proofs
must establish that freshness from the module's allocation audit. -/
theorem primitive_total_and_typed {env : Indexed.Environment} {world : World} {binding : PrimitiveBinding}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {arguments : List ValueType} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env binding allowed brand arguments output)
    (typed : PrimitiveValuesHaveTypes env world values arguments) (fresh : PrimitiveFresh binding world brand) :
    PrimitiveOutcome env world binding values output := by
  have association := rule.association
  unfold PrimitiveAssociation at association
  split at association
  all_goals first
    | exact descriptor_total rule typed fresh
    | exact global_total rule typed
    | exact origin_total rule typed
    | exact identity_total rule typed
    | exact dimension_total rule typed
    | exact compose_total rule typed
    | exact apply_total rule typed
    | contradiction


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
      cases declaration <;> simp [globalObject, entry] at computed
      case global implementation => cases computed; rfl

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
  · contradiction

end VastitasOracle.IndexedSemantics
