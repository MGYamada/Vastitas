import VastitasKernel.IndexedSemantics
import VastitasOracle.IndexedAssociations
import VastitasOracle.SmoothRuntime
import VastitasOracle.SmoothCanonical

set_option autoImplicit false

/-! Typed totality and runtime erasure of the smooth primitives (Stage 3).

A value of `Smooth<X, Y>` is a `SmoothRuntime.Program` that is well typed
between the dimensions of the declared smooth objects `X` and `Y`. Every
accepted smooth primitive returns a value of its checked result type:

- a declared map is a well-formed primitive node;
- `compose` builds the node `Program.compose after before`, whose middle
  dimensions agree because both operands name the same middle object;
- `composite` collapses a program to one well-formed map
  (`SmoothCanonical.composite_wellTyped`);
- `int_point` builds a point of `X` from `dim X` runtime integers;
- `same` returns a Boolean.

`IndexedSemantics.primitive_total_and_typed` and
`IndexedSemantics.primitive_runtime_erasure` dispatch to these lemmas. -/
namespace VastitasOracle.SmoothPrimitives

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics

/-- The value of an accepted primitive and its type. The smooth primitives
leave the world unchanged. -/
def SmoothOutcome (env : Indexed.Environment) (world : World) (binding : PrimitiveBinding)
    (values : List Value) (output : ValueType) : Prop :=
  ∃ value, evalPrimitive env binding values = some value ∧ PrimitiveValueHasType env world value output

theorem smooth_family {env : Indexed.Environment} {family : DeclId}
    (h : isSmoothFamily env family = true) : familyRepresentation env family = some .smooth := by
  unfold isSmoothFamily at h
  unfold familyRepresentation
  split at h <;> simp_all

theorem endpoints_spec {env : Indexed.Environment} {application : Application} {n m : Nat}
    (h : smoothEndpoints? env application = some (n, m)) :
    ∃ x y, application.indices = [.object (.global x), .object (.global y)] ∧
      smoothDimension? env x = some n ∧ smoothDimension? env y = some m := by
  unfold smoothEndpoints? at h
  split at h
  · rename_i x y indices
    split at h
    · rename_i n' m' hx hy
      cases h
      exact ⟨x, y, indices, hx, hy⟩
    · cases h
  · cases h

/-- The typing of a smooth program: two declared smooth objects, and a
program well typed between their dimensions. -/
theorem smooth_has_type {env : Indexed.Environment} {world : World} {program : SmoothRuntime.Program}
    {application : Application} (representation : familyRepresentation env application.family = some .smooth)
    (typed : IndexedHasType env world (.smooth program) application) :
    ∃ x y n m, application.indices = [.object (.global x), .object (.global y)] ∧
      smoothDimension? env x = some n ∧ smoothDimension? env y = some m ∧ program.wellTyped n m = true := by
  obtain ⟨_, typed⟩ := typed
  simp only [representation] at typed
  split at typed
  case h_5 =>
    rename_i program' x y heqValue _ heqIndices
    cases heqValue
    obtain ⟨n, m, hx, hy, welltyped⟩ := typed
    exact ⟨x, y, n, m, heqIndices, hx, hy, welltyped⟩
  all_goals simp_all

/-- Only a program has a smooth type. -/
theorem smooth_value {env : Indexed.Environment} {world : World} {value : Value} {application : Application}
    (representation : familyRepresentation env application.family = some .smooth)
    (typed : PrimitiveValueHasType env world value (.indexed application)) :
    ∃ program x y n m, value = .indexed (.smooth program) ∧
      application.indices = [.object (.global x), .object (.global y)] ∧
      smoothDimension? env x = some n ∧ smoothDimension? env y = some m ∧ program.wellTyped n m = true := by
  cases value <;> simp only [PrimitiveValueHasType] at typed <;> try contradiction
  case indexed value =>
    cases value with
    | smooth program =>
      obtain ⟨x, y, n, m, h⟩ := smooth_has_type representation typed
      exact ⟨program, x, y, n, m, rfl, h⟩
    | _ =>
      obtain ⟨_, typed⟩ := typed
      simp only [representation] at typed

/-- The canonical typing of a smooth value from its parts. -/
theorem smooth_typed {env : Indexed.Environment} {world : World} {application : Application}
    {program : SmoothRuntime.Program} {x y : DeclId} {n m : Nat}
    (representation : familyRepresentation env application.family = some .smooth)
    (valid : application.Valid env) (indices : application.indices = [.object (.global x), .object (.global y)])
    (hx : smoothDimension? env x = some n) (hy : smoothDimension? env y = some m)
    (welltyped : program.wellTyped n m = true) :
    PrimitiveValueHasType env world (.indexed (.smooth program)) (.indexed application) := by
  refine ⟨valid, ?_⟩
  simp only [representation, indices]
  exact ⟨n, m, hx, hy, welltyped⟩

/-- The family of a smooth value has the smooth representation. -/
theorem smooth_representation {env : Indexed.Environment} {world : World} {program : SmoothRuntime.Program}
    {application : Application} (typed : IndexedHasType env world (.smooth program) application) :
    familyRepresentation env application.family = some .smooth := by
  have shape := typed.2
  split at shape <;> simp_all

/-- The typing of a smooth value does not depend on the world: its indices are
declared global objects. -/
theorem smooth_world {env : Indexed.Environment} {before after : World} {program : SmoothRuntime.Program}
    {application : Application} (typed : IndexedHasType env before (.smooth program) application) :
    IndexedHasType env after (.smooth program) application := by
  have representation := smooth_representation typed
  obtain ⟨x, y, n, m, indices, hx, hy, welltyped⟩ := smooth_has_type representation typed
  exact smooth_typed representation typed.1 indices hx hy welltyped

theorem lookup_entry {env : Indexed.Environment} {id : DeclId} {declaration : Declaration}
    (h : lookup env id = some declaration) :
    ∃ entry ∈ env, entry.id = id ∧ entry.declaration = declaration := by
  unfold lookup at h
  cases found : env.find? (fun entry => entry.id == id) with
  | none => simp [found] at h
  | some entry =>
    simp only [found, Option.map_some, Option.some.injEq] at h
    exact ⟨entry, List.mem_of_find?_eq_some found, by simpa using List.find?_some found, h⟩

theorem family_valid {env : Indexed.Environment} (envValid : env.Valid) {id : DeclId} {family : Family}
    (h : lookup env id = some (.family family)) : family.Valid env := by
  obtain ⟨entry, member, _, declaration⟩ := lookup_entry h
  have valid := envValid.declarations entry member
  unfold Entry.Valid at valid
  rw [declaration] at valid
  exact valid

/-- **Disjointness.** In a valid environment, an application of a smooth
family names exactly two declared smooth objects: no descriptor global,
presented object or local object brand. -/
theorem smooth_application_indices {env : Indexed.Environment} (envValid : env.Valid)
    {application : Application} (valid : application.Valid env)
    (representation : familyRepresentation env application.family = some .smooth) :
    ∃ x y, application.indices = [.object (.global x), .object (.global y)] ∧
      (smoothDimension? env x).isSome = true ∧ (smoothDimension? env y).isSome = true := by
  obtain ⟨family, found, arity, _, constraints⟩ := valid
  have smooth : family.representation = .smooth := by
    simpa [familyRepresentation, found] using representation
  obtain ⟨_, _, _, shape⟩ := family_valid envValid found
  simp only [smooth] at shape
  obtain ⟨length, constraintsEq, _⟩ := shape
  rw [constraintsEq] at constraints
  obtain ⟨x, hx, sx⟩ := constraints (.canonical 0) (by simp)
  obtain ⟨y, hy, sy⟩ := constraints (.canonical 1) (by simp)
  have count : application.indices.length = 2 := arity ▸ length
  match indices : application.indices, count with
  | [a, b], _ =>
    rw [indices] at hx hy
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hx hy
    exact ⟨x, y, by rw [hx, hy], sx, sy⟩

theorem values_nil {env : Indexed.Environment} {world : World} {values : List Value}
    (typed : PrimitiveValuesHaveTypes env world values []) : values = [] := by
  cases values <;> simp_all [PrimitiveValuesHaveTypes]

theorem values_single {env : Indexed.Environment} {world : World} {values : List Value} {type : ValueType}
    (typed : PrimitiveValuesHaveTypes env world values [type]) :
    ∃ value, values = [value] ∧ PrimitiveValueHasType env world value type := by
  cases values with
  | nil => contradiction
  | cons value rest => exact ⟨value, by simp [values_nil typed.2], typed.1⟩

theorem values_pair {env : Indexed.Environment} {world : World} {values : List Value} {first second : ValueType}
    (typed : PrimitiveValuesHaveTypes env world values [first, second]) :
    ∃ left right, values = [left, right] ∧ PrimitiveValueHasType env world left first ∧
      PrimitiveValueHasType env world right second := by
  cases values with
  | nil => contradiction
  | cons left rest =>
    obtain ⟨right, equal, typedRight⟩ := values_single typed.2
    exact ⟨left, right, by simp [equal], typed.1, typedRight⟩

/-- `count` runtime integers. -/
theorem integer_values {env : Indexed.Environment} {world : World} :
    ∀ {values : List Value} {count : Nat},
      PrimitiveValuesHaveTypes env world values ((List.range count).map fun _ => .integer) →
      ∃ coordinates, values.mapM Value.integer? = some coordinates ∧ coordinates.length = count
  | [], count, typed => by
    cases count with
    | zero => exact ⟨[], rfl, rfl⟩
    | succ n => simp [List.range_succ_eq_map, PrimitiveValuesHaveTypes] at typed
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
        obtain ⟨coordinates, found, length⟩ := integer_values tail
        exact ⟨v :: coordinates, by simp [found, Value.integer?], by simp [length]⟩

theorem smoothConstant_total {env : Indexed.Environment} {world : World} {application : Application}
    {map : AlgebraRuntime.Map} {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType}
    {values : List Value}
    (rule : PrimitiveTyped env (.smoothConstant application map) allowed brand [] output)
    (typed : PrimitiveValuesHaveTypes env world values []) :
    SmoothOutcome env world (.smoothConstant application map) values output := by
  have empty := values_nil typed
  subst values
  have association : output = .indexed application := (IndexedAssociations.smoothConstant_association.mp rule.association).symm
  subst association
  have valid : smoothConstantValid env application map = true := rule.bindingValid
  unfold smoothConstantValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨⟨smooth, _⟩, endpoints⟩ := valid
  cases h : smoothEndpoints? env application with
  | none => simp [h] at endpoints
  | some dimensions =>
    obtain ⟨n, m⟩ := dimensions
    simp only [h] at endpoints
    obtain ⟨x, y, indices, hx, hy⟩ := endpoints_spec h
    exact ⟨_, rfl, smooth_typed (smooth_family smooth) rule.resultValid indices hx hy endpoints⟩

theorem smoothCompose_total {env : Indexed.Environment} {world : World} {family gf ff : DeclId}
    {middle target source middle' : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.smoothCompose family) allowed brand
      [.indexed ⟨gf, [.object middle, .object target]⟩, .indexed ⟨ff, [.object source, .object middle']⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨gf, [.object middle, .object target]⟩, .indexed ⟨ff, [.object source, .object middle']⟩]) :
    SmoothOutcome env world (.smoothCompose family) values output := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := IndexedAssociations.smoothCompose_association.mp rule.association
  have smooth := smooth_family rule.bindingValid
  obtain ⟨left, right, rfl, leftTyped, rightTyped⟩ := values_pair typed
  obtain ⟨after, y, z, k, m, rfl, afterIndices, hy, hz, afterTyped⟩ := smooth_value smooth leftTyped
  obtain ⟨before, x, y', n, k', rfl, beforeIndices, hx, hy', beforeTyped⟩ := smooth_value smooth rightTyped
  simp only [List.cons.injEq, Index.object.injEq, and_true] at afterIndices beforeIndices
  obtain ⟨rfl, rfl⟩ := afterIndices
  obtain ⟨rfl, same⟩ := beforeIndices
  cases same
  have hk : k' = k := Option.some.inj (hy'.symm.trans hy)
  subst hk
  refine ⟨_, rfl, smooth_typed smooth rule.resultValid rfl hx hz ?_⟩
  simp only [SmoothRuntime.Program.wellTyped, Bool.and_eq_true,
    VastitasOracle.SmoothRuntime.wellTyped_outputArity beforeTyped]
  exact ⟨beforeTyped, afterTyped⟩

theorem smoothEqual_total {env : Indexed.Environment} {world : World} {family : DeclId}
    {left right : Application} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.smoothEqual family) allowed brand [.indexed left, .indexed right] output)
    (typed : PrimitiveValuesHaveTypes env world values [.indexed left, .indexed right]) :
    SmoothOutcome env world (.smoothEqual family) values output := by
  obtain ⟨familyEqual, _, rfl, rfl⟩ := IndexedAssociations.smoothEqual_association.mp rule.association
  have smooth : familyRepresentation env left.family = some .smooth :=
    familyEqual ▸ smooth_family (rule.bindingValid : isSmoothFamily env family = true)
  obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ := values_pair typed
  obtain ⟨a, _, _, _, _, rfl, _⟩ := smooth_value smooth firstTyped
  obtain ⟨b, _, _, _, _, rfl, _⟩ := smooth_value smooth secondTyped
  exact ⟨.boolean (SmoothRuntime.same a b), rfl, trivial⟩

theorem smoothComposite_total {env : Indexed.Environment} {world : World} {family : DeclId}
    {application : Application} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.smoothComposite family) allowed brand [.indexed application] output)
    (typed : PrimitiveValuesHaveTypes env world values [.indexed application]) :
    SmoothOutcome env world (.smoothComposite family) values output := by
  obtain ⟨familyEqual, rfl⟩ := IndexedAssociations.smoothComposite_association.mp rule.association
  have smooth : familyRepresentation env application.family = some .smooth :=
    familyEqual ▸ smooth_family (rule.bindingValid : isSmoothFamily env family = true)
  obtain ⟨value, rfl, valueTyped⟩ := values_single typed
  obtain ⟨program, x, y, n, m, rfl, indices, hx, hy, welltyped⟩ := smooth_value smooth valueTyped
  exact ⟨_, rfl, smooth_typed smooth rule.resultValid indices hx hy
    (VastitasOracle.SmoothCanonical.composite_wellTyped welltyped)⟩

theorem smoothIntPoint_total {env : Indexed.Environment} {world : World} {family object point : DeclId}
    {arguments : List ValueType} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.smoothIntPoint family object point) allowed brand arguments output)
    (typed : PrimitiveValuesHaveTypes env world values arguments) :
    SmoothOutcome env world (.smoothIntPoint family object point) values output := by
  obtain ⟨rfl, rfl⟩ := IndexedAssociations.smoothIntPoint_association.mp rule.association
  have valid : smoothIntPointValid env family object point = true := rule.bindingValid
  unfold smoothIntPointValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨⟨⟨smooth, objectSmooth⟩, pointZero⟩, _⟩ := valid
  obtain ⟨dimension, objectDimension⟩ := Option.isSome_iff_exists.mp objectSmooth
  obtain ⟨coordinates, found, length⟩ := integer_values typed
  have arity : smoothArity env object = dimension := by simp [smoothArity, objectDimension]
  rw [arity] at length
  refine ⟨.indexed (.smooth (SmoothRuntime.intPoint coordinates)), ?_,
    smooth_typed (smooth_family smooth) rule.resultValid rfl pointZero objectDimension ?_⟩
  · simp [evalPrimitive, smoothPointValue, found]
  · rw [← length]
    exact VastitasOracle.SmoothCanonical.intPoint_wellTyped coordinates

/-! ## Runtime erasure -/

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

/-- A point from runtime integers erases to the runtime `intPoint`. -/
theorem smoothPoint_erasure {family object point : DeclId} {values : List Value} {value : Value}
    (evaluated : smoothPointValue values = some value) :
    ∃ inputs output, values.mapM erasePrimitiveValue = some inputs ∧
      erasePrimitiveValue value = some output ∧
      evalRuntimePrimitive (.smoothIntPoint family object point) inputs = some output := by
  unfold smoothPointValue at evaluated
  cases coordinates : values.mapM Value.integer? with
  | none => simp [coordinates] at evaluated
  | some list =>
    simp [coordinates] at evaluated
    subst evaluated
    obtain ⟨inputs, erased, runtime⟩ := integers_erase coordinates
    exact ⟨inputs, _, erased, rfl, by simp [evalRuntimePrimitive, smoothPointRuntime, runtime]⟩

/-- **Reification.** The value of `compose` is the program node
`Program.compose after before`, both in the Core semantics and at runtime.
It is never the expanded composite. -/
theorem smoothCompose_value (env : Indexed.Environment) (family : DeclId)
    (after before : SmoothRuntime.Program) :
    evalPrimitive env (.smoothCompose family) [.indexed (.smooth after), .indexed (.smooth before)] =
      some (.indexed (.smooth (.compose after before))) ∧
    evalRuntimePrimitive (.smoothCompose family) [.smooth after, .smooth before] =
      some (.smooth (.compose after before)) := ⟨rfl, rfl⟩

end VastitasOracle.SmoothPrimitives
