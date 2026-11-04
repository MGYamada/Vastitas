import VastitasKernel.IndexedSemantics
import VastitasOracle.SmoothRuntime
import VastitasOracle.SmoothPrimitives
import VastitasOracle.IndexedAssociations

set_option autoImplicit false

/-! Typed totality and runtime erasure of the fiber and tape primitives (Stage 3).

A value of `Cotangent<X>` or `Tangent<X>` is a fiber of that variance: the
failure value `none`, or a point and components with `dim X` entries each
(`FiberTyped`). A value of `Tape<X, Y>` is the forward record of a program
checked as `X → Y` at a point of `X` (`TapeTyped`, the residual relation).
Every accepted fiber or tape primitive returns a value of its checked result
type:

- `fiber_vector` builds a fiber at a point of `X` from `dim X` integers;
- `cotangent_pullback` and `differential` return a fiber over the source of
  the map, by `pullback_mem_of_wellTyped`;
- `linearize` returns a tape that satisfies the residual relation;
- `cotangent_backward` on such a tape returns a fiber over its source;
- `fiber_at` and `fiber_equal` return Booleans, and `fiber_component` and
  `fiber_pairing` return integer pairs.

Fiber and tape values name declared smooth objects only, so their typing does
not depend on the world and survives renaming and package transport.
`IndexedSemantics.primitive_total_and_typed` and
`IndexedSemantics.primitive_runtime_erasure` dispatch to these lemmas. -/
namespace VastitasOracle.SmoothFibers

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasOracle.SmoothPrimitives

/-! ## Families -/

theorem fiber_family {env : Indexed.Environment} {family : DeclId} {variance : Variance}
    (h : fiberVariance? env family = some variance) : familyRepresentation env family = some (.fiber variance) := by
  unfold fiberVariance? at h
  unfold familyRepresentation
  split at h
  · rename_i contract _
    split at h <;> simp_all
  · simp at h

theorem fiber_family_cotangent {env : Indexed.Environment} {family : DeclId}
    (h : (fiberVariance? env family == some .cotangent) = true) :
    familyRepresentation env family = some (.fiber .cotangent) :=
  fiber_family (by simpa using h)

theorem fiber_family_some {env : Indexed.Environment} {family : DeclId}
    (h : (fiberVariance? env family).isSome = true) :
    ∃ variance, familyRepresentation env family = some (.fiber variance) := by
  obtain ⟨variance, hv⟩ := Option.isSome_iff_exists.mp h
  exact ⟨variance, fiber_family hv⟩

theorem tape_family {env : Indexed.Environment} {family : DeclId}
    (h : isTapeFamily env family = true) : familyRepresentation env family = some .tape := by
  unfold isTapeFamily at h
  unfold familyRepresentation
  split at h <;> simp_all

/-! ## Typing of fiber and tape values -/

theorem fiber_has_type {env : Indexed.Environment} {world : World} {variance : Variance}
    {value : SmoothRuntime.FiberValue} {application : Application}
    (typed : IndexedHasType env world (.fiber variance value) application) :
    familyRepresentation env application.family = some (.fiber variance) ∧
      ∃ x n, application.indices = [.object (.global x)] ∧ smoothDimension? env x = some n ∧
        FiberTyped n value := by
  obtain ⟨_, typed⟩ := typed
  split at typed
  case h_6 =>
    rename_i heqValue heqRepresentation heqIndices
    cases heqValue
    obtain ⟨rfl, n, hx, fiberTyped⟩ := typed
    exact ⟨heqRepresentation, _, n, heqIndices, hx, fiberTyped⟩
  all_goals simp_all

theorem tape_has_type {env : Indexed.Environment} {world : World} {tape : SmoothRuntime.Tape}
    {application : Application} (typed : IndexedHasType env world (.tape tape) application) :
    familyRepresentation env application.family = some .tape ∧
      ∃ x y n m, application.indices = [.object (.global x), .object (.global y)] ∧
        smoothDimension? env x = some n ∧ smoothDimension? env y = some m ∧ TapeTyped n m tape := by
  obtain ⟨_, typed⟩ := typed
  split at typed
  case h_7 =>
    rename_i heqValue heqRepresentation heqIndices
    cases heqValue
    obtain ⟨n, m, hx, hy, tapeTyped⟩ := typed
    exact ⟨heqRepresentation, _, _, n, m, heqIndices, hx, hy, tapeTyped⟩
  all_goals simp_all

/-- The canonical typing of a fiber value from its parts. -/
theorem fiber_typed {env : Indexed.Environment} {world : World} {application : Application}
    {variance : Variance} {value : SmoothRuntime.FiberValue} {x : DeclId} {n : Nat}
    (representation : familyRepresentation env application.family = some (.fiber variance))
    (valid : application.Valid env) (indices : application.indices = [.object (.global x)])
    (hx : smoothDimension? env x = some n) (fiberTyped : FiberTyped n value) :
    PrimitiveValueHasType env world (.indexed (.fiber variance value)) (.indexed application) := by
  refine ⟨valid, ?_⟩
  simp only [representation, indices]
  exact ⟨trivial, n, hx, fiberTyped⟩

/-- The canonical typing of a tape value from its parts. -/
theorem tape_typed {env : Indexed.Environment} {world : World} {application : Application}
    {tape : SmoothRuntime.Tape} {x y : DeclId} {n m : Nat}
    (representation : familyRepresentation env application.family = some .tape)
    (valid : application.Valid env) (indices : application.indices = [.object (.global x), .object (.global y)])
    (hx : smoothDimension? env x = some n) (hy : smoothDimension? env y = some m)
    (tapeTyped : TapeTyped n m tape) :
    PrimitiveValueHasType env world (.indexed (.tape tape)) (.indexed application) := by
  refine ⟨valid, ?_⟩
  simp only [representation, indices]
  exact ⟨n, m, hx, hy, tapeTyped⟩

/-- Only a fiber of the family's variance has a fiber type. -/
theorem fiber_value {env : Indexed.Environment} {world : World} {value : Value} {application : Application}
    {variance : Variance}
    (representation : familyRepresentation env application.family = some (.fiber variance))
    (typed : PrimitiveValueHasType env world value (.indexed application)) :
    ∃ fiber x n, value = .indexed (.fiber variance fiber) ∧ application.indices = [.object (.global x)] ∧
      smoothDimension? env x = some n ∧ FiberTyped n fiber := by
  cases value <;> simp only [PrimitiveValueHasType] at typed <;> try contradiction
  case indexed value =>
    cases value with
    | fiber variance' fiber =>
      obtain ⟨found, x, n, indices, hx, fiberTyped⟩ := fiber_has_type typed
      rw [representation] at found
      cases found
      exact ⟨fiber, x, n, rfl, indices, hx, fiberTyped⟩
    | _ =>
      obtain ⟨_, typed⟩ := typed
      simp only [representation] at typed

/-- Only a tape has a tape type. -/
theorem tape_value {env : Indexed.Environment} {world : World} {value : Value} {application : Application}
    (representation : familyRepresentation env application.family = some .tape)
    (typed : PrimitiveValueHasType env world value (.indexed application)) :
    ∃ tape x y n m, value = .indexed (.tape tape) ∧
      application.indices = [.object (.global x), .object (.global y)] ∧
      smoothDimension? env x = some n ∧ smoothDimension? env y = some m ∧ TapeTyped n m tape := by
  cases value <;> simp only [PrimitiveValueHasType] at typed <;> try contradiction
  case indexed value =>
    cases value with
    | tape tape =>
      obtain ⟨_, x, y, n, m, indices, hx, hy, tapeTyped⟩ := tape_has_type typed
      exact ⟨tape, x, y, n, m, rfl, indices, hx, hy, tapeTyped⟩
    | _ =>
      obtain ⟨_, typed⟩ := typed
      simp only [representation] at typed

/-- The typing of a fiber does not depend on the world: its index is a
declared global object. -/
theorem fiber_world {env : Indexed.Environment} {before after : World} {variance : Variance}
    {value : SmoothRuntime.FiberValue} {application : Application}
    (typed : IndexedHasType env before (.fiber variance value) application) :
    IndexedHasType env after (.fiber variance value) application := by
  obtain ⟨representation, x, n, indices, hx, fiberTyped⟩ := fiber_has_type typed
  exact fiber_typed representation typed.1 indices hx fiberTyped

/-- The typing of a tape does not depend on the world. -/
theorem tape_world {env : Indexed.Environment} {before after : World} {tape : SmoothRuntime.Tape}
    {application : Application} (typed : IndexedHasType env before (.tape tape) application) :
    IndexedHasType env after (.tape tape) application := by
  obtain ⟨representation, x, y, n, m, indices, hx, hy, tapeTyped⟩ := tape_has_type typed
  exact tape_typed representation typed.1 indices hx hy tapeTyped

/-- **Disjointness.** In a valid environment, an application of a fiber family
names exactly one declared smooth object. -/
theorem fiber_application_indices {env : Indexed.Environment} (envValid : env.Valid)
    {application : Application} {variance : Variance} (valid : application.Valid env)
    (representation : familyRepresentation env application.family = some (.fiber variance)) :
    ∃ x, application.indices = [.object (.global x)] ∧ (smoothDimension? env x).isSome = true := by
  obtain ⟨family, found, arity, _, constraints⟩ := valid
  have fiber : family.representation = .fiber variance := by
    simpa [familyRepresentation, found] using representation
  obtain ⟨_, _, _, shape⟩ := family_valid envValid found
  simp only [fiber] at shape
  obtain ⟨length, constraintsEq, _⟩ := shape
  rw [constraintsEq] at constraints
  obtain ⟨x, hx, sx⟩ := constraints (.canonical 0) (by simp)
  have count : application.indices.length = 1 := arity ▸ length
  match indices : application.indices, count with
  | [a], _ =>
    rw [indices] at hx
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
    exact ⟨x, by rw [hx], sx⟩

/-- **Disjointness.** In a valid environment, an application of a tape family
names exactly two declared smooth objects. -/
theorem tape_application_indices {env : Indexed.Environment} (envValid : env.Valid)
    {application : Application} (valid : application.Valid env)
    (representation : familyRepresentation env application.family = some .tape) :
    ∃ x y, application.indices = [.object (.global x), .object (.global y)] ∧
      (smoothDimension? env x).isSome = true ∧ (smoothDimension? env y).isSome = true := by
  obtain ⟨family, found, arity, _, constraints⟩ := valid
  have tape : family.representation = .tape := by
    simpa [familyRepresentation, found] using representation
  obtain ⟨_, _, _, shape⟩ := family_valid envValid found
  simp only [tape] at shape
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

/-! ## Runtime facts behind the typing -/

theorem coordinates_length {point : SmoothRuntime.Program} {n : Nat} (hpoint : point.wellTyped 0 n = true) :
    (SmoothRuntime.coordinates point).length = n := by
  rw [SmoothRuntime.coordinates, VastitasOracle.SmoothRuntime.eval_length,
    VastitasOracle.SmoothRuntime.wellTyped_outputArity hpoint]

/-- **Pullback typing.** For a map checked as `ℝⁿ → ℝᵐ` and a point checked as
`ℝ⁰ → ℝⁿ`, every pullback is a fiber over `ℝⁿ`. -/
theorem pullback_typed (mode : SmoothRuntime.PullbackMode) {map point : SmoothRuntime.Program}
    {n m : Nat} (hmap : map.wellTyped n m = true) (hpoint : point.wellTyped 0 n = true)
    (seed : SmoothRuntime.FiberValue) : FiberTyped n (SmoothRuntime.pullback mode map point seed) := by
  cases h : SmoothRuntime.pullback mode map point seed with
  | none => trivial
  | some result =>
    obtain ⟨_, hl, hc⟩ := VastitasOracle.SmoothRuntime.pullback_mem_of_wellTyped hmap hpoint h
    exact ⟨hl, hc⟩

theorem differential_typed {function point : SmoothRuntime.Program} {n m : Nat}
    (hfunction : function.wellTyped n m = true) (hpoint : point.wellTyped 0 n = true) :
    FiberTyped n (SmoothRuntime.differential function point) := by
  rw [VastitasOracle.SmoothRuntime.differential_eq_pullback]
  exact pullback_typed .saved hfunction hpoint _

/-- **Linearize typing.** `linearize` builds a tape that satisfies the
residual relation. -/
theorem linearize_typed {map point : SmoothRuntime.Program} {n m : Nat}
    (hmap : map.wellTyped n m = true) (hpoint : point.wellTyped 0 n = true) :
    TapeTyped n m (SmoothRuntime.linearize map point) :=
  ⟨map, SmoothRuntime.coordinates point, hmap, coordinates_length hpoint, rfl⟩

/-- **Backward typing.** The reverse pass over a tape `ℝⁿ → ℝᵐ` returns a
fiber over `ℝⁿ`. -/
theorem backward_typed {n m : Nat} {tape : SmoothRuntime.Tape} (tapeTyped : TapeTyped n m tape)
    (seed : SmoothRuntime.FiberValue) : FiberTyped n (SmoothRuntime.backward tape seed) := by
  obtain ⟨program, point, hprogram, hpoint, rfl⟩ := tapeTyped
  cases seed with
  | none => trivial
  | some seed =>
    simp only [SmoothRuntime.backward]
    split
    · refine ⟨by rw [VastitasOracle.SmoothRuntime.forward_input]; exact hpoint, ?_⟩
      rw [VastitasOracle.SmoothRuntime.backward_forward, VastitasOracle.SmoothRuntime.reverse_length,
        VastitasOracle.SmoothRuntime.wellTyped_inputArity hprogram]
    · trivial

theorem vector_typed {point : SmoothRuntime.Program} {n : Nat} (hpoint : point.wellTyped 0 n = true)
    {components : List Int} (length : components.length = n) :
    FiberTyped n (SmoothRuntime.vector point components) :=
  ⟨coordinates_length hpoint, by simp [length]⟩

/-! ## Typed totality -/

/-- A point operand: a program well typed from `ℝ⁰` to the dimension of `x`. -/
theorem point_value {env : Indexed.Environment} {world : World} {value : Value} {smooth point x : DeclId}
    (representation : familyRepresentation env smooth = some .smooth)
    (pointZero : smoothDimension? env point = some 0)
    (typed : PrimitiveValueHasType env world value
      (.indexed ⟨smooth, [.object (.global point), .object (.global x)]⟩)) :
    ∃ program n, value = .indexed (.smooth program) ∧ smoothDimension? env x = some n ∧
      program.wellTyped 0 n = true := by
  obtain ⟨program, p, x', k, n, rfl, indices, hp, hx, welltyped⟩ := smooth_value representation typed
  simp only [List.cons.injEq, Index.object.injEq, ObjectRef.global.injEq, and_true] at indices
  obtain ⟨rfl, rfl⟩ := indices
  rw [pointZero, Option.some.injEq] at hp
  subst hp
  exact ⟨program, n, rfl, hx, welltyped⟩

theorem fiberVector_total {env : Indexed.Environment} {world : World} {family smooth object sf point : DeclId}
    {x : Indexed.ObjectRef} {components : List ValueType} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.fiberVector family smooth object) allowed brand
      (.indexed ⟨sf, [.object (.global point), .object x]⟩ :: components) output)
    (typed : PrimitiveValuesHaveTypes env world values
      (.indexed ⟨sf, [.object (.global point), .object x]⟩ :: components)) :
    SmoothOutcome env world (.fiberVector family smooth object) values output := by
  have valid : fiberVectorValid env family smooth object = true := rule.bindingValid
  obtain ⟨rfl, rfl, rfl, pointZero, rfl⟩ := IndexedAssociations.fiberVector_association.mp rule.association
  unfold fiberVectorValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨⟨⟨fiberSome, smoothFamily⟩, objectSome⟩, _⟩ := valid
  obtain ⟨variance, hv⟩ := Option.isSome_iff_exists.mp fiberSome
  obtain ⟨dimension, hdim⟩ := Option.isSome_iff_exists.mp objectSome
  cases values with
  | nil => contradiction
  | cons first rest =>
    obtain ⟨firstTyped, restTyped⟩ := typed
    obtain ⟨program, n, rfl, hx, welltyped⟩ := point_value (smooth_family smoothFamily) pointZero firstTyped
    rw [hdim, Option.some.injEq] at hx
    subst hx
    obtain ⟨coordinates, found, length⟩ := integer_values restTyped
    have arity : smoothArity env object = dimension := by simp [smoothArity, hdim]
    rw [arity] at length
    refine ⟨.indexed (.fiber variance (SmoothRuntime.vector program coordinates)), ?_,
      fiber_typed (fiber_family hv) rule.resultValid rfl hdim (vector_typed welltyped length)⟩
    simp [evalPrimitive, fiberVectorValue, hv, found]

theorem fiberAt_total {env : Indexed.Environment} {world : World} {family smooth ff sf point : DeclId}
    {x x' : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType}
    {values : List Value}
    (rule : PrimitiveTyped env (.fiberAt family smooth) allowed brand
      [.indexed ⟨ff, [.object x]⟩, .indexed ⟨sf, [.object (.global point), .object x']⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨ff, [.object x]⟩, .indexed ⟨sf, [.object (.global point), .object x']⟩]) :
    SmoothOutcome env world (.fiberAt family smooth) values output := by
  have valid : fiberAtValid env family smooth = true := rule.bindingValid
  obtain ⟨rfl, rfl, rfl, _, rfl⟩ := IndexedAssociations.fiberAt_association.mp rule.association
  unfold fiberAtValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨variance, representation⟩ := fiber_family_some valid.1
  obtain ⟨left, right, rfl, leftTyped, rightTyped⟩ := values_pair typed
  obtain ⟨fiber, _, _, rfl, _⟩ := fiber_value representation leftTyped
  obtain ⟨program, _, _, _, _, rfl, _⟩ := smooth_value (smooth_family valid.2) rightTyped
  exact ⟨.boolean (SmoothRuntime.fiberAt fiber program), rfl, trivial⟩

theorem fiberEqual_total {env : Indexed.Environment} {world : World} {family : DeclId}
    {left right : Application} {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType}
    {values : List Value}
    (rule : PrimitiveTyped env (.fiberEqual family) allowed brand [.indexed left, .indexed right] output)
    (typed : PrimitiveValuesHaveTypes env world values [.indexed left, .indexed right]) :
    SmoothOutcome env world (.fiberEqual family) values output := by
  have valid : fiberEqualValid env family = true := rule.bindingValid
  obtain ⟨familyEqual, _, rfl, rfl⟩ := IndexedAssociations.fiberEqual_association.mp rule.association
  obtain ⟨variance, representation⟩ := fiber_family_some valid
  rw [← familyEqual] at representation
  obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ := values_pair typed
  obtain ⟨a, _, _, rfl, _⟩ := fiber_value representation firstTyped
  obtain ⟨b, _, _, rfl, _⟩ := fiber_value representation secondTyped
  exact ⟨.boolean (SmoothRuntime.fiberEqual a b), rfl, trivial⟩

theorem fiberComponent_total {env : Indexed.Environment} {world : World} {family object ff : DeclId}
    {coordinate : Nat} {x : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.fiberComponent family object coordinate) allowed brand
      [.indexed ⟨ff, [.object x]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values [.indexed ⟨ff, [.object x]⟩]) :
    SmoothOutcome env world (.fiberComponent family object coordinate) values output := by
  have valid : fiberComponentValid env family object coordinate = true := rule.bindingValid
  obtain ⟨rfl, rfl, rfl⟩ := IndexedAssociations.fiberComponent_association.mp rule.association
  unfold fiberComponentValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨variance, representation⟩ := fiber_family_some valid.1.1
  obtain ⟨value, rfl, valueTyped⟩ := values_single typed
  obtain ⟨fiber, _, _, rfl, _⟩ := fiber_value representation valueTyped
  exact ⟨.pairInt (SmoothRuntime.component fiber coordinate).1 (SmoothRuntime.component fiber coordinate).2,
    rfl, trivial⟩

theorem fiberPairing_total {env : Indexed.Environment} {world : World} {cotangent tangent cf tf : DeclId}
    {x x' : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType}
    {values : List Value}
    (rule : PrimitiveTyped env (.fiberPairing cotangent tangent) allowed brand
      [.indexed ⟨cf, [.object x]⟩, .indexed ⟨tf, [.object x']⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values [.indexed ⟨cf, [.object x]⟩, .indexed ⟨tf, [.object x']⟩]) :
    SmoothOutcome env world (.fiberPairing cotangent tangent) values output := by
  have valid : fiberPairingValid env cotangent tangent = true := rule.bindingValid
  obtain ⟨rfl, rfl, rfl, rfl⟩ := IndexedAssociations.fiberPairing_association.mp rule.association
  unfold fiberPairingValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ := values_pair typed
  obtain ⟨a, _, _, rfl, _⟩ := fiber_value (fiber_family (by simpa using valid.1)) firstTyped
  obtain ⟨b, _, _, rfl, _⟩ := fiber_value (fiber_family (by simpa using valid.2)) secondTyped
  exact ⟨.pairInt (SmoothRuntime.pairing a b).1 (SmoothRuntime.pairing a b).2, rfl, trivial⟩

theorem values_triple {env : Indexed.Environment} {world : World} {values : List Value}
    {first second third : ValueType}
    (typed : PrimitiveValuesHaveTypes env world values [first, second, third]) :
    ∃ a b c, values = [a, b, c] ∧ PrimitiveValueHasType env world a first ∧
      PrimitiveValueHasType env world b second ∧ PrimitiveValueHasType env world c third := by
  cases values with
  | nil => contradiction
  | cons a rest =>
    obtain ⟨b, c, rfl, hb, hc⟩ := values_pair typed.2
    exact ⟨a, b, c, rfl, typed.1, hb, hc⟩

/-- A map operand and a point operand at the map's source. -/
theorem map_and_point {env : Indexed.Environment} {world : World} {smooth point : DeclId}
    {x y : Indexed.ObjectRef} {mapValue pointValue : Value}
    (representation : familyRepresentation env smooth = some .smooth)
    (pointZero : smoothDimension? env point = some 0)
    (mapTyped : PrimitiveValueHasType env world mapValue (.indexed ⟨smooth, [.object x, .object y]⟩))
    (pointTyped : PrimitiveValueHasType env world pointValue
      (.indexed ⟨smooth, [.object (.global point), .object x]⟩)) :
    ∃ map program a b n m, mapValue = .indexed (.smooth map) ∧ pointValue = .indexed (.smooth program) ∧
      x = .global a ∧ y = .global b ∧ smoothDimension? env a = some n ∧ smoothDimension? env b = some m ∧
      map.wellTyped n m = true ∧ program.wellTyped 0 n = true := by
  obtain ⟨map, a, b, n, m, rfl, indices, ha, hb, mapWellTyped⟩ := smooth_value representation mapTyped
  simp only [List.cons.injEq, Index.object.injEq, and_true] at indices
  obtain ⟨rfl, rfl⟩ := indices
  obtain ⟨program, n', rfl, ha', pointWellTyped⟩ := point_value representation pointZero pointTyped
  rw [ha, Option.some.injEq] at ha'
  subst ha'
  exact ⟨map, program, a, b, n, m, rfl, rfl, rfl, rfl, ha, hb, mapWellTyped, pointWellTyped⟩

theorem cotangentPullback_total {env : Indexed.Environment} {world : World}
    {smooth cotangent mf pf cf point : DeclId} {mode : SmoothRuntime.PullbackMode}
    {x y x' y' : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType}
    {values : List Value}
    (rule : PrimitiveTyped env (.cotangentPullback smooth cotangent mode) allowed brand
      [.indexed ⟨mf, [.object x, .object y]⟩, .indexed ⟨pf, [.object (.global point), .object x']⟩,
        .indexed ⟨cf, [.object y']⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨mf, [.object x, .object y]⟩, .indexed ⟨pf, [.object (.global point), .object x']⟩,
        .indexed ⟨cf, [.object y']⟩]) :
    SmoothOutcome env world (.cotangentPullback smooth cotangent mode) values output := by
  have valid : cotangentPullbackValid env smooth cotangent = true := rule.bindingValid
  obtain ⟨rfl, rfl, rfl, rfl, rfl, pointZero, rfl⟩ := IndexedAssociations.cotangentPullback_association.mp rule.association
  unfold cotangentPullbackValid at valid
  simp only [Bool.and_eq_true] at valid
  have smoothRepresentation := smooth_family valid.1
  have cotangentRepresentation := fiber_family_cotangent valid.2
  obtain ⟨mapValue, pointValue, seedValue, rfl, mapTyped, pointTyped, seedTyped⟩ := values_triple typed
  obtain ⟨map, program, a, b, n, m, rfl, rfl, rfl, rfl, ha, _, mapWellTyped, pointWellTyped⟩ :=
    map_and_point smoothRepresentation pointZero mapTyped pointTyped
  obtain ⟨seed, _, _, rfl, _⟩ := fiber_value cotangentRepresentation seedTyped
  exact ⟨_, rfl, fiber_typed cotangentRepresentation rule.resultValid rfl ha
    (pullback_typed mode mapWellTyped pointWellTyped seed)⟩

theorem differential_total {env : Indexed.Environment} {world : World}
    {smooth cotangent line mf pf point : DeclId} {x y x' : Indexed.ObjectRef}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.differential smooth cotangent line) allowed brand
      [.indexed ⟨mf, [.object x, .object y]⟩, .indexed ⟨pf, [.object (.global point), .object x']⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨mf, [.object x, .object y]⟩, .indexed ⟨pf, [.object (.global point), .object x']⟩]) :
    SmoothOutcome env world (.differential smooth cotangent line) values output := by
  have valid : differentialValid env smooth cotangent line = true := rule.bindingValid
  obtain ⟨rfl, rfl, rfl, rfl, pointZero, rfl⟩ := IndexedAssociations.differential_association.mp rule.association
  unfold differentialValid at valid
  simp only [Bool.and_eq_true] at valid
  have smoothRepresentation := smooth_family valid.1.1
  have cotangentRepresentation := fiber_family_cotangent valid.1.2
  obtain ⟨mapValue, pointValue, rfl, mapTyped, pointTyped⟩ := values_pair typed
  obtain ⟨map, program, a, b, n, m, rfl, rfl, rfl, _, ha, _, mapWellTyped, pointWellTyped⟩ :=
    map_and_point smoothRepresentation pointZero mapTyped pointTyped
  exact ⟨_, rfl, fiber_typed cotangentRepresentation rule.resultValid rfl ha
    (differential_typed mapWellTyped pointWellTyped)⟩

theorem linearize_total {env : Indexed.Environment} {world : World} {smooth tape mf pf point : DeclId}
    {x y x' : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType}
    {values : List Value}
    (rule : PrimitiveTyped env (.linearize smooth tape) allowed brand
      [.indexed ⟨mf, [.object x, .object y]⟩, .indexed ⟨pf, [.object (.global point), .object x']⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨mf, [.object x, .object y]⟩, .indexed ⟨pf, [.object (.global point), .object x']⟩]) :
    SmoothOutcome env world (.linearize smooth tape) values output := by
  have valid : linearizeValid env smooth tape = true := rule.bindingValid
  obtain ⟨rfl, rfl, rfl, pointZero, rfl⟩ := IndexedAssociations.linearize_association.mp rule.association
  unfold linearizeValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨mapValue, pointValue, rfl, mapTyped, pointTyped⟩ := values_pair typed
  obtain ⟨map, program, a, b, n, m, rfl, rfl, rfl, rfl, ha, hb, mapWellTyped, pointWellTyped⟩ :=
    map_and_point (smooth_family valid.1) pointZero mapTyped pointTyped
  exact ⟨_, rfl, tape_typed (tape_family valid.2) rule.resultValid rfl ha hb
    (linearize_typed mapWellTyped pointWellTyped)⟩

theorem cotangentBackward_total {env : Indexed.Environment} {world : World} {tape cotangent tf cf : DeclId}
    {x y y' : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType}
    {values : List Value}
    (rule : PrimitiveTyped env (.cotangentBackward tape cotangent) allowed brand
      [.indexed ⟨tf, [.object x, .object y]⟩, .indexed ⟨cf, [.object y']⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨tf, [.object x, .object y]⟩, .indexed ⟨cf, [.object y']⟩]) :
    SmoothOutcome env world (.cotangentBackward tape cotangent) values output := by
  have valid : cotangentBackwardValid env tape cotangent = true := rule.bindingValid
  obtain ⟨rfl, rfl, rfl, rfl⟩ := IndexedAssociations.cotangentBackward_association.mp rule.association
  unfold cotangentBackwardValid at valid
  simp only [Bool.and_eq_true] at valid
  have cotangentRepresentation := fiber_family_cotangent valid.2
  obtain ⟨tapeValue, seedValue, rfl, tapeTyped, seedTyped⟩ := values_pair typed
  obtain ⟨tapeRecord, a, b, n, m, rfl, indices, ha, _, residual⟩ := tape_value (tape_family valid.1) tapeTyped
  simp only [List.cons.injEq, Index.object.injEq, and_true] at indices
  obtain ⟨rfl, rfl⟩ := indices
  obtain ⟨seed, _, _, rfl, _⟩ := fiber_value cotangentRepresentation seedTyped
  exact ⟨_, rfl, fiber_typed cotangentRepresentation rule.resultValid rfl ha (backward_typed residual seed)⟩

/-! ## Runtime erasure -/

/-- A fiber from runtime integers erases to the runtime `vector`. -/
theorem fiberVector_erasure {env : Indexed.Environment} {family smooth object : DeclId}
    {point : SmoothRuntime.Program} {components : List Value} {value : Value}
    (evaluated : fiberVectorValue env family point components = some value) :
    ∃ inputs output, (Value.indexed (.smooth point) :: components).mapM erasePrimitiveValue = some inputs ∧
      erasePrimitiveValue value = some output ∧
      evalRuntimePrimitive (.fiberVector family smooth object) inputs = some output := by
  unfold fiberVectorValue at evaluated
  cases variance : fiberVariance? env family with
  | none => simp [variance] at evaluated
  | some variance =>
    cases coordinates : components.mapM Value.integer? with
    | none => simp [variance, coordinates] at evaluated
    | some list =>
      simp [variance, coordinates] at evaluated
      subst evaluated
      obtain ⟨inputs, erased, runtime⟩ := integers_erase coordinates
      refine ⟨.smooth point :: inputs, _, ?_, rfl, ?_⟩
      · simp [erasePrimitiveValue, erased]
      · simp [evalRuntimePrimitive, fiberVectorRuntime, runtime]

end VastitasOracle.SmoothFibers
