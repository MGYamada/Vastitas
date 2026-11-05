import VastitasOracle.AffineDeclarations
import VastitasOracle.SmoothPrimitives
import VastitasKernel.SmoothDeclarations

set_option autoImplicit false

/-! Structural soundness of smooth objects and smooth maps (Stage 3).

An accepted `.smoothAffine` entry has a smooth implementation and distinct
coordinates within the generator limit, which is exactly what
`SmoothDeclarations.checkObject` checks. A smooth implementation is never a
presented or descriptor implementation, so:

- `affineData?`, `chainOf` and every Stage 2 contract ignore smooth objects;
- the sealed Stage 1 point and morphism families and the Stage 2 relative
  family never range over smooth objects;
- a smooth family ranges over smooth objects only, and its applications name
  two declared smooth objects;
- a smooth implementation has no `indexed global` objects, so every canonical
  object of a smooth implementation is an `Affine(n)[…]` declaration.

The value of `compose` is the program node `Program.compose`, never the
expanded composite, both in the Core semantics and at runtime.

The Stage 2 statements (`validAffine_sound`, `presented_not_descriptor`,
`sealed_families_exclude_presented`) are unchanged. -/
namespace VastitasOracle.SmoothDeclarations

open VastitasKernel VastitasKernel.Indexed

/-- An accepted smooth object. -/
theorem smoothAffine_sound {env : Environment} {implementation : DeclId} {coordinates : List String}
    (h : validSmoothAffine env implementation coordinates = true) :
    smoothImplementation env implementation = true ∧ coordinates.length ≤ Limits.algebraGenerators ∧
      coordinates.Nodup ∧ SmoothDeclarations.checkObject coordinates.length coordinates = .ok () := by
  unfold validSmoothAffine at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨smooth, bounded⟩, distinct⟩ := h
  refine ⟨smooth, bounded, distinct, ?_⟩
  have notAbove : ¬coordinates.length > Limits.algebraGenerators := by omega
  simp [SmoothDeclarations.checkObject, notAbove, distinct]
  rfl

/-- Smooth implementations are never presented implementations. -/
theorem smooth_not_presented {env : Environment} {id : DeclId}
    (h : smoothImplementation env id = true) : presentedImplementation env id = false := by
  unfold smoothImplementation at h
  unfold presentedImplementation
  split at h <;> simp_all

/-- Smooth implementations are never descriptor implementations. -/
theorem smooth_not_descriptor {env : Environment} {id : DeclId}
    (h : smoothImplementation env id = true) : affineImplementation env id = false := by
  unfold smoothImplementation at h
  unfold affineImplementation
  split at h <;> simp_all

/-- A smooth object has no presented data. -/
theorem affineData_smooth_none {env : Environment} {id : DeclId} {coordinates : List String}
    (h : smoothCoordinates? env id = some coordinates) : affineData? env id = none := by
  unfold smoothCoordinates? at h
  unfold affineData?
  split at h <;> simp_all

/-- A smooth object has no base chain, so `structural` never holds for it. -/
theorem chainOf_smooth_none {env : Environment} {id : DeclId} {coordinates : List String}
    (h : smoothCoordinates? env id = some coordinates) : chainOf env id = none := by
  unfold chainOf
  cases fuel : Limits.algebraChain with
  | zero => rfl
  | succ fuel => simp [affineChain, affineData_smooth_none h]

/-- `canonical object` holds exactly when that index is a declared smooth object. -/
theorem canonical_holds {env : Environment} {indices : List Index} {object : Nat} :
    (Constraint.canonical object).Holds env indices ↔
      ∃ x coordinates, indices[object]? = some (.object (.global x)) ∧
        smoothCoordinates? env x = some coordinates := by
  constructor
  · rintro ⟨x, found, smooth⟩
    unfold smoothDimension? at smooth
    obtain ⟨coordinates, hc⟩ := Option.isSome_iff_exists.mp (by simpa using smooth)
    exact ⟨x, coordinates, found, hc⟩
  · rintro ⟨x, coordinates, found, hc⟩
    exact ⟨x, found, by simp [smoothDimension?, hc]⟩

private theorem domain_all {env : Environment} {f : Family} {predicate : DeclId → Bool}
    (all : f.parameters.all (fun p => match p with
      | .object id => (Indexed.domain env id).all predicate
      | _ => false) = true)
    {domain : DeclId} (parameter : Parameter.object domain ∈ f.parameters) {id : DeclId}
    (member : id ∈ Indexed.domain env domain) : predicate id = true :=
  List.all_eq_true.mp (List.all_eq_true.mp all _ parameter) id member

/-- **Non-regression.** The sealed Stage 1 point and morphism families and the
Stage 2 relative family never range over smooth implementations. -/
theorem sealed_families_exclude_smooth {env : Environment} {f : Family}
    (valid : f.Valid env)
    (sealed : f.representation = .point ∨ f.representation = .morphism ∨ f.representation = .relative)
    {domain : DeclId} (parameter : Parameter.object domain ∈ f.parameters) {id : DeclId}
    (member : id ∈ Indexed.domain env domain) : smoothImplementation env id = false := by
  obtain ⟨_, _, _, representation⟩ := valid
  cases smooth : smoothImplementation env id
  · rfl
  · rcases sealed with sealed | sealed | sealed
    · simp only [sealed] at representation
      have descriptor := List.all_eq_true.mp (List.all_eq_true.mp representation.2.2.2.2 _ parameter) id member
      rw [smooth_not_descriptor smooth] at descriptor
      cases descriptor
    · simp only [sealed] at representation
      have descriptor := List.all_eq_true.mp (List.all_eq_true.mp representation.2.2.2.2 _ parameter) id member
      rw [smooth_not_descriptor smooth] at descriptor
      cases descriptor
    · simp only [sealed] at representation
      have presented := domain_all representation.2.2 parameter member
      rw [smooth_not_presented smooth] at presented
      cases presented

/-- A smooth family ranges over smooth implementations only: no presented
and no descriptor implementation. -/
theorem smooth_families_exclude_foreign {env : Environment} {f : Family}
    (valid : f.Valid env) (sealed : f.representation = .smooth)
    {domain : DeclId} (parameter : Parameter.object domain ∈ f.parameters) {id : DeclId}
    (member : id ∈ Indexed.domain env domain) :
    smoothImplementation env id = true ∧ presentedImplementation env id = false ∧
      affineImplementation env id = false := by
  obtain ⟨_, _, _, representation⟩ := valid
  simp only [sealed] at representation
  have smooth := domain_all representation.2.2 parameter member
  exact ⟨smooth, smooth_not_presented smooth, smooth_not_descriptor smooth⟩

/-- In a valid environment, an application of a smooth family names exactly
two declared smooth objects. -/
theorem smooth_applications_name_smooth_objects {env : Environment} (envValid : env.Valid)
    {application : Application} (valid : application.Valid env)
    (representation : familyRepresentation env application.family = some .smooth) :
    ∃ x y, application.indices = [.object (.global x), .object (.global y)] ∧
      (smoothDimension? env x).isSome = true ∧ (smoothDimension? env y).isSome = true :=
  SmoothPrimitives.smooth_application_indices envValid valid representation

/-- **Smooth objects are declared.** In a valid environment, every canonical
global object whose implementation is smooth is an `Affine(n)[…]` declaration
that passes `checkObject`. In particular there is no smooth `indexed global`. -/
theorem smooth_objects_are_declared {env : Environment} (envValid : env.Valid) {id : DeclId}
    {type : ObjectType} (found : ObjectRef.type? env (.global id) = some type)
    (smooth : smoothImplementation env type.domain = true) :
    ∃ coordinates, lookup env id = some (.smoothAffine type.domain coordinates) ∧
      SmoothDeclarations.checkObject coordinates.length coordinates = .ok () := by
  unfold ObjectRef.type? at found
  cases declared : lookup env id with
  | none => simp [declared] at found
  | some declaration =>
    obtain ⟨entry, member, _, entryDeclaration⟩ := SmoothPrimitives.lookup_entry declared
    have entryValid := envValid.declarations entry member
    unfold Entry.Valid at entryValid
    rw [entryDeclaration] at entryValid
    cases declaration with
    | global implementation =>
      cases marker : implementationMarker env implementation <;>
        simp [declared, Declaration.objectImplementation?, marker] at found
      subst found
      dsimp only at entryValid smooth
      rw [smooth] at entryValid
      exact absurd entryValid.2.2 (by simp)
    | affine implementation data =>
      cases marker : implementationMarker env implementation <;>
        simp [declared, Declaration.objectImplementation?, marker] at found
      subst found
      dsimp only at entryValid smooth
      have presented := (AffineDeclarations.validAffine_sound entryValid).1
      rw [smooth_not_presented smooth] at presented
      cases presented
    | smoothAffine implementation coordinates =>
      cases marker : implementationMarker env implementation <;>
        simp [declared, Declaration.objectImplementation?, marker] at found
      subst found
      dsimp only at entryValid
      exact ⟨coordinates, rfl, (smoothAffine_sound entryValid).2.2.2⟩
    | marker | implementation | classification | family | metric | metricEvidence =>
      simp [declared, Declaration.objectImplementation?] at found

/-- **Reification.** The value of `compose` is the program node
`Program.compose after before` in the Core semantics, and it erases to the
same node at runtime. It is never the expanded composite. -/
theorem smoothCompose_reifies (env : Environment) (family : DeclId) (after before : SmoothRuntime.Program) :
    Core.Semantics.evalPrimitive env (.smoothCompose family)
        [.indexed (.smooth after), .indexed (.smooth before)] =
      some (.indexed (.smooth (.compose after before))) ∧
    Core.Semantics.evalRuntimePrimitive (.smoothCompose family) [.smooth after, .smooth before] =
      some (.smooth (.compose after before)) :=
  SmoothPrimitives.smoothCompose_value env family after before

/-- An actual Core `compose` node evaluates to the program node built from the
values of its operands. -/
theorem core_compose_reifies {module : Core.Module} {fuel : Nat} {values : Core.Semantics.Values}
    {id : DeclId} {first second : Core.Term} {result : Core.Result} {family : DeclId}
    {after before : SmoothRuntime.Program}
    (found : module.declarations.primitive? id = some (.smoothCompose family))
    (afterValue : Core.Semantics.eval module fuel values first = some (.indexed (.smooth after)))
    (beforeValue : Core.Semantics.eval module fuel values second = some (.indexed (.smooth before))) :
    Core.Semantics.eval module (fuel + 1) values (.primitive id [first, second] result) =
      some (.indexed (.smooth (.compose after before))) := by
  simp [Core.Semantics.eval, found, afterValue, beforeValue, Core.Semantics.evalPrimitive, PrimitiveBinding.contract,
    PrimitiveDescriptor.ofBool]

end VastitasOracle.SmoothDeclarations
