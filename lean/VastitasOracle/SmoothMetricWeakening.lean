import VastitasKernel.IndexedSemantics

set_option autoImplicit false

/-! **Metric-free differentiation (C12).** Adding metric declarations changes
neither the validity nor the evaluation of any binding that is not `flat` or
`sharp`.

A *metric declaration* is a metric, metric evidence, or a family with the
`metric_form` representation (`MetricDeclaration`). For every environment
`env` and every list `extra` of entries whose declarations are all metric
declarations, and for every binding other than `flat` and `sharp`:

- `validPrimitiveBinding (env ++ extra) b = validPrimitiveBinding env b`
  (`validPrimitiveBinding_metric_weakening`), and likewise for the
  propositional `PrimitiveBinding.Valid`;
- `evalPrimitive (env ++ extra) b vs = evalPrimitive env b vs` for all
  operands `vs`; this holds for every binding (`evalPrimitive_metric_weakening`).

In particular `differential` and `cotangent_pullback` are unchanged
(`differential_metric_free`, `cotangentPullback_metric_free`). Read from right
to left, the same equations say that removing appended metric declarations
changes nothing either.

The appended entries need not be fresh. `lookup` returns the first entry with
an id, so an appended entry never shadows an entry of `env`; an appended entry
with a fresh id is a metric declaration, which no metric-free contract or
evaluation consults. The proof shows that every lookup-derived view that these
contracts use treats a metric declaration exactly like a missing one, and that
`familyRepresentation` and `validApplication`, which can see a fresh
`metric_form` family, are only consulted behind a guard that excludes it. -/
namespace VastitasOracle.SmoothMetricWeakening

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics

/-- A declaration that only the metric profile contributes. -/
def MetricDeclaration : Declaration → Prop
  | .metric .. | .metricEvidence .. => True
  | .family contract => contract.representation = .metricForm
  | _ => False

/-- Every binding except `flat` and `sharp`. -/
def MetricFree : PrimitiveBinding → Prop
  | .metricFlat .. | .metricSharp .. => False
  | _ => True

theorem lookup_append (env extra : Environment) (id : DeclId) :
    lookup (env ++ extra) id = (lookup env id).or (lookup extra id) := by
  unfold lookup
  rw [List.find?_append]
  cases env.find? (fun entry => entry.id == id) <;> rfl

theorem found_of_isSmoothFamily {env : Environment} {id : DeclId} (h : isSmoothFamily env id = true) : (lookup env id).isSome = true := by
  unfold isSmoothFamily at h
  split at h <;> simp_all

theorem found_of_fiberVariance {env : Environment} {id : DeclId} (h : (fiberVariance? env id).isSome = true) :
    (lookup env id).isSome = true := by
  unfold fiberVariance? at h
  split at h <;> simp_all

theorem found_of_familyRepresentation {env : Environment} {id : DeclId} {representation : FamilyRepresentation}
    (h : (familyRepresentation env id == some representation) = true) : (lookup env id).isSome = true := by
  unfold familyRepresentation at h
  split at h <;> simp_all

theorem found_of_isRelativeFamily {env : Environment} {id : DeclId} (h : isRelativeFamily env id = true) :
    (lookup env id).isSome = true := found_of_familyRepresentation h

section Weakening

variable {env extra : Environment} (metric : ∀ entry ∈ extra, MetricDeclaration entry.declaration)
include metric

theorem lookup_cases (id : DeclId) :
    lookup (env ++ extra) id = lookup env id ∨
      (lookup env id = none ∧ ∃ declaration, lookup (env ++ extra) id = some declaration ∧
        MetricDeclaration declaration) := by
  rw [lookup_append]
  cases found : lookup env id with
  | some declaration => exact .inl rfl
  | none =>
    cases appended : lookup extra id with
    | none => exact .inl rfl
    | some declaration =>
      unfold lookup at appended
      cases entry : extra.find? (fun entry => entry.id == id) with
      | none => simp [entry] at appended
      | some e =>
        simp only [entry, Option.map_some, Option.some.injEq] at appended
        refine .inr ⟨rfl, declaration, rfl, ?_⟩
        rw [← appended]
        exact metric e (List.mem_of_find?_eq_some entry)

theorem lookup_of_isSome {id : DeclId} (found : (lookup env id).isSome = true) :
    lookup (env ++ extra) id = lookup env id := by
  rcases lookup_cases (env := env) metric id with same | ⟨none, _⟩
  · exact same
  · rw [none] at found
    cases found

/-! ### Views that treat a metric declaration as a missing one -/

-- The proof pattern of every view below: on an inherited entry the view is
-- unchanged, and on an appended metric declaration it agrees with `none`.
set_option hygiene false in
local macro "view_append" lemma:ident id:term : tactic => `(tactic| (
  rcases lookup_cases (env := env) metric $id with same | ⟨none, declaration, found, kind⟩
  · simp only [$lemma:ident, same]
  · simp only [$lemma:ident, none, found]
    cases declaration <;> simp_all [MetricDeclaration]))

theorem isMarker_append (id : DeclId) : isMarker (env ++ extra) id = isMarker env id := by
  view_append isMarker id

theorem implementationMarker_append (id : DeclId) :
    implementationMarker (env ++ extra) id = implementationMarker env id := by
  view_append implementationMarker id

theorem affineImplementation_append (id : DeclId) :
    affineImplementation (env ++ extra) id = affineImplementation env id := by
  view_append affineImplementation id

theorem affineData_append (id : DeclId) : affineData? (env ++ extra) id = affineData? env id := by
  view_append affineData? id

theorem smoothCoordinates_append (id : DeclId) :
    smoothCoordinates? (env ++ extra) id = smoothCoordinates? env id := by
  view_append smoothCoordinates? id

theorem smoothDimension_append (id : DeclId) :
    smoothDimension? (env ++ extra) id = smoothDimension? env id := by
  simp only [smoothDimension?, smoothCoordinates_append metric]

theorem domain_append (id : DeclId) : Indexed.domain (env ++ extra) id = Indexed.domain env id := by
  view_append Indexed.domain id

theorem isDomain_append (id : DeclId) : isDomain (env ++ extra) id = isDomain env id := by
  view_append isDomain id

theorem objectImplementation_append (id : DeclId) :
    (lookup (env ++ extra) id).bind Declaration.objectImplementation? =
      (lookup env id).bind Declaration.objectImplementation? := by
  rcases lookup_cases (env := env) metric id with same | ⟨none, declaration, found, kind⟩
  · rw [same]
  · rw [none, found]
    cases declaration <;> simp_all [MetricDeclaration, Declaration.objectImplementation?]

theorem fiberVariance_append (id : DeclId) : fiberVariance? (env ++ extra) id = fiberVariance? env id := by
  view_append fiberVariance? id

theorem isTapeFamily_append (id : DeclId) : isTapeFamily (env ++ extra) id = isTapeFamily env id := by
  view_append isTapeFamily id

theorem isSmoothFamily_append (id : DeclId) : isSmoothFamily (env ++ extra) id = isSmoothFamily env id := by
  view_append isSmoothFamily id

theorem affineGlobal_append (id : DeclId) : affineGlobal (env ++ extra) id = affineGlobal env id := by
  rcases lookup_cases (env := env) metric id with same | ⟨none, declaration, found, kind⟩
  · simp only [affineGlobal, same, affineImplementation_append metric]
  · simp only [affineGlobal, none, found]
    cases declaration <;> simp_all [MetricDeclaration]

theorem implementationSupports_append (id : DeclId) (capability : Capability) :
    implementationSupports (env ++ extra) id capability = implementationSupports env id capability := by
  view_append implementationSupports id

/-- A fresh `metric_form` family is the only way a family representation can
appear; every metric-free contract compares with another representation. -/
theorem familyRepresentation_append (id : DeclId) {representation : FamilyRepresentation}
    (other : representation ≠ .metricForm) :
    (familyRepresentation (env ++ extra) id == some representation) =
      (familyRepresentation env id == some representation) := by
  rcases lookup_cases (env := env) metric id with same | ⟨none, declaration, found, kind⟩
  · simp only [familyRepresentation, same]
  · simp only [familyRepresentation, none, found]
    cases declaration <;> simp_all [MetricDeclaration]
    exact fun h => other h.symm

theorem isRelativeFamily_append (id : DeclId) : isRelativeFamily (env ++ extra) id = isRelativeFamily env id := by
  simp only [isRelativeFamily, familyRepresentation_append metric id (by decide : FamilyRepresentation.relative ≠ _)]

theorem globalObject_append (id : DeclId) : globalObject (env ++ extra) id = globalObject env id := by
  simp only [globalObject, objectImplementation_append metric]

/-! ### Derived views -/

theorem type_append (ref : Indexed.ObjectRef) : ref.type? (env ++ extra) = ref.type? env := by
  cases ref with
  | global id => simp only [ObjectRef.type?, objectImplementation_append metric, implementationMarker_append metric]
  | «local» => rfl

theorem implementations_append (type : ObjectType) :
    type.implementations (env ++ extra) = type.implementations env := by
  simp only [ObjectType.implementations, domain_append metric, implementationMarker_append metric]

theorem objectTypeValid_append (type : ObjectType) : type.Valid (env ++ extra) ↔ type.Valid env := by
  simp only [ObjectType.Valid, isDomain_append metric, isMarker_append metric, implementations_append metric]

theorem supports_append (type : ObjectType) (capability : Capability) :
    type.Supports (env ++ extra) capability ↔ type.Supports env capability := by
  simp only [ObjectType.Supports, objectTypeValid_append metric, implementations_append metric,
    implementationSupports_append metric]

theorem refValid_append (ref : Indexed.ObjectRef) : ref.Valid (env ++ extra) ↔ ref.Valid env := by
  simp only [ObjectRef.Valid, type_append metric, objectTypeValid_append metric]

theorem implementationType_append (id : DeclId) :
    implementationType (env ++ extra) id = implementationType env id := by
  simp only [implementationType, implementationMarker_append metric]

theorem affineChain_append (fuel : Nat) (id : DeclId) :
    affineChain (env ++ extra) fuel id = affineChain env fuel id := by
  induction fuel generalizing id with
  | zero => rfl
  | succ fuel ih => simp only [affineChain, affineData_append metric, ih]

theorem chainOf_append (id : DeclId) : chainOf (env ++ extra) id = chainOf env id := by
  simp only [chainOf, affineChain_append metric]

theorem onChain_append (object base : DeclId) : onChain (env ++ extra) object base = onChain env object base := by
  simp only [onChain, chainOf_append metric]

theorem chainImages_append (fuel : Nat) (object base : DeclId) :
    chainImages (env ++ extra) fuel object base = chainImages env fuel object base := by
  induction fuel generalizing object with
  | zero => rfl
  | succ fuel ih => simp only [chainImages, affineData_append metric, ih]

theorem structureImages_append (object base : DeclId) :
    structureImages? (env ++ extra) object base = structureImages? env object base := by
  simp only [structureImages?, structureImagesWithin, chainImages_append metric]

theorem plainFiber_append (id : DeclId) : plainFiber? (env ++ extra) id = plainFiber? env id := by
  simp only [plainFiber?, affineData_append metric]

theorem affineArity_append (id : DeclId) : affineArity (env ++ extra) id = affineArity env id := by
  simp only [affineArity, affineData_append metric]

theorem freeAffine_append (id : DeclId) : freeAffine (env ++ extra) id = freeAffine env id := by
  simp only [freeAffine, affineData_append metric]

theorem pointBase_append (id : DeclId) : pointBase (env ++ extra) id = pointBase env id := by
  simp only [pointBase, affineData_append metric]

theorem smoothArity_append (id : DeclId) : smoothArity (env ++ extra) id = smoothArity env id := by
  simp only [smoothArity, smoothDimension_append metric]

theorem smoothEndpoints_append (application : Application) :
    smoothEndpoints? (env ++ extra) application = smoothEndpoints? env application := by
  simp only [smoothEndpoints?, smoothDimension_append metric]

theorem accepts_append (parameter : Indexed.Parameter) (index : Index) :
    parameter.Accepts (env ++ extra) index ↔ parameter.Accepts env index := by
  cases parameter <;> cases index <;>
    simp only [Parameter.Accepts, isDomain_append metric, isMarker_append metric, type_append metric,
      objectTypeValid_append metric, implementations_append metric, domain_append metric]

theorem constraintHolds_append (indices : List Index) (constraint : Constraint) :
    constraintHolds (env ++ extra) indices constraint = constraintHolds env indices constraint := by
  cases constraint <;>
    simp only [constraintHolds, type_append metric, onChain_append metric, smoothDimension_append metric]

theorem constraintHolds_append' (indices : List Index) :
    constraintHolds (env ++ extra) indices = constraintHolds env indices :=
  funext (constraintHolds_append metric indices)

/-- An application whose family is an entry of `env` is valid after the
extension exactly when it was valid before. -/
theorem validApplication_of_found {application : Application}
    (found : (lookup env application.family).isSome = true) :
    validApplication (env ++ extra) application = validApplication env application := by
  simp only [validApplication, lookup_of_isSome metric found, accepts_append metric,
    constraintHolds_append' metric]

theorem validApplication_mk_of_found {family : DeclId} {indices : List Index}
    (found : (lookup env family).isSome = true) :
    validApplication (env ++ extra) ⟨family, indices⟩ = validApplication env ⟨family, indices⟩ :=
  validApplication_of_found metric (application := ⟨family, indices⟩) found

theorem relativeConstantValid_append (application : Application) (map : AlgebraRuntime.Map) :
    relativeConstantValid (env ++ extra) application map = relativeConstantValid env application map := by
  simp only [relativeConstantValid, isRelativeFamily_append metric, affineData_append metric,
    structureImages_append metric]
  cases relative : isRelativeFamily env application.family
  · simp
  · simp only [validApplication_of_found metric (application := application) (found_of_isRelativeFamily relative)]

theorem relativeIsoValid_append (forward backward : Application × AlgebraRuntime.Map) :
    relativeIsoValid (env ++ extra) forward backward = relativeIsoValid env forward backward := by
  simp only [relativeIsoValid, relativeIsoCheck, relativeConstantValid_append metric, affineData_append metric]

theorem relativeCartesianValid_append (first second inverse : Application × AlgebraRuntime.Map) (fiber : DeclId) :
    relativeCartesianValid (env ++ extra) first second inverse fiber =
      relativeCartesianValid env first second inverse fiber := by
  simp only [relativeCartesianValid, relativeCartesianCheck, relativeConstantValid_append metric,
    plainFiber_append metric, affineData_append metric]

/-- **Weakening of binding validity.** Appending metric declarations does not
change the validity of any binding other than `flat` and `sharp`. -/
theorem validPrimitiveBinding_metric_weakening {binding : PrimitiveBinding} (free : MetricFree binding) :
    validPrimitiveBinding (env ++ extra) binding = validPrimitiveBinding env binding := by
  cases binding with
  | metricFlat | metricSharp => exact absurd free id
  | origin domain family base =>
    simp only [validPrimitiveBinding, originContract, supports_append metric,
      familyRepresentation_append metric family (by decide : FamilyRepresentation.point ≠ _)]
    cases point : familyRepresentation env family == some .point
    · simp
    · simp only [validApplication_mk_of_found metric (found_of_familyRepresentation point)]
  | identity domain family =>
    simp only [validPrimitiveBinding, identityContract, objectTypeValid_append metric,
      familyRepresentation_append metric family (by decide : FamilyRepresentation.morphism ≠ _)]
    cases morphism : familyRepresentation env family == some .morphism
    · simp
    · simp only [validApplication_mk_of_found metric (found_of_familyRepresentation morphism)]
  | smoothConstant application map =>
    simp only [validPrimitiveBinding, smoothConstantValid, isSmoothFamily_append metric,
      smoothEndpoints_append metric]
    cases smooth : isSmoothFamily env application.family
    · simp
    · simp only [validApplication_of_found metric (application := application) (found_of_isSmoothFamily smooth)]
  | smoothIntPoint family object point =>
    simp only [validPrimitiveBinding, smoothIntPointValid, isSmoothFamily_append metric,
      smoothDimension_append metric]
    cases smooth : isSmoothFamily env family
    · simp
    · simp only [validApplication_mk_of_found metric (found_of_isSmoothFamily smooth)]
  | fiberVector family smooth object =>
    simp only [validPrimitiveBinding, fiberVectorValid, fiberVariance_append metric, isSmoothFamily_append metric,
      smoothDimension_append metric]
    cases fiber : (fiberVariance? env family).isSome
    · simp
    · simp only [validApplication_mk_of_found metric (found_of_fiberVariance fiber)]
  | fiberComponent family object coordinate =>
    simp only [validPrimitiveBinding, fiberComponentValid, fiberVariance_append metric, smoothArity_append metric]
    cases fiber : (fiberVariance? env family).isSome
    · simp
    · simp only [validApplication_mk_of_found metric (found_of_fiberVariance fiber)]
  | compose family =>
    simp only [validPrimitiveBinding,
      familyRepresentation_append metric family (by decide : FamilyRepresentation.morphism ≠ _)]
  | apply maps points =>
    simp only [validPrimitiveBinding,
      familyRepresentation_append metric maps (by decide : FamilyRepresentation.morphism ≠ _),
      familyRepresentation_append metric points (by decide : FamilyRepresentation.point ≠ _)]
  | _ =>
    simp only [validPrimitiveBinding, implementationType_append metric, affineImplementation_append metric,
      objectTypeValid_append metric, affineGlobal_append metric, refValid_append metric, supports_append metric,
      relativeConstantValid_append metric, isRelativeFamily_append metric, onChain_append metric,
      affineData_append metric, affineArity_append metric, freeAffine_append metric, pointBase_append metric,
      plainFiber_append metric, relativeIsoValid_append metric, relativeCartesianValid_append metric,
      isSmoothFamily_append metric, fiberAtValid, fiberEqualValid, fiberPairingValid, cotangentPullbackValid,
      differentialValid, linearizeValid, cotangentBackwardValid, fiberVariance_append metric,
      isTapeFamily_append metric, smoothDimension_append metric]

/-- The propositional contract is unchanged as well. -/
theorem primitiveBindingValid_metric_weakening {binding : PrimitiveBinding} (free : MetricFree binding) :
    binding.Valid (env ++ extra) ↔ binding.Valid env := by
  rw [← Audit.validPrimitiveBinding_iff, ← Audit.validPrimitiveBinding_iff,
    validPrimitiveBinding_metric_weakening metric free]

theorem fiberVectorValue_append (family : DeclId) (point : SmoothRuntime.Program) (values : List Value) :
    fiberVectorValue (env ++ extra) family point values = fiberVectorValue env family point values := by
  simp only [fiberVectorValue, fiberVariance_append metric]

/-- **Weakening of evaluation.** Appending metric declarations does not change
the value of any primitive. Only `global`, `origin` and `fiber_vector` consult
the environment, and none of them reads a metric declaration. -/
theorem evalPrimitive_metric_weakening (binding : PrimitiveBinding) (values : List Value) :
    evalPrimitive (env ++ extra) binding values = evalPrimitive env binding values := by
  unfold evalPrimitive
  simp only [globalObject_append metric, fiberVectorValue_append metric]

/-- **The differential is metric-free.** Its validity and its value are the
same with and without appended metric declarations. -/
theorem differential_metric_free (smooth cotangent line : DeclId) (values : List Value) :
    validPrimitiveBinding (env ++ extra) (.differential smooth cotangent line) =
        validPrimitiveBinding env (.differential smooth cotangent line) ∧
      evalPrimitive (env ++ extra) (.differential smooth cotangent line) values =
        evalPrimitive env (.differential smooth cotangent line) values :=
  ⟨validPrimitiveBinding_metric_weakening metric trivial, evalPrimitive_metric_weakening metric _ values⟩

/-- **The cotangent pullback is metric-free**, in both modes. -/
theorem cotangentPullback_metric_free (smooth cotangent : DeclId) (mode : SmoothRuntime.PullbackMode)
    (values : List Value) :
    validPrimitiveBinding (env ++ extra) (.cotangentPullback smooth cotangent mode) =
        validPrimitiveBinding env (.cotangentPullback smooth cotangent mode) ∧
      evalPrimitive (env ++ extra) (.cotangentPullback smooth cotangent mode) values =
        evalPrimitive env (.cotangentPullback smooth cotangent mode) values :=
  ⟨validPrimitiveBinding_metric_weakening metric trivial, evalPrimitive_metric_weakening metric _ values⟩

end Weakening

end VastitasOracle.SmoothMetricWeakening
