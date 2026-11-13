import VastitasOracle.SmoothMetricWeakening

set_option autoImplicit false

/-! **Nature weakening (C17; ADR 0002 "Independence of `std`" and
"Evidence").** Adding `nature` declarations changes the validity of no
non-nature declaration (one that `NatureDimension` does not check), no
binding's validity and no evaluation. Nature declarations can change each
other's validity, which these theorems do not cover: `checkBaseDimension`
counts every base dimension, so a 17th base dimension makes every base
dimension invalid.

A *nature declaration* (`NatureDeclaration`) is a base dimension, a quantity,
a reading, a scale, a physical metric, or a family with the `reading` or
`physical_metric` representation, valid or not. The kernel keeps
declarations in source order, so nature declarations may sit anywhere. For
every list `extra` of nature declarations:

- **declarations:** if the ids of `pre ++ extra ++ post` are unique, as in
  every valid environment, then for every class ranking `ranks` and every
  entry that `NatureDimension` does not check (`NatureCheck`): markers,
  implementations, classifications, globals, families, presented and smooth
  objects, std metrics, metric evidence and frames,
  `entry.Valid (pre ++ extra ++ post) ranks ↔ entry.Valid (pre ++ post) ranks`
  (`entryValid_nature_insertion`, `validEntry_nature_insertion`, `…_of_valid`);
- **bindings:** for every binding, `flat` and `sharp` included,
  `validPrimitiveBinding` and `evalPrimitive` are unchanged
  (`validPrimitiveBinding_nature_insertion`, `evalPrimitive_nature_insertion`,
  `…_of_valid`);
- **at the end:** the same equations for `env ++ extra` and `env` hold with
  no hypothesis on ids (`entryValid_nature_weakening`,
  `validPrimitiveBinding_nature_weakening`, `evalPrimitive_nature_weakening`).

In particular a std metric with its evidence is valid with and without any
reading of its object and any interpretation of it, and `flat` and `sharp`
keep their validity and their values (`metric_nature_free`,
`metric_valid_with_reading`, `flat_sharp_nature_free`). Read from right to
left, the same equations say that removing nature declarations changes
nothing either.

All forms are instances of one statement about a `NatureExtension small big`:
each lookup in `big` is the lookup in `small` or a nature declaration where
`small` has nothing, and both agree on `coefficientConsistent`, the one
non-lookup view that a non-nature check reads. An appended entry never
shadows an entry of `env`, because `lookup` returns the first entry with an id
(`natureExtension_append`); with unique ids an inserted block behaves like an
appended one (`natureExtension_insert`, by
`SmoothMetricWeakening.lookup_insert`). The proof shows that every view that a
non-nature check or a binding contract reads treats a nature declaration
exactly like a missing one. The representations `reading` and
`physical_metric` are compared only by the nature checks
(`isReadingFamily`, `isPhysicalMetricFamily`).

**Boundary.** The declaration statements hold for every class ranking. That
`classRanks` itself is unchanged is not proved here: its fixpoint loop is
private to the kernel and takes the environment's length as fuel, so the
statement about whole environments is not stated. The frame bindings of
Stage 4 read frame declarations, frame-array and frame-map families and fiber
families, never a nature declaration; their cases follow
`SmoothMetricWeakening`. -/
namespace VastitasOracle.NatureWeakening

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasOracle.SmoothMetricWeakening (lookup_append lookup_insert found_of_isSmoothFamily
  found_of_fiberVariance found_of_familyRepresentation found_of_isRelativeFamily found_of_frameFiberVariance
  found_of_isFrameMapFamily isSome_of_beq_some)

/-- The declarations that `NatureDimension` checks: base dimensions,
quantities, readings, scales and physical metrics. -/
def NatureCheck : Declaration → Prop
  | .baseDimension | .quantity .. | .reading .. | .scale .. | .physicalMetric .. => True
  | _ => False

/-- A declaration that only `nature::dimension` contributes: one that
`NatureDimension` checks, or a family with the `reading` or
`physical_metric` representation. -/
def NatureDeclaration : Declaration → Prop
  | .baseDimension | .quantity .. | .reading .. | .scale .. | .physicalMetric .. => True
  | .family contract => contract.representation = .reading ∨ contract.representation = .physicalMetric
  | _ => False

/-- `big` extends `small` by nature declarations: each lookup in `big` is the
lookup in `small`, or a nature declaration where `small` has nothing, and the
two environments agree on the coefficient kinds of their implementations. -/
structure NatureExtension (small big : Environment) : Prop where
  lookup : ∀ id, lookup big id = lookup small id ∨
    (lookup small id = none ∧ ∃ declaration, lookup big id = some declaration ∧ NatureDeclaration declaration)
  coefficients : ∀ marker kind, coefficientConsistent big marker kind = coefficientConsistent small marker kind

theorem found_of_isMetricFamily {env : Environment} {id : DeclId} (h : isMetricFamily env id = true) :
    (lookup env id).isSome = true := by
  unfold isMetricFamily at h
  split at h <;> simp_all

theorem found_of_fiberVariance_beq {env : Environment} {id : DeclId} {variance : Variance}
    (h : (fiberVariance? env id == some variance) = true) : (lookup env id).isSome = true :=
  found_of_fiberVariance (by simp only [beq_iff_eq] at h; simp [h])

section Extension

variable {small big : Environment} (ext : NatureExtension small big)
include ext

theorem lookup_of_isSome {id : DeclId} (found : (lookup small id).isSome = true) :
    lookup big id = lookup small id := by
  rcases ext.lookup id with same | ⟨none, _⟩
  · exact same
  · rw [none] at found
    cases found

/-- A declaration that is not a nature declaration is found in `big` exactly
when it is found in `small`. -/
theorem lookup_eq_some_iff {id : DeclId} {declaration : Declaration} (other : ¬ NatureDeclaration declaration) :
    lookup big id = some declaration ↔ lookup small id = some declaration := by
  rcases ext.lookup id with same | ⟨none, added, found, kind⟩
  · rw [same]
  · rw [none, found]
    constructor
    · intro h
      cases h
      exact absurd kind other
    · intro h
      cases h

/-! ### Views that treat a nature declaration as a missing one -/

-- The proof pattern of every view below: on an inherited entry the view is
-- unchanged, and on an added nature declaration it agrees with `none`.
set_option hygiene false in
local macro "view_append" lemma:ident id:term : tactic => `(tactic| (
  rcases ext.lookup $id with same | ⟨none, declaration, found, kind⟩
  · simp only [$lemma:ident, same]
  · simp only [$lemma:ident, none, found]
    cases declaration <;> simp only [NatureDeclaration] at kind <;> (try rcases kind with kind | kind) <;>
      simp_all))

theorem isMarker_append (id : DeclId) : isMarker big id = isMarker small id := by
  view_append isMarker id

theorem implementationMarker_append (id : DeclId) :
    implementationMarker big id = implementationMarker small id := by
  view_append implementationMarker id

theorem affineImplementation_append (id : DeclId) :
    affineImplementation big id = affineImplementation small id := by
  view_append affineImplementation id

theorem presentedImplementation_append (id : DeclId) :
    presentedImplementation big id = presentedImplementation small id := by
  view_append presentedImplementation id

theorem smoothImplementation_append (id : DeclId) :
    smoothImplementation big id = smoothImplementation small id := by
  view_append smoothImplementation id

theorem affineData_append (id : DeclId) : affineData? big id = affineData? small id := by
  view_append affineData? id

theorem smoothCoordinates_append (id : DeclId) :
    smoothCoordinates? big id = smoothCoordinates? small id := by
  view_append smoothCoordinates? id

theorem smoothDimension_append (id : DeclId) :
    smoothDimension? big id = smoothDimension? small id := by
  simp only [smoothDimension?, smoothCoordinates_append ext]

theorem domain_append (id : DeclId) : Indexed.domain big id = Indexed.domain small id := by
  view_append Indexed.domain id

theorem isDomain_append (id : DeclId) : isDomain big id = isDomain small id := by
  view_append isDomain id

theorem objectImplementation_append (id : DeclId) :
    (lookup big id).bind Declaration.objectImplementation? =
      (lookup small id).bind Declaration.objectImplementation? := by
  rcases ext.lookup id with same | ⟨none, declaration, found, kind⟩
  · rw [same]
  · rw [none, found]
    cases declaration <;> simp_all [NatureDeclaration, Declaration.objectImplementation?]

theorem fiberVariance_append (id : DeclId) : fiberVariance? big id = fiberVariance? small id := by
  view_append fiberVariance? id

theorem isTapeFamily_append (id : DeclId) : isTapeFamily big id = isTapeFamily small id := by
  view_append isTapeFamily id

theorem isSmoothFamily_append (id : DeclId) : isSmoothFamily big id = isSmoothFamily small id := by
  view_append isSmoothFamily id

theorem isMetricFamily_append (id : DeclId) : isMetricFamily big id = isMetricFamily small id := by
  view_append isMetricFamily id

theorem frameData_append (id : DeclId) : frameData? big id = frameData? small id := by
  view_append frameData? id

theorem frameFamily_append (id : DeclId) : frameFamily? big id = frameFamily? small id := by
  simp only [frameFamily?, frameData_append ext]

theorem frameObject_append (id : DeclId) : frameObject? big id = frameObject? small id := by
  simp only [frameObject?, frameData_append ext]

theorem frameFiberVariance_append (id : DeclId) : frameFiberVariance? big id = frameFiberVariance? small id := by
  view_append frameFiberVariance? id

theorem isFrameMapFamily_append (id : DeclId) : isFrameMapFamily big id = isFrameMapFamily small id := by
  view_append isFrameMapFamily id

theorem frameDeclared_append (frame : FrameRef) : frameDeclared big frame = frameDeclared small frame := by
  simp only [frameDeclared, frameData_append ext]

theorem affineGlobal_append (id : DeclId) : affineGlobal big id = affineGlobal small id := by
  rcases ext.lookup id with same | ⟨none, declaration, found, kind⟩
  · simp only [affineGlobal, same, affineImplementation_append ext]
  · simp only [affineGlobal, none, found]
    cases declaration <;> simp_all [NatureDeclaration]

theorem implementationSupports_append (id : DeclId) (capability : Capability) :
    implementationSupports big id capability = implementationSupports small id capability := by
  view_append implementationSupports id

theorem metricData_append (id : DeclId) : metricData? big id = metricData? small id := by
  rcases ext.lookup id with same | ⟨none, declaration, found, kind⟩
  · simp only [metricData?, same, smoothDimension_append ext]
  · simp only [metricData?, none, found]
    cases declaration <;> simp_all [NatureDeclaration]

/-- A nature family is the only way a nature family representation can
appear; every other view compares with another representation. -/
theorem familyRepresentation_eq_append (id : DeclId) {representation : FamilyRepresentation}
    (other : representation ≠ .reading ∧ representation ≠ .physicalMetric) :
    familyRepresentation big id = some representation ↔ familyRepresentation small id = some representation := by
  rcases ext.lookup id with same | ⟨none, declaration, found, kind⟩
  · simp only [familyRepresentation, same]
  · simp only [familyRepresentation, none, found]
    cases declaration <;> simp only [NatureDeclaration] at kind <;> (try rcases kind with kind | kind) <;>
      simp_all [eq_comm]

theorem familyRepresentation_append (id : DeclId) {representation : FamilyRepresentation}
    (other : representation ≠ .reading ∧ representation ≠ .physicalMetric) :
    (familyRepresentation big id == some representation) =
      (familyRepresentation small id == some representation) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact familyRepresentation_eq_append ext id other

theorem isRelativeFamily_append (id : DeclId) : isRelativeFamily big id = isRelativeFamily small id := by
  simp only [isRelativeFamily, familyRepresentation_append ext id (representation := .relative) (by decide)]

theorem globalObject_append (id : DeclId) : globalObject big id = globalObject small id := by
  simp only [globalObject, objectImplementation_append ext]

/-! ### Derived views -/

theorem type_append (ref : Indexed.ObjectRef) : ref.type? big = ref.type? small := by
  cases ref with
  | global id => simp only [ObjectRef.type?, objectImplementation_append ext, implementationMarker_append ext]
  | «local» => rfl

theorem implementations_append (type : ObjectType) :
    type.implementations big = type.implementations small := by
  simp only [ObjectType.implementations, domain_append ext, implementationMarker_append ext]

theorem objectTypeValid_append (type : ObjectType) : type.Valid big ↔ type.Valid small := by
  simp only [ObjectType.Valid, isDomain_append ext, isMarker_append ext, implementations_append ext]

theorem supports_append (type : ObjectType) (capability : Capability) :
    type.Supports big capability ↔ type.Supports small capability := by
  simp only [ObjectType.Supports, objectTypeValid_append ext, implementations_append ext,
    implementationSupports_append ext]

theorem refValid_append (ref : Indexed.ObjectRef) : ref.Valid big ↔ ref.Valid small := by
  simp only [ObjectRef.Valid, type_append ext, objectTypeValid_append ext]

theorem implementationType_append (id : DeclId) :
    implementationType big id = implementationType small id := by
  simp only [implementationType, implementationMarker_append ext]

theorem affineChain_append (fuel : Nat) (id : DeclId) :
    affineChain big fuel id = affineChain small fuel id := by
  induction fuel generalizing id with
  | zero => rfl
  | succ fuel ih => simp only [affineChain, affineData_append ext, ih]

theorem chainOf_append (id : DeclId) : chainOf big id = chainOf small id := by
  simp only [chainOf, affineChain_append ext]

theorem onChain_append (object base : DeclId) : onChain big object base = onChain small object base := by
  simp only [onChain, chainOf_append ext]

theorem chainImages_append (fuel : Nat) (object base : DeclId) :
    chainImages big fuel object base = chainImages small fuel object base := by
  induction fuel generalizing object with
  | zero => rfl
  | succ fuel ih => simp only [chainImages, affineData_append ext, ih]

theorem structureImages_append (object base : DeclId) :
    structureImages? big object base = structureImages? small object base := by
  simp only [structureImages?, structureImagesWithin, chainImages_append ext]

theorem plainFiber_append (id : DeclId) : plainFiber? big id = plainFiber? small id := by
  simp only [plainFiber?, affineData_append ext]

theorem affineArity_append (id : DeclId) : affineArity big id = affineArity small id := by
  simp only [affineArity, affineData_append ext]

theorem freeAffine_append (id : DeclId) : freeAffine big id = freeAffine small id := by
  simp only [freeAffine, affineData_append ext]

theorem pointBase_append (id : DeclId) : pointBase big id = pointBase small id := by
  simp only [pointBase, affineData_append ext]

theorem smoothArity_append (id : DeclId) : smoothArity big id = smoothArity small id := by
  simp only [smoothArity, smoothDimension_append ext]

theorem smoothEndpoints_append (application : Application) :
    smoothEndpoints? big application = smoothEndpoints? small application := by
  simp only [smoothEndpoints?, smoothDimension_append ext]

theorem accepts_append (parameter : Indexed.Parameter) (index : Index) :
    parameter.Accepts big index ↔ parameter.Accepts small index := by
  cases parameter <;> cases index <;>
    simp only [Parameter.Accepts, isDomain_append ext, isMarker_append ext, type_append ext,
      objectTypeValid_append ext, implementations_append ext, domain_append ext, frameFamily_append ext]

theorem constraintHolds_append (indices : List Index) (constraint : Constraint) :
    constraintHolds big indices constraint = constraintHolds small indices constraint := by
  cases constraint <;>
    simp only [constraintHolds, type_append ext, onChain_append ext, smoothDimension_append ext]

theorem constraintHolds_append' (indices : List Index) :
    constraintHolds big indices = constraintHolds small indices :=
  funext (constraintHolds_append ext indices)

/-- An application whose family is an entry of `small` is valid after the
extension exactly when it was valid before. -/
theorem validApplication_of_found {application : Application}
    (found : (lookup small application.family).isSome = true) :
    validApplication big application = validApplication small application := by
  simp only [validApplication, lookup_of_isSome ext found, accepts_append ext,
    constraintHolds_append' ext]

theorem validApplication_mk_of_found {family : DeclId} {indices : List Index}
    (found : (lookup small family).isSome = true) :
    validApplication big ⟨family, indices⟩ = validApplication small ⟨family, indices⟩ :=
  validApplication_of_found ext (application := ⟨family, indices⟩) found

theorem relativeConstantValid_append (application : Application) (map : AlgebraRuntime.Map) :
    relativeConstantValid big application map = relativeConstantValid small application map := by
  simp only [relativeConstantValid, isRelativeFamily_append ext, affineData_append ext,
    structureImages_append ext]
  cases relative : isRelativeFamily small application.family
  · simp
  · simp only [validApplication_of_found ext (application := application) (found_of_isRelativeFamily relative)]

theorem relativeIsoValid_append (forward backward : Application × AlgebraRuntime.Map) :
    relativeIsoValid big forward backward = relativeIsoValid small forward backward := by
  simp only [relativeIsoValid, relativeIsoCheck, relativeConstantValid_append ext, affineData_append ext]

theorem relativeCartesianValid_append (first second inverse : Application × AlgebraRuntime.Map) (fiber : DeclId) :
    relativeCartesianValid big first second inverse fiber =
      relativeCartesianValid small first second inverse fiber := by
  simp only [relativeCartesianValid, relativeCartesianCheck, relativeConstantValid_append ext,
    plainFiber_append ext, affineData_append ext]

/-! ### Metrics -/

theorem metricFlatValid_append (metric object : DeclId) (gram : SmoothRuntime.Matrix) (tangent cotangent : DeclId) :
    metricFlatValid big metric object gram tangent cotangent =
      metricFlatValid small metric object gram tangent cotangent := by
  simp only [metricFlatValid, metricData_append ext, fiberVariance_append ext]
  cases metricData? small metric with
  | none => rfl
  | some data =>
    obtain ⟨object', n, gram'⟩ := data
    simp only
    cases tangentFamily : fiberVariance? small tangent == some .tangent
    · simp
    · cases cotangentFamily : fiberVariance? small cotangent == some .cotangent
      · simp
      · simp only [validApplication_mk_of_found ext (found_of_fiberVariance_beq tangentFamily),
          validApplication_mk_of_found ext (found_of_fiberVariance_beq cotangentFamily)]

theorem metricSharpValid_append (metric evidence object : DeclId) (gram inverse : SmoothRuntime.Matrix)
    (cotangent tangent : DeclId) :
    metricSharpValid big metric evidence object gram inverse cotangent tangent =
      metricSharpValid small metric evidence object gram inverse cotangent tangent := by
  have guarded : ∀ (first : Bool),
      (first && (fiberVariance? small cotangent == some .cotangent) && (fiberVariance? small tangent == some .tangent) &&
        validApplication big ⟨cotangent, [.object (.global object)]⟩ &&
        validApplication big ⟨tangent, [.object (.global object)]⟩) =
      (first && (fiberVariance? small cotangent == some .cotangent) && (fiberVariance? small tangent == some .tangent) &&
        validApplication small ⟨cotangent, [.object (.global object)]⟩ &&
        validApplication small ⟨tangent, [.object (.global object)]⟩) := by
    intro first
    cases cotangentFamily : fiberVariance? small cotangent == some .cotangent
    · simp
    · cases tangentFamily : fiberVariance? small tangent == some .tangent
      · simp
      · simp only [validApplication_mk_of_found ext (found_of_fiberVariance_beq tangentFamily),
          validApplication_mk_of_found ext (found_of_fiberVariance_beq cotangentFamily)]
  rcases ext.lookup evidence with same | ⟨none, declaration, found, kind⟩
  · simp only [metricSharpValid, metricData_append ext, fiberVariance_append ext, same]
    cases metricData? small metric with
    | none => rfl
    | some data =>
      cases lookup small evidence with
      | none => rfl
      | some declaration =>
        cases declaration <;> try rfl
        rename_i metric' certificate
        cases certificate <;> try rfl
        exact guarded _
  · simp only [metricSharpValid, metricData_append ext, none, found]
    cases metricData? small metric with
    | none => rfl
    | some data => cases declaration <;> simp_all [NatureDeclaration]

/-! ### Binding validity and evaluation -/

/-- **Weakening of binding validity.** A nature extension does not change the
validity of any binding: no binding contract reads a nature declaration. -/
theorem validPrimitiveBinding_of_extension (binding : PrimitiveBinding) :
    validPrimitiveBinding big binding = validPrimitiveBinding small binding := by
  cases binding with
  | metricFlat metric object gram tangent cotangent =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      metricFlatValid_append ext]
  | metricSharp metric evidence object gram inverse cotangent tangent =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      metricSharpValid_append ext]
  | origin domain family base =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, originContract, supports_append ext,
      familyRepresentation_append ext family (representation := .point) (by decide)]
    cases point : familyRepresentation small family == some .point
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_familyRepresentation point)]
  | identity domain family =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, identityContract, objectTypeValid_append ext,
      familyRepresentation_append ext family (representation := .morphism) (by decide)]
    cases morphism : familyRepresentation small family == some .morphism
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_familyRepresentation morphism)]
  | smoothConstant application map =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      smoothConstantValid, isSmoothFamily_append ext,
      smoothEndpoints_append ext]
    cases smooth : isSmoothFamily small application.family
    · simp
    · simp only [validApplication_of_found ext (application := application) (found_of_isSmoothFamily smooth)]
  | relativeIntPoint family object base =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, isRelativeFamily_append ext,
      freeAffine_append ext, pointBase_append ext]
    cases relative : isRelativeFamily small family
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_isRelativeFamily relative)]
  | smoothIntPoint family object point =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      smoothIntPointValid, isSmoothFamily_append ext,
      smoothDimension_append ext]
    cases smooth : isSmoothFamily small family
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_isSmoothFamily smooth)]
  | fiberVector family smooth object =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      fiberVectorValid, fiberVariance_append ext, isSmoothFamily_append ext,
      smoothDimension_append ext]
    cases fiber : (fiberVariance? small family).isSome
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_fiberVariance fiber)]
  | fiberComponent family object coordinate =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      fiberComponentValid, fiberVariance_append ext, smoothArity_append ext]
    cases fiber : (fiberVariance? small family).isSome
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_fiberVariance fiber)]
  | compose family =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract,
      familyRepresentation_append ext family (representation := .morphism) (by decide)]
  | apply maps points =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract,
      familyRepresentation_append ext maps (representation := .morphism) (by decide),
      familyRepresentation_append ext points (representation := .point) (by decide)]
  | frameEncode variance fiber coords frame =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, FrameRegistry.frameEncode, PrimitiveDescriptor.ofBool,
      frameEncodeValid, frameDeclared_append ext, fiberVariance_append ext, frameFiberVariance_append ext]
    cases fiber : fiberVariance? small fiber == some variance
    · simp
    · cases arrays : frameFiberVariance? small coords == some variance
      · simp
      · simp only [validApplication_mk_of_found ext (found_of_fiberVariance (isSome_of_beq_some fiber)),
          validApplication_mk_of_found ext (found_of_frameFiberVariance (isSome_of_beq_some arrays))]
  | frameDecode variance coords fiber frame =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, FrameRegistry.frameDecode, PrimitiveDescriptor.ofBool,
      frameDecodeValid, frameDeclared_append ext, fiberVariance_append ext, frameFiberVariance_append ext]
    cases arrays : frameFiberVariance? small coords == some variance
    · simp
    · cases fiber : fiberVariance? small fiber == some variance
      · simp
      · simp only [validApplication_mk_of_found ext (found_of_fiberVariance (isSome_of_beq_some fiber)),
          validApplication_mk_of_found ext (found_of_frameFiberVariance (isSome_of_beq_some arrays))]
  | frameVector coords smooth object frame =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, FrameRegistry.frameVector, PrimitiveDescriptor.ofBool,
      frameVectorValid, frameFiberVariance_append ext, isSmoothFamily_append ext, frameObject_append ext,
      smoothDimension_append ext]
    cases arrays : (frameFiberVariance? small coords).isSome
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_frameFiberVariance arrays)]
  | frameMatrix smooth map source target =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, FrameRegistry.frameMatrix, PrimitiveDescriptor.ofBool,
      frameMatrixValid, isSmoothFamily_append ext, isFrameMapFamily_append ext, frameDeclared_append ext]
    cases maps : isFrameMapFamily small map
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_isFrameMapFamily maps)]
  | frameTransition smooth map source target =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, FrameRegistry.frameTransition,
      PrimitiveDescriptor.ofBool, frameTransitionValid, isSmoothFamily_append ext, isFrameMapFamily_append ext,
      frameDeclared_append ext]
    cases maps : isFrameMapFamily small map
    · simp
    · simp only [validApplication_mk_of_found ext (found_of_isFrameMapFamily maps)]
  | cotangentJacobian cotangent application map =>
    have contract : ∀ env, validPrimitiveBinding env (.cotangentJacobian cotangent application map) =
        cotangentJacobianValid env cotangent application map := by
      intro env
      simp only [validPrimitiveBinding, PrimitiveBinding.contract]
      split <;> rfl
    rw [contract, contract]
    simp only [cotangentJacobianValid, smoothConstantValid, isSmoothFamily_append ext, smoothEndpoints_append ext,
      fiberVariance_append ext]
    cases smooth : isSmoothFamily small application.family
    · simp
    · cases cotangentFamily : fiberVariance? small cotangent == some .cotangent
      · simp
      · have found : (lookup small cotangent).isSome = true := found_of_fiberVariance_beq cotangentFamily
        simp only [validApplication_of_found ext (application := application) (found_of_isSmoothFamily smooth),
          validApplication_mk_of_found ext found]
  | _ =>
    simp only [validPrimitiveBinding, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
      PrimitiveDescriptor.evidence, implementationType_append ext, affineImplementation_append ext,
      objectTypeValid_append ext, affineGlobal_append ext, refValid_append ext, supports_append ext,
      relativeConstantValid_append ext, isRelativeFamily_append ext, onChain_append ext,
      affineData_append ext, affineArity_append ext, plainFiber_append ext, relativeIsoValid_append ext,
      relativeCartesianValid_append ext,
      isSmoothFamily_append ext, fiberAtValid, fiberEqualValid, fiberPairingValid, cotangentPullbackValid,
      differentialValid, linearizeValid, cotangentBackwardValid, smoothApplyValid, fiberVariance_append ext,
      isTapeFamily_append ext, smoothDimension_append ext,
      -- The frame entries of Stage 4 that read no application.
      FrameRegistry.frameApply, FrameRegistry.frameCoapply, FrameRegistry.frameCompose, FrameRegistry.framePairing,
      FrameRegistry.frameComponent, FrameRegistry.frameEntry, FrameRegistry.frameEqual, FrameRegistry.frameAt,
      frameApplyValid, frameCoapplyValid, frameComposeValid, framePairingValid, frameComponentValid,
      frameEntryValid, frameEqualValid, frameAtValid, frameFiberVariance_append ext, isFrameMapFamily_append ext]

/-- The propositional contract is unchanged as well. -/
theorem primitiveBindingValid_of_extension (binding : PrimitiveBinding) :
    binding.Valid big ↔ binding.Valid small := by
  rw [← Audit.validPrimitiveBinding_iff, ← Audit.validPrimitiveBinding_iff,
    validPrimitiveBinding_of_extension ext binding]

theorem fiberVectorValue_append (family : DeclId) (point : SmoothRuntime.Program) (values : List Value) :
    fiberVectorValue big family point values = fiberVectorValue small family point values := by
  simp only [fiberVectorValue, fiberVariance_append ext]

theorem frameVectorValue_append (coords : DeclId) (point : SmoothRuntime.Program) (values : List Value) :
    frameVectorValue big coords point values = frameVectorValue small coords point values := by
  simp only [frameVectorValue, frameFiberVariance_append ext]

/-- **Weakening of evaluation.** A nature extension does not change the value
of any primitive. Only `global`, `origin`, `fiber_vector` and `frame_vector`
consult the environment, and none of them reads a nature declaration. -/
theorem evalPrimitive_of_extension (binding : PrimitiveBinding) (values : List Value) :
    evalPrimitive big binding values = evalPrimitive small binding values := by
  cases binding
  case cotangentJacobian cotangent application map =>
    simp only [evalPrimitive, PrimitiveBinding.contract]
    split <;> rfl
  all_goals simp only [evalPrimitive, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
    PrimitiveDescriptor.evidence, globalObject_append ext, fiberVectorValue_append ext,
    frameVectorValue_append ext,
    -- The frame entries of Stage 4 read only their embedded frames.
    FrameRegistry.frameEncode, FrameRegistry.frameDecode, FrameRegistry.frameVector,
    FrameRegistry.frameMatrix, FrameRegistry.frameTransition, FrameRegistry.frameApply,
    FrameRegistry.frameCoapply, FrameRegistry.frameCompose, FrameRegistry.framePairing,
    FrameRegistry.frameComponent, FrameRegistry.frameEntry, FrameRegistry.frameEqual, FrameRegistry.frameAt]

/-! ### Declaration validity -/

theorem scalarBaseProfile_append (id : DeclId) : scalarBaseProfile big id = scalarBaseProfile small id := by
  unfold scalarBaseProfile
  rcases ext.lookup id with same | ⟨none, declaration, found, kind⟩
  · rw [same]
    cases lookup small id with
    | none => rfl
    | some declaration =>
      cases declaration with
      | global implementation =>
        simp only [Option.bind_eq_bind, Option.bind_some]
        rcases ext.lookup implementation with same' | ⟨none', declaration', found', kind'⟩
        · rw [same']
        · rw [none', found']
          cases declaration' <;> simp_all [NatureDeclaration]
      | _ => rfl
  · rw [none, found]
    cases declaration <;> simp_all [NatureDeclaration]

theorem representationValid_append (marker : DeclId) (capabilities : List Capability)
    (representation : Representation) :
    representation.Valid big marker capabilities ↔ representation.Valid small marker capabilities := by
  cases representation <;> simp only [Representation.Valid, ext.coefficients, scalarBaseProfile_append ext]

theorem parameterValid_append (parameter : Indexed.Parameter) : parameter.Valid big ↔ parameter.Valid small := by
  cases parameter <;>
    simp only [Parameter.Valid, isDomain_append ext,
      familyRepresentation_eq_append ext _ (representation := .frame) (by decide)]

theorem familyValid_append (contract : Family) : contract.Valid big ↔ contract.Valid small := by
  have affine : affineImplementation big = affineImplementation small := funext (affineImplementation_append ext)
  have presented : presentedImplementation big = presentedImplementation small :=
    funext (presentedImplementation_append ext)
  have smooth : smoothImplementation big = smoothImplementation small := funext (smoothImplementation_append ext)
  unfold Family.Valid
  cases contract.representation <;>
    simp only [parameterValid_append ext, domain_append ext, affine, presented, smooth]

theorem validAffine_append (id implementation : DeclId) (data : AlgebraDeclarations.AffineData) :
    validAffine big id implementation data = validAffine small id implementation data := by
  have affineData : affineData? big = affineData? small := funext (affineData_append ext)
  simp only [validAffine, presentedImplementation_append ext, chainOf_append ext, affineData,
    implementationMarker_append ext]
  cases data.base with
  | none => rfl
  | some base =>
    rcases ext.lookup base with same | ⟨none, declaration, found, kind⟩
    · simp only [same]
    · simp only [none, found]
      cases declaration <;> simp_all [NatureDeclaration]

theorem validMetric_append (family object : DeclId) (gram : SmoothRuntime.Matrix) :
    validMetric big family object gram = validMetric small family object gram := by
  simp only [validMetric, isMetricFamily_append ext, smoothDimension_append ext]
  cases metric : isMetricFamily small family
  · simp
  · simp only [validApplication_mk_of_found ext (found_of_isMetricFamily metric)]

theorem validMetricEvidence_append (metric : DeclId) (evidence : MetricEvidence) :
    validMetricEvidence big metric evidence = validMetricEvidence small metric evidence := by
  simp only [validMetricEvidence, metricData_append ext]

theorem checkFrame_append (family object : DeclId) (matrix inverse : PolyMatrix) :
    FrameDeclarations.checkFrame big family object matrix inverse =
      FrameDeclarations.checkFrame small family object matrix inverse := by
  simp only [FrameDeclarations.checkFrame, isFrameFamily,
    familyRepresentation_append ext family (representation := .frame) (by decide), smoothDimension_append ext]
  cases frame : familyRepresentation small family == some .frame
  · simp
  · simp only [validApplication_mk_of_found ext (found_of_familyRepresentation frame)]

theorem lookup_classification_iff (id : DeclId) (parents implementations : List DeclId) :
    lookup big id = some (.classification parents implementations) ↔
      lookup small id = some (.classification parents implementations) :=
  lookup_eq_some_iff ext (by simp [NatureDeclaration])

/-- **Weakening of declaration validity.** A nature extension does not change
the validity of any entry that `NatureDimension` does not check, for every
class ranking. -/
theorem entryValid_of_extension (ranks : List (DeclId × Nat)) {entry : Entry}
    (other : ¬ NatureCheck entry.declaration) : entry.Valid big ranks ↔ entry.Valid small ranks := by
  obtain ⟨id, declaration⟩ := entry
  cases declaration with
  | marker => exact Iff.rfl
  | implementation marker representation capabilities =>
    simp only [Entry.Valid, isMarker_append ext, representationValid_append ext]
  | classification parents implementations =>
    simp only [Entry.Valid, implementationMarker_append ext, lookup_classification_iff ext]
  | global implementation =>
    simp only [Entry.Valid, implementationMarker_append ext, presentedImplementation_append ext,
      smoothImplementation_append ext]
  | family contract => exact familyValid_append ext contract
  | affine implementation data => simp only [Entry.Valid, validAffine_append ext]
  | smoothAffine implementation coordinates =>
    simp only [Entry.Valid, validSmoothAffine, smoothImplementation_append ext]
  | metric family object gram => simp only [Entry.Valid, validMetric_append ext]
  | metricEvidence metric evidence => simp only [Entry.Valid, validMetricEvidence_append ext]
  | frame family object matrix inverse => simp only [Entry.Valid, checkFrame_append ext]
  | _ => exact absurd trivial other

/-- The executable check is unchanged as well. -/
theorem validEntry_of_extension (ranks : List (DeclId × Nat)) {entry : Entry}
    (other : ¬ NatureCheck entry.declaration) : validEntry big ranks entry = validEntry small ranks entry := by
  rw [Bool.eq_iff_iff, Audit.validEntry_iff, Audit.validEntry_iff]
  exact entryValid_of_extension ext ranks other

end Extension

/-! ### Nature declarations at the end or anywhere -/

theorem coefficientConsistent_append (env extra : Environment) (marker : DeclId) (kind : CoefficientKind) :
    coefficientConsistent (env ++ extra) marker kind =
      (coefficientConsistent env marker kind && coefficientConsistent extra marker kind) := by
  simp only [coefficientConsistent, List.all_append]

theorem coefficientConsistent_nature {extra : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration) (marker : DeclId) (kind : CoefficientKind) :
    coefficientConsistent extra marker kind = true := by
  unfold coefficientConsistent
  rw [List.all_eq_true]
  intro entry member
  have kind' := nature entry member
  cases h : entry.declaration <;> simp_all [NatureDeclaration]

/-- **Appending.** Nature declarations appended to any environment form a
nature extension. An appended entry never shadows an entry of `env`, because
`lookup` returns the first entry with an id. -/
theorem natureExtension_append {env extra : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration) : NatureExtension env (env ++ extra) where
  lookup := by
    intro id
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
          exact nature e (List.mem_of_find?_eq_some entry)
  coefficients := by
    intro marker kind
    rw [coefficientConsistent_append, coefficientConsistent_nature nature, Bool.and_true]

/-- **Inserting.** Nature declarations inserted at any position of an
environment with unique ids form a nature extension of the environment
without them. -/
theorem natureExtension_insert {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) :
    NatureExtension (pre ++ post) (pre ++ extra ++ post) where
  lookup := by
    intro id
    rw [lookup_insert unique id]
    exact (natureExtension_append nature).lookup id
  coefficients := by
    intro marker kind
    rw [coefficientConsistent_append, coefficientConsistent_append, coefficientConsistent_append,
      coefficientConsistent_nature nature, Bool.and_true]

/-! ### Nature declarations anywhere -/

/-- **Weakening of declaration validity, anywhere.** Inserting nature
declarations at any position of an environment with unique ids does not
change the validity of any entry that `NatureDimension` does not check, for
every class ranking. The kernel keeps declarations in source order, so this is
the form that applies to it. -/
theorem entryValid_nature_insertion {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (ranks : List (DeclId × Nat)) {entry : Entry}
    (other : ¬ NatureCheck entry.declaration) :
    entry.Valid (pre ++ extra ++ post) ranks ↔ entry.Valid (pre ++ post) ranks :=
  entryValid_of_extension (natureExtension_insert nature unique) ranks other

theorem validEntry_nature_insertion {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (ranks : List (DeclId × Nat)) {entry : Entry}
    (other : ¬ NatureCheck entry.declaration) :
    validEntry (pre ++ extra ++ post) ranks entry = validEntry (pre ++ post) ranks entry :=
  validEntry_of_extension (natureExtension_insert nature unique) ranks other

/-- **Weakening of binding validity, anywhere.** No binding, `flat` and
`sharp` included, changes its validity. -/
theorem validPrimitiveBinding_nature_insertion {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (binding : PrimitiveBinding) :
    validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding :=
  validPrimitiveBinding_of_extension (natureExtension_insert nature unique) binding

theorem primitiveBindingValid_nature_insertion {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (binding : PrimitiveBinding) :
    binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post) :=
  primitiveBindingValid_of_extension (natureExtension_insert nature unique) binding

/-- **Weakening of evaluation, anywhere.** -/
theorem evalPrimitive_nature_insertion {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (binding : PrimitiveBinding) (values : List Value) :
    evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values :=
  evalPrimitive_of_extension (natureExtension_insert nature unique) binding values

/-- In a valid environment the ids are unique, so the insertion forms need no
further hypothesis. -/
theorem entryValid_nature_insertion_of_valid {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration) (valid : (pre ++ extra ++ post).Valid)
    (ranks : List (DeclId × Nat)) {entry : Entry} (other : ¬ NatureCheck entry.declaration) :
    entry.Valid (pre ++ extra ++ post) ranks ↔ entry.Valid (pre ++ post) ranks :=
  entryValid_nature_insertion nature valid.unique ranks other

theorem validPrimitiveBinding_nature_insertion_of_valid {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration) (valid : (pre ++ extra ++ post).Valid)
    (binding : PrimitiveBinding) :
    validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding :=
  validPrimitiveBinding_nature_insertion nature valid.unique binding

theorem evalPrimitive_nature_insertion_of_valid {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration) (valid : (pre ++ extra ++ post).Valid)
    (binding : PrimitiveBinding) (values : List Value) :
    evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values :=
  evalPrimitive_nature_insertion nature valid.unique binding values

/-! ### Nature declarations at the end -/

/-- **Appending.** Nature declarations appended to any environment change no
entry that `NatureDimension` does not check, with no hypothesis on ids. -/
theorem entryValid_nature_weakening {env extra : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration) (ranks : List (DeclId × Nat))
    {entry : Entry} (other : ¬ NatureCheck entry.declaration) :
    entry.Valid (env ++ extra) ranks ↔ entry.Valid env ranks :=
  entryValid_of_extension (natureExtension_append nature) ranks other

theorem validPrimitiveBinding_nature_weakening {env extra : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration) (binding : PrimitiveBinding) :
    validPrimitiveBinding (env ++ extra) binding = validPrimitiveBinding env binding :=
  validPrimitiveBinding_of_extension (natureExtension_append nature) binding

theorem evalPrimitive_nature_weakening {env extra : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration) (binding : PrimitiveBinding)
    (values : List Value) : evalPrimitive (env ++ extra) binding values = evalPrimitive env binding values :=
  evalPrimitive_of_extension (natureExtension_append nature) binding values

/-! ### A std metric does not depend on nature (C17) -/

/-- **A std metric with its evidence is valid with and without nature.**
Nature declarations at any position of an environment with unique ids, valid
or not, leave a metric declaration and an evidence declaration exactly as
valid as they were. Readings of the metric's object and physical
interpretations of the metric are among them. -/
theorem metric_nature_free {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (ranks : List (DeclId × Nat))
    {metric evidence : Entry} {family object metricId : DeclId} {gram : SmoothRuntime.Matrix}
    {certificate : MetricEvidence}
    (isMetric : metric.declaration = .metric family object gram)
    (isEvidence : evidence.declaration = .metricEvidence metricId certificate) :
    (metric.Valid (pre ++ extra ++ post) ranks ↔ metric.Valid (pre ++ post) ranks) ∧
      (evidence.Valid (pre ++ extra ++ post) ranks ↔ evidence.Valid (pre ++ post) ranks) :=
  ⟨entryValid_nature_insertion nature unique ranks (by simp [isMetric, NatureCheck]),
    entryValid_nature_insertion nature unique ranks (by simp [isEvidence, NatureCheck])⟩

/-- **With and without a reading.** A reading with a fresh id, of any object
and at any position, leaves a std metric and its evidence as valid as they
were. -/
theorem metric_valid_with_reading {pre post : Environment} {reading : Entry} {readingFamily readingObject : DeclId}
    {quantities : List DeclId} (isReading : reading.declaration = .reading readingFamily readingObject quantities)
    (unique : ((pre ++ [reading] ++ post).map Entry.id).Nodup)
    (ranks : List (DeclId × Nat)) {metric evidence : Entry} {family object metricId : DeclId}
    {gram : SmoothRuntime.Matrix} {certificate : MetricEvidence}
    (isMetric : metric.declaration = .metric family object gram)
    (isEvidence : evidence.declaration = .metricEvidence metricId certificate) :
    (metric.Valid (pre ++ [reading] ++ post) ranks ↔ metric.Valid (pre ++ post) ranks) ∧
      (evidence.Valid (pre ++ [reading] ++ post) ranks ↔ evidence.Valid (pre ++ post) ranks) :=
  metric_nature_free (by simp [isReading, NatureDeclaration]) unique ranks isMetric isEvidence

/-- **`flat` and `sharp` do not depend on nature.** Their validity and their
values are unchanged by nature declarations at any position. -/
theorem flat_sharp_nature_free {pre extra post : Environment}
    (nature : ∀ entry ∈ extra, NatureDeclaration entry.declaration)
    (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) (metric evidence object : DeclId)
    (gram inverse : SmoothRuntime.Matrix) (tangent cotangent : DeclId) (values : List Value) :
    validPrimitiveBinding (pre ++ extra ++ post) (.metricFlat metric object gram tangent cotangent) =
        validPrimitiveBinding (pre ++ post) (.metricFlat metric object gram tangent cotangent) ∧
      validPrimitiveBinding (pre ++ extra ++ post) (.metricSharp metric evidence object gram inverse cotangent tangent) =
        validPrimitiveBinding (pre ++ post) (.metricSharp metric evidence object gram inverse cotangent tangent) ∧
      evalPrimitive (pre ++ extra ++ post) (.metricFlat metric object gram tangent cotangent) values =
        evalPrimitive (pre ++ post) (.metricFlat metric object gram tangent cotangent) values ∧
      evalPrimitive (pre ++ extra ++ post) (.metricSharp metric evidence object gram inverse cotangent tangent) values =
        evalPrimitive (pre ++ post) (.metricSharp metric evidence object gram inverse cotangent tangent) values :=
  ⟨validPrimitiveBinding_nature_insertion nature unique _, validPrimitiveBinding_nature_insertion nature unique _,
    evalPrimitive_nature_insertion nature unique _ values, evalPrimitive_nature_insertion nature unique _ values⟩

end VastitasOracle.NatureWeakening
