import VastitasKernel.IndexedSemantics

set_option autoImplicit false

/-! **Declaration extensions.** The common layer of the weakening theorems of
`SmoothMetricWeakening` (C12), `FrameWeakening` (C13) and `NatureWeakening`
(C17).

An `Extension Hidden small big` says that each lookup in `big` is the lookup
in `small`, or a declaration satisfying `Hidden` where `small` has nothing.
`MetricExtension`, `FrameExtension` and `NatureExtension` each contain one,
for the metric, frame and nature declarations. A *profile declaration*
(`ProfileDeclaration`) is a declaration of any of the three kinds. This
module proves once that the lookup-derived views that the binding contracts,
the evaluator and the non-profile declaration checks read, apart from the
views of frame declarations, treat a profile declaration exactly like a
missing one, and so do not change in any of the three extensions.
`SmoothMetricWeakening` adds the views that also see frames, for an extension
by metric or nature declarations (`MetricOrNatureDeclaration`).
`familyRepresentation` can see a profile family, and is only stated here for
the other representations. -/
namespace VastitasOracle.DeclarationExtension

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics

/-- `big` extends `small` by declarations satisfying `Hidden`: each lookup in
`big` is the lookup in `small`, or a `Hidden` declaration where `small` has
nothing. -/
def Extension (Hidden : Declaration → Prop) (small big : Environment) : Prop :=
  ∀ id, lookup big id = lookup small id ∨
    (lookup small id = none ∧ ∃ declaration, lookup big id = some declaration ∧ Hidden declaration)

theorem Extension.mono {Hidden Hidden' : Declaration → Prop}
    (weaker : ∀ declaration, Hidden declaration → Hidden' declaration) {small big : Environment}
    (ext : Extension Hidden small big) : Extension Hidden' small big := by
  intro id
  rcases ext id with same | ⟨none, declaration, found, kind⟩
  · exact .inl same
  · exact .inr ⟨none, declaration, found, weaker declaration kind⟩

/-- A declaration that only a profile contributes, valid or not: of the metric
profile (a metric, metric evidence, or a family with the `metric_form`
representation), of `nature::dimension` (a base dimension, a quantity, a
reading, a scale, a physical metric, or a family with the `reading` or
`physical_metric` representation), or a frame. -/
def ProfileDeclaration : Declaration → Prop
  | .metric .. | .metricEvidence .. | .frame .. | .baseDimension | .quantity .. | .reading .. | .scale ..
  | .physicalMetric .. => True
  | .family contract => contract.representation = .metricForm ∨ contract.representation = .reading ∨
      contract.representation = .physicalMetric
  | _ => False

/-- A profile declaration that is not a frame. -/
def MetricOrNatureDeclaration : Declaration → Prop
  | .metric .. | .metricEvidence .. | .baseDimension | .quantity .. | .reading .. | .scale ..
  | .physicalMetric .. => True
  | .family contract => contract.representation = .metricForm ∨ contract.representation = .reading ∨
      contract.representation = .physicalMetric
  | _ => False

theorem Extension.profile {small big : Environment} (ext : Extension MetricOrNatureDeclaration small big) :
    Extension ProfileDeclaration small big :=
  ext.mono fun declaration kind => by
    cases declaration <;> simp_all [MetricOrNatureDeclaration, ProfileDeclaration]

section Any

variable {Hidden : Declaration → Prop} {small big : Environment} (ext : Extension Hidden small big)
include ext

theorem lookup_of_isSome {id : DeclId} (found : (lookup small id).isSome = true) :
    lookup big id = lookup small id := by
  rcases ext id with same | ⟨none, _⟩
  · exact same
  · rw [none] at found
    cases found

end Any

section Profile

variable {small big : Environment} (ext : Extension ProfileDeclaration small big)
include ext

/-! ### Views that treat a profile declaration as a missing one -/

-- The proof pattern of every view below: on an inherited entry the view is
-- unchanged, and on an added profile declaration it agrees with `none`.
local macro "profile_view" ext:term:max view:ident id:term:max : tactic => `(tactic| (
  rcases $ext:term $id with same | ⟨none, declaration, found, kind⟩
  · simp only [$view:ident, same]
  · simp only [$view:ident, none, found]
    cases declaration <;> simp only [ProfileDeclaration] at kind <;> (try rcases kind with kind | kind | kind) <;>
      simp_all))

theorem isMarker_append (id : DeclId) : isMarker big id = isMarker small id := by
  profile_view ext isMarker id

theorem implementationMarker_append (id : DeclId) :
    implementationMarker big id = implementationMarker small id := by
  profile_view ext implementationMarker id

theorem affineImplementation_append (id : DeclId) :
    affineImplementation big id = affineImplementation small id := by
  profile_view ext affineImplementation id

theorem presentedImplementation_append (id : DeclId) :
    presentedImplementation big id = presentedImplementation small id := by
  profile_view ext presentedImplementation id

theorem smoothImplementation_append (id : DeclId) :
    smoothImplementation big id = smoothImplementation small id := by
  profile_view ext smoothImplementation id

theorem affineData_append (id : DeclId) : affineData? big id = affineData? small id := by
  profile_view ext affineData? id

theorem smoothCoordinates_append (id : DeclId) :
    smoothCoordinates? big id = smoothCoordinates? small id := by
  profile_view ext smoothCoordinates? id

theorem smoothDimension_append (id : DeclId) :
    smoothDimension? big id = smoothDimension? small id := by
  simp only [smoothDimension?, smoothCoordinates_append ext]

theorem domain_append (id : DeclId) : Indexed.domain big id = Indexed.domain small id := by
  profile_view ext Indexed.domain id

theorem isDomain_append (id : DeclId) : isDomain big id = isDomain small id := by
  profile_view ext isDomain id

theorem objectImplementation_append (id : DeclId) :
    (lookup big id).bind Declaration.objectImplementation? =
      (lookup small id).bind Declaration.objectImplementation? := by
  rcases ext id with same | ⟨none, declaration, found, kind⟩
  · rw [same]
  · rw [none, found]
    cases declaration <;> simp only [ProfileDeclaration] at kind <;> (try rcases kind with kind | kind | kind) <;>
      simp_all [Declaration.objectImplementation?]

theorem fiberVariance_append (id : DeclId) : fiberVariance? big id = fiberVariance? small id := by
  profile_view ext fiberVariance? id

theorem isTapeFamily_append (id : DeclId) : isTapeFamily big id = isTapeFamily small id := by
  profile_view ext isTapeFamily id

theorem isSmoothFamily_append (id : DeclId) : isSmoothFamily big id = isSmoothFamily small id := by
  profile_view ext isSmoothFamily id

theorem frameFiberVariance_append (id : DeclId) : frameFiberVariance? big id = frameFiberVariance? small id := by
  profile_view ext frameFiberVariance? id

theorem isFrameMapFamily_append (id : DeclId) : isFrameMapFamily big id = isFrameMapFamily small id := by
  profile_view ext isFrameMapFamily id

theorem affineGlobal_append (id : DeclId) : affineGlobal big id = affineGlobal small id := by
  rcases ext id with same | ⟨none, declaration, found, kind⟩
  · simp only [affineGlobal, same, affineImplementation_append ext]
  · simp only [affineGlobal, none, found]
    cases declaration <;> simp only [ProfileDeclaration] at kind <;> (try rcases kind with kind | kind | kind) <;>
      simp_all

theorem implementationSupports_append (id : DeclId) (capability : Capability) :
    implementationSupports big id capability = implementationSupports small id capability := by
  profile_view ext implementationSupports id

/-- A profile family is the only way a profile family representation can
appear; every other view compares with another representation. -/
theorem familyRepresentation_eq_append (id : DeclId) {representation : FamilyRepresentation}
    (other : representation ≠ .metricForm ∧ representation ≠ .reading ∧ representation ≠ .physicalMetric) :
    familyRepresentation big id = some representation ↔ familyRepresentation small id = some representation := by
  rcases ext id with same | ⟨none, declaration, found, kind⟩
  · simp only [familyRepresentation, same]
  · simp only [familyRepresentation, none, found]
    cases declaration <;> simp only [ProfileDeclaration] at kind <;> (try rcases kind with kind | kind | kind) <;>
      simp_all [eq_comm]

theorem familyRepresentation_append (id : DeclId) {representation : FamilyRepresentation}
    (other : representation ≠ .metricForm ∧ representation ≠ .reading ∧ representation ≠ .physicalMetric) :
    (familyRepresentation big id == some representation) =
      (familyRepresentation small id == some representation) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact familyRepresentation_eq_append ext id other

theorem isRelativeFamily_append (id : DeclId) : isRelativeFamily big id = isRelativeFamily small id := by
  simp only [isRelativeFamily, familyRepresentation_append ext id (representation := .relative) (by decide)]

theorem globalObject_append (id : DeclId) : globalObject big id = globalObject small id := by
  simp only [globalObject, objectImplementation_append ext]

theorem scalarBaseProfile_append (id : DeclId) : scalarBaseProfile big id = scalarBaseProfile small id := by
  unfold scalarBaseProfile
  rcases ext id with same | ⟨none, declaration, found, kind⟩
  · rw [same]
    cases lookup small id with
    | none => rfl
    | some declaration =>
      cases declaration with
      | global implementation =>
        simp only [Option.bind_eq_bind, Option.bind_some]
        rcases ext implementation with same' | ⟨none', declaration', found', kind'⟩
        · rw [same']
        · rw [none', found']
          cases declaration' <;> simp_all [ProfileDeclaration]
      | _ => rfl
  · rw [none, found]
    cases declaration <;> simp_all [ProfileDeclaration]

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

theorem constraintHolds_append (indices : List Index) (constraint : Constraint) :
    constraintHolds big indices constraint = constraintHolds small indices constraint := by
  cases constraint <;>
    simp only [constraintHolds, type_append ext, onChain_append ext, smoothDimension_append ext]

theorem constraintHolds_append' (indices : List Index) :
    constraintHolds big indices = constraintHolds small indices :=
  funext (constraintHolds_append ext indices)

theorem fiberVectorValue_append (family : DeclId) (point : SmoothRuntime.Program) (values : List Value) :
    fiberVectorValue big family point values = fiberVectorValue small family point values := by
  simp only [fiberVectorValue, fiberVariance_append ext]

theorem frameVectorValue_append (coords : DeclId) (point : SmoothRuntime.Program) (values : List Value) :
    frameVectorValue big coords point values = frameVectorValue small coords point values := by
  simp only [frameVectorValue, frameFiberVariance_append ext]

/-! ### Evaluation and declaration views -/

/-- **Evaluation.** A profile extension does not change the value of any
primitive. Only `global`, `origin`, `fiber_vector` and `frame_vector` consult
the environment, and none of them reads a profile declaration. -/
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
    rcases ext base with same | ⟨none, declaration, found, kind⟩
    · simp only [same]
    · simp only [none, found]
      cases declaration <;> simp only [ProfileDeclaration] at kind <;> (try rcases kind with kind | kind | kind) <;>
        simp_all

end Profile

end VastitasOracle.DeclarationExtension
