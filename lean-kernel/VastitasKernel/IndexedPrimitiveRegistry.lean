import VastitasKernel.IndexedAudit
import VastitasKernel.IndexedPrimitiveBinding
import VastitasKernel.IndexedPrimitiveDescriptors

/-! The primitive registry (#622): one descriptor per `PrimitiveBinding`
constructor, built from the binding's own data, in the single dispatch
`PrimitiveBinding.contract` through which the derived tables read it.

The validity contract (`PrimitiveBinding.Valid`, `validPrimitiveBinding` and
`validPrimitiveBinding_iff`) is derived from the arm below and needs no case
elsewhere; the remaining tables (`arity`, `PrimitiveAssociation`,
`inferPrimitiveResult`, `evalPrimitive`, `renderPrimitive`, the decoder and
the role table) are migrated by the later steps of #622 and still take a case
per constructor. A proof that unfolds a derived table at one constructor needs
only `PrimitiveBinding.contract` (and `PrimitiveDescriptor.ofBool`) in its
`simp` set. Each arm names the exact checks of `Indexed`,
`IndexedPrimitiveBinding` and `IndexedSmoothContracts`; family, base and object
IDs are part of the contract, displayed names and arbitrary certificates are
not. -/
namespace VastitasKernel.Indexed
open VastitasKernel.Indexed.Audit (validApplication_iff)

/-- The registry: the descriptor of a binding, from the binding's own data.
This is the one dispatch on binding constructors. -/
def PrimitiveBinding.contract : PrimitiveBinding → PrimitiveDescriptor
  /- Objects, points and morphisms. -/
  | .descriptor implementation =>
    { validProp env := affineImplementation env implementation = true ∧
        ∃ ty ∈ implementationType env implementation, ty.Valid env
      validBool env := match implementationType env implementation with
        | some ty => affineImplementation env implementation && decide (ty.Valid env)
        | none => false
      valid_iff env := by cases implementationType env implementation <;> simp [Bool.and_eq_true] }
  | .global id =>
    { validProp env := affineGlobal env id = true ∧ ObjectRef.Valid env (.global id)
      validBool env := affineGlobal env id && decide (ObjectRef.Valid env (.global id))
      valid_iff env := by simp [Bool.and_eq_true] }
  | .origin domain family base =>
    { validProp env := domain.Supports env .origin ∧ familyRepresentation env family = some .point ∧
        Application.Valid env ⟨family, [.object (.local domain 0), .object (.global base)]⟩
      validBool env := originContract env domain family base
      valid_iff env := by simp [originContract, Bool.and_eq_true, validApplication_iff, and_assoc] }
  | .identity domain family =>
    { validProp env := domain.Valid env ∧ familyRepresentation env family = some .morphism ∧
        Application.Valid env ⟨family, [.object (.local domain 0), .object (.local domain 0)]⟩
      validBool env := identityContract env domain family
      valid_iff env := by simp [identityContract, Bool.and_eq_true, validApplication_iff, and_assoc] }
  | .dimension domain =>
    { validProp env := domain.Supports env .dimension
      validBool env := decide (domain.Supports env .dimension)
      valid_iff env := by simp }
  | .compose family =>
    { validProp env := familyRepresentation env family = some .morphism
      validBool env := familyRepresentation env family == some .morphism
      valid_iff env := by simp }
  | .apply maps points =>
    { validProp env := familyRepresentation env maps = some .morphism ∧
        familyRepresentation env points = some .point
      validBool env := familyRepresentation env maps == some .morphism &&
        familyRepresentation env points == some .point
      valid_iff env := by simp [Bool.and_eq_true] }
  /- Relative morphisms over a base (Stage 2). -/
  | .relativeConstant application map => .ofBool fun env => relativeConstantValid env application map
  | .relativeCompose family => .ofBool fun env => isRelativeFamily env family
  | .relativeView family source target =>
    { validProp env := isRelativeFamily env family = true ∧ onChain env source target = true
      validBool env := isRelativeFamily env family && onChain env source target
      valid_iff env := by simp [Bool.and_eq_true] }
  | .relativeEqual family => .ofBool fun env => isRelativeFamily env family
  | .relativeCoefficient family source target coordinate monomial =>
    { validProp env := isRelativeFamily env family = true ∧ (affineData? env source).isSome = true ∧
        coordinate < affineArity env target ∧ (affineData? env target).isSome = true ∧
        monomial.length = affineArity env source
      validBool env := isRelativeFamily env family && (affineData? env source).isSome &&
        decide (coordinate < affineArity env target) && (affineData? env target).isSome &&
        monomial.length == affineArity env source
      valid_iff env := by simp [Bool.and_eq_true, and_assoc] }
  | .relativeIntPoint family object base =>
    { validProp env := isRelativeFamily env family = true ∧ freeAffine env object = true ∧
        pointBase env base = true
      validBool env := isRelativeFamily env family && freeAffine env object && pointBase env base
      valid_iff env := by simp [Bool.and_eq_true, and_assoc] }
  | .relativePair family fiber =>
    { validProp env := isRelativeFamily env family = true ∧ (plainFiber? env fiber).isSome = true
      validBool env := isRelativeFamily env family && (plainFiber? env fiber).isSome
      valid_iff env := by simp [Bool.and_eq_true] }
  | .relativeIso forward backward => .ofBool fun env => relativeIsoValid env forward backward
  | .relativeCartesian first second inverse fiber =>
    .ofBool fun env => relativeCartesianValid env first second inverse fiber
  /- Smooth maps, fibers, tapes and metrics (Stage 3). The pullback mode chooses
  how forward values are obtained and is not part of the contract. -/
  | .smoothConstant application map => .ofBool fun env => smoothConstantValid env application map
  | .smoothCompose family => .ofBool fun env => isSmoothFamily env family
  | .smoothEqual family => .ofBool fun env => isSmoothFamily env family
  | .smoothIntPoint family object point => .ofBool fun env => smoothIntPointValid env family object point
  | .smoothComposite family => .ofBool fun env => isSmoothFamily env family
  | .fiberVector family smooth object => .ofBool fun env => fiberVectorValid env family smooth object
  | .fiberAt family smooth => .ofBool fun env => fiberAtValid env family smooth
  | .fiberEqual family => .ofBool fun env => fiberEqualValid env family
  | .fiberComponent family object coordinate =>
    .ofBool fun env => fiberComponentValid env family object coordinate
  | .fiberPairing cotangent tangent => .ofBool fun env => fiberPairingValid env cotangent tangent
  | .cotangentPullback smooth cotangent _ => .ofBool fun env => cotangentPullbackValid env smooth cotangent
  | .differential smooth cotangent line => .ofBool fun env => differentialValid env smooth cotangent line
  | .linearize smooth tape => .ofBool fun env => linearizeValid env smooth tape
  | .cotangentBackward tape cotangent => .ofBool fun env => cotangentBackwardValid env tape cotangent
  | .metricFlat metric object gram tangent cotangent =>
    .ofBool fun env => metricFlatValid env metric object gram tangent cotangent
  | .metricSharp metric evidence object gram inverse cotangent tangent =>
    .ofBool fun env => metricSharpValid env metric evidence object gram inverse cotangent tangent

end VastitasKernel.Indexed
