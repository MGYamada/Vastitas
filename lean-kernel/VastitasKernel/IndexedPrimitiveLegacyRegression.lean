import VastitasKernel.IndexedPrimitives

/-! Frozen copies of the primitive tables as they were before the registry
(#622), with the proof that the derived tables agree with them on every
binding. Each table that moves into `PrimitiveBinding.contract` keeps its
pre-registry definition here until the migration is complete; the proofs are
by definitional unfolding, so a registry entry that changed a contract would
fail here. The module is deleted at the end of the migration; the emit goldens
(`tests/fixtures/emit`) stay. -/
namespace VastitasKernel.Indexed.PrimitiveLegacyRegression

def legacyValid (env : Environment) : PrimitiveBinding → Prop
  | .descriptor implementation => affineImplementation env implementation = true ∧
      ∃ ty ∈ implementationType env implementation, ty.Valid env
  | .global id => affineGlobal env id = true ∧ ObjectRef.Valid env (.global id)
  | .origin domain family base => domain.Supports env .origin ∧
      familyRepresentation env family = some .point ∧
      Application.Valid env ⟨family, [.object (.local domain 0), .object (.global base)]⟩
  | .identity domain family => domain.Valid env ∧
      familyRepresentation env family = some .morphism ∧
      Application.Valid env ⟨family, [.object (.local domain 0), .object (.local domain 0)]⟩
  | .dimension domain => domain.Supports env .dimension
  | .compose family => familyRepresentation env family = some .morphism
  | .apply maps points => familyRepresentation env maps = some .morphism ∧
      familyRepresentation env points = some .point
  | .relativeConstant application map => relativeConstantValid env application map = true
  | .relativeCompose family | .relativeEqual family => isRelativeFamily env family = true
  | .relativeView family source target =>
      isRelativeFamily env family = true ∧ onChain env source target = true
  | .relativeCoefficient family source target coordinate monomial =>
      isRelativeFamily env family = true ∧ (affineData? env source).isSome = true ∧
      coordinate < affineArity env target ∧ (affineData? env target).isSome = true ∧
      monomial.length = affineArity env source
  | .relativeIntPoint family object base =>
      isRelativeFamily env family = true ∧ freeAffine env object = true ∧ pointBase env base = true
  | .relativePair family fiber => isRelativeFamily env family = true ∧ (plainFiber? env fiber).isSome = true
  | .relativeIso forward backward => relativeIsoValid env forward backward = true
  | .relativeCartesian first second inverse fiber => relativeCartesianValid env first second inverse fiber = true
  | .smoothConstant application map => smoothConstantValid env application map = true
  | .smoothCompose family | .smoothEqual family | .smoothComposite family => isSmoothFamily env family = true
  | .smoothIntPoint family object point => smoothIntPointValid env family object point = true
  | .fiberVector family smooth object => fiberVectorValid env family smooth object = true
  | .fiberAt family smooth => fiberAtValid env family smooth = true
  | .fiberEqual family => fiberEqualValid env family = true
  | .fiberComponent family object coordinate => fiberComponentValid env family object coordinate = true
  | .fiberPairing cotangent tangent => fiberPairingValid env cotangent tangent = true
  | .cotangentPullback smooth cotangent _ => cotangentPullbackValid env smooth cotangent = true
  | .differential smooth cotangent line => differentialValid env smooth cotangent line = true
  | .linearize smooth tape => linearizeValid env smooth tape = true
  | .cotangentBackward tape cotangent => cotangentBackwardValid env tape cotangent = true
  | .metricFlat metric object gram tangent cotangent =>
      metricFlatValid env metric object gram tangent cotangent = true
  | .metricSharp metric evidence object gram inverse cotangent tangent =>
      metricSharpValid env metric evidence object gram inverse cotangent tangent = true

def legacyValidPrimitiveBinding (env : Environment) : PrimitiveBinding → Bool
  | .descriptor implementation => match implementationType env implementation with
    | some ty => affineImplementation env implementation && decide (ty.Valid env)
    | none => false
  | .global id => affineGlobal env id && decide (ObjectRef.Valid env (.global id))
  | .origin domain family base => originContract env domain family base
  | .identity domain family => identityContract env domain family
  | .dimension domain => decide (domain.Supports env .dimension)
  | .compose family => familyRepresentation env family == some .morphism
  | .apply maps points => familyRepresentation env maps == some .morphism &&
      familyRepresentation env points == some .point
  | .relativeConstant application map => relativeConstantValid env application map
  | .relativeCompose family | .relativeEqual family => isRelativeFamily env family
  | .relativeView family source target => isRelativeFamily env family && onChain env source target
  | .relativeCoefficient family source target coordinate monomial =>
      isRelativeFamily env family && (affineData? env source).isSome &&
      decide (coordinate < affineArity env target) && (affineData? env target).isSome &&
      monomial.length == affineArity env source
  | .relativeIntPoint family object base =>
      isRelativeFamily env family && freeAffine env object && pointBase env base
  | .relativePair family fiber => isRelativeFamily env family && (plainFiber? env fiber).isSome
  | .relativeIso forward backward => relativeIsoValid env forward backward
  | .relativeCartesian first second inverse fiber => relativeCartesianValid env first second inverse fiber
  | .smoothConstant application map => smoothConstantValid env application map
  | .smoothCompose family | .smoothEqual family | .smoothComposite family => isSmoothFamily env family
  | .smoothIntPoint family object point => smoothIntPointValid env family object point
  | .fiberVector family smooth object => fiberVectorValid env family smooth object
  | .fiberAt family smooth => fiberAtValid env family smooth
  | .fiberEqual family => fiberEqualValid env family
  | .fiberComponent family object coordinate => fiberComponentValid env family object coordinate
  | .fiberPairing cotangent tangent => fiberPairingValid env cotangent tangent
  | .cotangentPullback smooth cotangent _ => cotangentPullbackValid env smooth cotangent
  | .differential smooth cotangent line => differentialValid env smooth cotangent line
  | .linearize smooth tape => linearizeValid env smooth tape
  | .cotangentBackward tape cotangent => cotangentBackwardValid env tape cotangent
  | .metricFlat metric object gram tangent cotangent => metricFlatValid env metric object gram tangent cotangent
  | .metricSharp metric evidence object gram inverse cotangent tangent =>
      metricSharpValid env metric evidence object gram inverse cotangent tangent

/-- The propositional contract of every binding is the pre-registry one. -/
theorem valid_agrees (env : Environment) (binding : PrimitiveBinding) :
    binding.Valid env ↔ legacyValid env binding := by
  cases binding <;> exact Iff.rfl

/-- The executable contract of every binding is the pre-registry one. -/
theorem validPrimitiveBinding_agrees (env : Environment) (binding : PrimitiveBinding) :
    validPrimitiveBinding env binding = legacyValidPrimitiveBinding env binding := by
  cases binding <;> rfl

end VastitasKernel.Indexed.PrimitiveLegacyRegression
