import VastitasKernel.IndexedAudit
import VastitasKernel.IndexedPrimitiveBinding
import VastitasKernel.IndexedPrimitiveDescriptors

set_option autoImplicit false

/-! The primitive registry (#622): one descriptor per `PrimitiveBinding`
constructor, built from the binding's own data, in the single dispatch
`PrimitiveBinding.contract` through which the derived tables read it.

Derived from the arm below, with no case elsewhere: the validity contract
(`PrimitiveBinding.Valid`, `validPrimitiveBinding`, `validPrimitiveBinding_iff`),
the operand association, result inference, the operand count, the argument
hints and the role table. The evaluators, the lowering and the decoder are
migrated by the later steps of #622 and still take a case per constructor. A
proof that unfolds a derived table at one constructor needs only
`PrimitiveBinding.contract` (and `PrimitiveDescriptor.ofBool`) in its `simp`
set. Each arm names the exact checks of `Indexed`, `IndexedPrimitiveBinding`
and `IndexedSmoothContracts`; family, base and object IDs are part of the
contract, displayed names and arbitrary certificates are not.

Index fields are named as their families declare them: a point is
`[target, source]`, a morphism, smooth map or tape `[source, target]`, a
relative morphism `[source, target, base]`, a fiber `[object]`. The role table
reports a shape's families once the operands have its index pattern;
`families := .early` keeps the precedence of the two primitives that report
them as soon as the operands are applications. -/
namespace VastitasKernel.Indexed
open VastitasKernel.Indexed.Audit (validApplication_iff)

/-- A morphism, smooth map or tape operand. -/
private abbrev map (role : String) (family : DeclId) : Operand :=
  .indexed role family [.var "source", .var "target"]
/-- A point operand: its first index is the target. -/
private abbrev point (role : String) (family : DeclId) : Operand :=
  .indexed role family [.var "target", .var "source"]
/-- A morphism over a base. -/
private abbrev relativeMap (role : String) (family : DeclId) : Operand :=
  .indexed role family [.var "source", .var "target", .var "base"]
/-- A vector or covector. -/
private abbrev fiber (role : String) (family : DeclId) : Operand := .indexed role family [.var "object"]
/-- A point of a smooth object: a smooth map from a 0-dimensional object. -/
private abbrev smoothPoint (family : DeclId) : Operand := map "point" family
/-- The point operand, at position 1, is over a 0-dimensional object. -/
private abbrev pointAtOrigin : Relation := .pointDimension ⟨1, 0⟩ 0

/-- The registry: the descriptor of a binding, from the binding's own data.
This is the one dispatch on binding constructors. -/
def PrimitiveBinding.contract : PrimitiveBinding → PrimitiveDescriptor
  /- Objects, points and morphisms. -/
  | .descriptor implementation =>
    { shape := { operands := [.natural], relations := [.freshBrand], result := .freshObject implementation }
      validProp env := affineImplementation env implementation = true ∧
        ∃ ty ∈ implementationType env implementation, ty.Valid env
      validBool env := match implementationType env implementation with
        | some ty => affineImplementation env implementation && decide (ty.Valid env)
        | none => false
      valid_iff env := by cases implementationType env implementation <;> simp [Bool.and_eq_true] }
  | .global id =>
    { shape := { operands := [], result := .globalObject id }
      validProp env := affineGlobal env id = true ∧ ObjectRef.Valid env (.global id)
      validBool env := affineGlobal env id && decide (ObjectRef.Valid env (.global id))
      valid_iff env := by simp [Bool.and_eq_true] }
  | .origin domain family base =>
    { shape :=
        { operands := [.object "object" domain], relations := [.refines 0],
          result := .indexed family [.objectRef 0, .fixed (.global base)] }
      validProp env := domain.Supports env .origin ∧ familyRepresentation env family = some .point ∧
        Application.Valid env ⟨family, [.object (.local domain 0), .object (.global base)]⟩
      validBool env := originContract env domain family base
      valid_iff env := by simp [originContract, Bool.and_eq_true, validApplication_iff, and_assoc] }
  | .identity domain family =>
    { shape :=
        { operands := [.object "object" domain], relations := [.refines 0],
          result := .indexed family [.objectRef 0, .objectRef 0] }
      validProp env := domain.Valid env ∧ familyRepresentation env family = some .morphism ∧
        Application.Valid env ⟨family, [.object (.local domain 0), .object (.local domain 0)]⟩
      validBool env := identityContract env domain family
      valid_iff env := by simp [identityContract, Bool.and_eq_true, validApplication_iff, and_assoc] }
  | .dimension domain =>
    { shape := { operands := [.object "object" domain], relations := [.refines 0], result := .natural }
      validProp env := domain.Supports env .dimension
      validBool env := decide (domain.Supports env .dimension)
      valid_iff env := by simp }
  | .compose family =>
    { shape :=
        { operands := [map "first map" family, map "second map" family],
          relations := [.sameRef ⟨0, 0⟩ ⟨1, 1⟩],
          result := .indexed family [.index ⟨1, 0⟩, .index ⟨0, 1⟩] }
      validProp env := familyRepresentation env family = some .morphism
      validBool env := familyRepresentation env family == some .morphism
      valid_iff env := by simp }
  | .apply maps points =>
    { shape :=
        { operands := [map "map" maps, point "point" points],
          relations := [.sameRef ⟨0, 0⟩ ⟨1, 0⟩],
          result := .indexed points [.index ⟨0, 1⟩, .index ⟨1, 1⟩] }
      validProp env := familyRepresentation env maps = some .morphism ∧
        familyRepresentation env points = some .point
      validBool env := familyRepresentation env maps == some .morphism &&
        familyRepresentation env points == some .point
      valid_iff env := by simp [Bool.and_eq_true] }
  /- Relative morphisms over a base (Stage 2). -/
  | .relativeConstant application affineMap =>
    .ofBool { operands := [], result := .constant application } fun env =>
      relativeConstantValid env application affineMap
  | .relativeCompose family =>
    .ofBool
      { operands := [relativeMap "first map" family, relativeMap "second map" family],
        relations := [.sameRef ⟨0, 0⟩ ⟨1, 1⟩, .sameRef ⟨0, 2⟩ ⟨1, 2⟩],
        result := .indexed family [.index ⟨1, 0⟩, .index ⟨0, 1⟩, .index ⟨0, 2⟩] }
      fun env => isRelativeFamily env family
  | .relativeView family source target =>
    { shape :=
        { operands := [.indexed "map" family
            [.var "source", .var "target", .fixed (.global source) "base" "the view's source base"]],
          result := .indexed family [.index ⟨0, 0⟩, .index ⟨0, 1⟩, .fixed (.global target)] }
      validProp env := isRelativeFamily env family = true ∧ onChain env source target = true
      validBool env := isRelativeFamily env family && onChain env source target
      valid_iff env := by simp [Bool.and_eq_true] }
  | .relativeEqual family =>
    .ofBool
      { operands := [.application "first map" family, .application "second map" family],
        relations := [.sameApplication 0 1 ["source", "target", "base"]], result := .boolean }
      fun env => isRelativeFamily env family
  | .relativeCoefficient family source target coordinate monomial =>
    { shape :=
        { operands := [.indexed "map" family
            [.fixed (.global source) "source" "the primitive's declared source",
             .fixed (.global target) "target" "the primitive's declared target", .any]],
          result := .integerPair, families := .early }
      validProp env := isRelativeFamily env family = true ∧ (affineData? env source).isSome = true ∧
        coordinate < affineArity env target ∧ (affineData? env target).isSome = true ∧
        monomial.length = affineArity env source
      validBool env := isRelativeFamily env family && (affineData? env source).isSome &&
        decide (coordinate < affineArity env target) && (affineData? env target).isSome &&
        monomial.length == affineArity env source
      valid_iff env := by simp [Bool.and_eq_true, and_assoc] }
  | .relativeIntPoint family object base =>
    { shape :=
        { operands := [], tail := some fun env => affineArity env object,
          result := .constant ⟨family, [.object (.global base), .object (.global object), .object (.global base)]⟩ }
      validProp env := isRelativeFamily env family = true ∧ freeAffine env object = true ∧
        pointBase env base = true
      validBool env := isRelativeFamily env family && freeAffine env object && pointBase env base
      valid_iff env := by simp [Bool.and_eq_true, and_assoc] }
  | .relativePair family fiber =>
    { shape :=
        { operands := [relativeMap "first map" family, relativeMap "second map" family],
          -- The factors and base of the fiber product declared without `via`.
          relations := [.sameRef ⟨0, 0⟩ ⟨1, 0⟩,
            .fixedFrom ⟨0, 2⟩ (fun env => (plainFiber? env fiber).map fun (_, _, base) => .global base) "the fiber's base",
            .fixedFrom ⟨1, 2⟩ (fun env => (plainFiber? env fiber).map fun (_, _, base) => .global base) "the fiber's base",
            .fixedFrom ⟨0, 1⟩ (fun env => (plainFiber? env fiber).map fun (left, _, _) => .global left)
              "the fiber's first factor",
            .fixedFrom ⟨1, 1⟩ (fun env => (plainFiber? env fiber).map fun (_, right, _) => .global right)
              "the fiber's second factor"],
          result := .indexed family [.index ⟨0, 0⟩, .fixed (.global fiber), .index ⟨0, 2⟩],
          families := .early }
      validProp env := isRelativeFamily env family = true ∧ (plainFiber? env fiber).isSome = true
      validBool env := isRelativeFamily env family && (plainFiber? env fiber).isSome
      valid_iff env := by simp [Bool.and_eq_true] }
  | .relativeIso forward backward => .ofBool .uncallable fun env => relativeIsoValid env forward backward
  | .relativeCartesian first second inverse fiber =>
    .ofBool .uncallable fun env => relativeCartesianValid env first second inverse fiber
  /- Smooth maps, fibers, tapes and metrics (Stage 3). The pullback mode chooses
  how forward values are obtained and is not part of the contract. -/
  | .smoothConstant application affineMap =>
    .ofBool { operands := [], result := .constant application } fun env =>
      smoothConstantValid env application affineMap
  | .smoothCompose family =>
    .ofBool
      { operands := [map "first map" family, map "second map" family],
        relations := [.sameRef ⟨0, 0⟩ ⟨1, 1⟩],
        result := .indexed family [.index ⟨1, 0⟩, .index ⟨0, 1⟩] }
      fun env => isSmoothFamily env family
  | .smoothEqual family =>
    .ofBool
      { operands := [.application "first map" family, .application "second map" family],
        relations := [.sameApplication 0 1 ["source", "target"]], result := .boolean }
      fun env => isSmoothFamily env family
  | .smoothIntPoint family object point =>
    .ofBool
      { operands := [], tail := some fun env => smoothArity env object,
        result := .constant ⟨family, [.object (.global point), .object (.global object)]⟩ }
      fun env => smoothIntPointValid env family object point
  | .smoothComposite family =>
    .ofBool { operands := [.application "map" family], result := .application 0 }
      fun env => isSmoothFamily env family
  | .fiberVector family smooth object =>
    .ofBool
      { operands := [.indexed "point" smooth
          [.var "source", .fixed (.global object) "target" "the primitive's declared object"]],
        tail := some fun env => smoothArity env object, relations := [.pointDimension ⟨0, 0⟩ 0],
        result := .constant ⟨family, [.object (.global object)]⟩ }
      fun env => fiberVectorValid env family smooth object
  | .fiberAt family smooth =>
    .ofBool
      { operands := [fiber "element" family, smoothPoint smooth],
        relations := [.sameRef ⟨0, 0⟩ ⟨1, 1⟩, pointAtOrigin], result := .boolean }
      fun env => fiberAtValid env family smooth
  | .fiberEqual family =>
    .ofBool
      { operands := [.application "first element" family, .application "second element" family],
        relations := [.sameApplication 0 1 ["object"]], result := .boolean }
      fun env => fiberEqualValid env family
  | .fiberComponent family object coordinate =>
    .ofBool
      { operands := [.indexed "element" family [.fixed (.global object) "object" "the primitive's declared object"]],
        result := .integerPair }
      fun env => fiberComponentValid env family object coordinate
  | .fiberPairing cotangent tangent =>
    .ofBool
      { operands := [fiber "covector" cotangent, fiber "vector" tangent],
        relations := [.sameRef ⟨0, 0⟩ ⟨1, 0⟩], result := .integerPair }
      fun env => fiberPairingValid env cotangent tangent
  | .cotangentPullback smooth cotangent _ =>
    .ofBool
      { operands := [map "map" smooth, smoothPoint smooth, fiber "seed" cotangent],
        relations := [.sameRef ⟨0, 0⟩ ⟨1, 1⟩, .sameRef ⟨0, 1⟩ ⟨2, 0⟩, pointAtOrigin],
        result := .indexed cotangent [.index ⟨0, 0⟩] }
      fun env => cotangentPullbackValid env smooth cotangent
  | .differential smooth cotangent line =>
    .ofBool
      { operands := [.indexed "function" smooth
          [.var "source", .fixed (.global line) "target" "the primitive's declared line"], smoothPoint smooth],
        relations := [.sameRef ⟨0, 0⟩ ⟨1, 1⟩, pointAtOrigin], result := .indexed cotangent [.index ⟨0, 0⟩] }
      fun env => differentialValid env smooth cotangent line
  | .linearize smooth tape =>
    .ofBool
      { operands := [map "map" smooth, smoothPoint smooth],
        relations := [.sameRef ⟨0, 0⟩ ⟨1, 1⟩, pointAtOrigin],
        result := .indexed tape [.index ⟨0, 0⟩, .index ⟨0, 1⟩] }
      fun env => linearizeValid env smooth tape
  | .cotangentBackward tape cotangent =>
    .ofBool
      { operands := [map "tape" tape, fiber "seed" cotangent],
        relations := [.sameRef ⟨0, 1⟩ ⟨1, 0⟩], result := .indexed cotangent [.index ⟨0, 0⟩] }
      fun env => cotangentBackwardValid env tape cotangent
  | .metricFlat metric object gram tangent cotangent =>
    .ofBool
      { operands := [.indexed "vector" tangent [.fixed (.global object) "object" "the metric's object"]],
        result := .indexed cotangent [.fixed (.global object)] }
      fun env => metricFlatValid env metric object gram tangent cotangent
  | .metricSharp metric evidence object gram inverse cotangent tangent =>
    .ofBool
      { operands := [.indexed "covector" cotangent [.fixed (.global object) "object" "the metric's object"]],
        result := .indexed tangent [.fixed (.global object)] }
      fun env => metricSharpValid env metric evidence object gram inverse cotangent tangent

end VastitasKernel.Indexed
