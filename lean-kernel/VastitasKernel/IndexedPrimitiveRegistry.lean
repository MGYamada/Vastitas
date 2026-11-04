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
hints, the role table, whether a call allocates, and the two evaluators
(`evalPrimitive`, `evalRuntimePrimitive`). The lowering and the decoder are
migrated by the later steps of #622 and still take a case per constructor. A
proof that unfolds a derived table at one constructor needs only
`PrimitiveBinding.contract` (and `PrimitiveDescriptor.ofBool` or
`PrimitiveDescriptor.evidence`) in its `simp` set. Each arm names the exact
checks of `Indexed`, `IndexedPrimitiveBinding` and `IndexedSmoothContracts`;
family, base and object IDs are part of the contract, displayed names and
arbitrary certificates are not.

Index fields are named as their families declare them: a point is
`[target, source]`, a morphism, smooth map or tape `[source, target]`, a
relative morphism `[source, target, base]`, a fiber `[object]`. The role table
reports a shape's families once the operands have its index pattern;
`families := .early` keeps the precedence of the two primitives that report
them as soon as the operands are applications.

The evaluators of an entry match the operand values its shape admits and
return `none` on any other list. The logical one builds the values of
`IndexedPrimitiveValues`; the erased one applies the runtime operations that
generated programs link, on erased values. The two agree up to erasure; the
oracle proves it per entry (`VastitasOracle.IndexedPrimitiveSoundness.Sound`). -/
namespace VastitasKernel.Indexed
open VastitasKernel.Indexed.Audit (validApplication_iff)
open VastitasKernel.Indexed.Core.Semantics (globalObject intPointValue smoothPointValue fiberVectorValue
  intPointRuntime smoothPointRuntime fiberVectorRuntime)

/-- A morphism, smooth map or tape operand. -/
private abbrev mapOperand (role : String) (family : DeclId) : Operand :=
  .indexed role family [.var "source", .var "target"]
/-- A point operand: its first index is the target. -/
private abbrev pointOperand (role : String) (family : DeclId) : Operand :=
  .indexed role family [.var "target", .var "source"]
/-- A morphism over a base. -/
private abbrev relativeMapOperand (role : String) (family : DeclId) : Operand :=
  .indexed role family [.var "source", .var "target", .var "base"]
/-- A vector or covector. -/
private abbrev fiberOperand (role : String) (family : DeclId) : Operand := .indexed role family [.var "object"]
/-- A point of a smooth object: a smooth map from a 0-dimensional object. -/
private abbrev smoothPointOperand (family : DeclId) : Operand := mapOperand "point" family
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
      valid_iff env := by cases implementationType env implementation <;> simp [Bool.and_eq_true]
      eval := fun _ values => match values with
        | [.natural dim] => some (.object ⟨implementation, IndexedRuntime.descriptor dim⟩)
        | _ => none
      evalRuntime := fun values => match values with
        | [.natural dim] => some (.object (IndexedRuntime.descriptor dim))
        | _ => none }
  | .global id =>
    { shape := { operands := [], result := .globalObject id }
      validProp env := affineGlobal env id = true ∧ ObjectRef.Valid env (.global id)
      validBool env := affineGlobal env id && decide (ObjectRef.Valid env (.global id))
      valid_iff env := by simp [Bool.and_eq_true]
      eval := fun env values => match values with
        | [] => (globalObject env id).map Core.Semantics.Value.object
        | _ => none
      evalRuntime := fun values => match values with
        | [] => some (.object IndexedRuntime.baseObject)
        | _ => none }
  | .origin domain family base =>
    { shape :=
        { operands := [.object "object" domain], relations := [.refines 0],
          result := .indexed family [.objectRef 0, .fixed (.global base)] }
      validProp env := domain.Supports env .origin ∧ familyRepresentation env family = some .point ∧
        Application.Valid env ⟨family, [.object (.local domain 0), .object (.global base)]⟩
      validBool env := originContract env domain family base
      valid_iff env := by simp [originContract, Bool.and_eq_true, validApplication_iff, and_assoc]
      eval := fun env values => match values with
        | [.object object] => do
          let baseObject ← globalObject env base
          pure (.indexed (.point ⟨object, baseObject⟩))
        | _ => none
      evalRuntime := fun values => match values with
        | [.object object] => some (.point (IndexedRuntime.origin object IndexedRuntime.baseObject))
        | _ => none }
  | .identity domain family =>
    { shape :=
        { operands := [.object "object" domain], relations := [.refines 0],
          result := .indexed family [.objectRef 0, .objectRef 0] }
      validProp env := domain.Valid env ∧ familyRepresentation env family = some .morphism ∧
        Application.Valid env ⟨family, [.object (.local domain 0), .object (.local domain 0)]⟩
      validBool env := identityContract env domain family
      valid_iff env := by simp [identityContract, Bool.and_eq_true, validApplication_iff, and_assoc]
      eval := fun _ values => match values with
        | [.object object] => some (.indexed (.morphism ⟨object, object⟩))
        | _ => none
      evalRuntime := fun values => match values with
        | [.object object] => some (.morphism (IndexedRuntime.identity object))
        | _ => none }
  | .dimension domain =>
    { shape := { operands := [.object "object" domain], relations := [.refines 0], result := .natural }
      validProp env := domain.Supports env .dimension
      validBool env := decide (domain.Supports env .dimension)
      valid_iff env := by simp
      eval := fun _ values => match values with
        | [.object object] => some (.natural object.descriptor.dimension)
        | _ => none
      evalRuntime := fun values => match values with
        | [.object object] => some (.natural object.dimension)
        | _ => none }
  | .compose family =>
    { shape :=
        { operands := [mapOperand "first map" family, mapOperand "second map" family],
          relations := [.sameRef ⟨0, 0⟩ ⟨1, 1⟩],
          result := .indexed family [.index ⟨1, 0⟩, .index ⟨0, 1⟩] }
      validProp env := familyRepresentation env family = some .morphism
      validBool env := familyRepresentation env family == some .morphism
      valid_iff env := by simp
      eval := fun _ values => match values with
        | [.indexed (.morphism after), .indexed (.morphism before)] =>
            some (.indexed (.morphism ⟨before.source, after.target⟩))
        | _ => none
      evalRuntime := fun values => match values with
        | [.morphism after, .morphism before] => some (.morphism (IndexedRuntime.compose after before))
        | _ => none }
  | .apply maps points =>
    { shape :=
        { operands := [mapOperand "map" maps, pointOperand "point" points],
          relations := [.sameRef ⟨0, 0⟩ ⟨1, 0⟩],
          result := .indexed points [.index ⟨0, 1⟩, .index ⟨1, 1⟩] }
      validProp env := familyRepresentation env maps = some .morphism ∧
        familyRepresentation env points = some .point
      validBool env := familyRepresentation env maps == some .morphism &&
        familyRepresentation env points == some .point
      valid_iff env := by simp [Bool.and_eq_true]
      eval := fun _ values => match values with
        | [.indexed (.morphism map), .indexed (.point point)] => some (.indexed (.point ⟨map.target, point.source⟩))
        | _ => none
      evalRuntime := fun values => match values with
        | [.morphism map, .point point] => some (.point (IndexedRuntime.apply map point))
        | _ => none }
  /- Relative morphisms over a base (Stage 2). -/
  | .relativeConstant application affineMap =>
    .ofBool { operands := [], result := .constant application }
      (fun env => relativeConstantValid env application affineMap)
      (fun _ values => match values with
        | [] => some (.indexed (.relative affineMap))
        | _ => none)
      (fun values => match values with
        | [] => some (.relative affineMap)
        | _ => none)
  | .relativeCompose family =>
    .ofBool
      { operands := [relativeMapOperand "first map" family, relativeMapOperand "second map" family],
        relations := [.sameRef ⟨0, 0⟩ ⟨1, 1⟩, .sameRef ⟨0, 2⟩ ⟨1, 2⟩],
        result := .indexed family [.index ⟨1, 0⟩, .index ⟨0, 1⟩, .index ⟨0, 2⟩] }
      (fun env => isRelativeFamily env family)
      (fun _ values => match values with
        | [.indexed (.relative after), .indexed (.relative before)] =>
            some (.indexed (.relative (AlgebraRuntime.Map.compose after before)))
        | _ => none)
      (fun values => match values with
        | [.relative after, .relative before] => some (.relative (AlgebraRuntime.Map.compose after before))
        | _ => none)
  | .relativeView family source target =>
    { shape :=
        { operands := [.indexed "map" family
            [.var "source", .var "target", .fixed (.global source) "base" "the view's source base"]],
          result := .indexed family [.index ⟨0, 0⟩, .index ⟨0, 1⟩, .fixed (.global target)] }
      validProp env := isRelativeFamily env family = true ∧ onChain env source target = true
      validBool env := isRelativeFamily env family && onChain env source target
      valid_iff env := by simp [Bool.and_eq_true]
      eval := fun _ values => match values with
        | [.indexed (.relative map)] => some (.indexed (.relative map))
        | _ => none
      evalRuntime := fun values => match values with
        | [.relative map] => some (.relative map)
        | _ => none }
  | .relativeEqual family =>
    .ofBool
      { operands := [.application "first map" family, .application "second map" family],
        relations := [.sameApplication 0 1 ["source", "target", "base"]], result := .boolean }
      (fun env => isRelativeFamily env family)
      (fun _ values => match values with
        | [.indexed (.relative left), .indexed (.relative right)] => some (.boolean (AlgebraRuntime.Map.same left right))
        | _ => none)
      (fun values => match values with
        | [.relative left, .relative right] => some (.boolean (AlgebraRuntime.Map.same left right))
        | _ => none)
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
      valid_iff env := by simp [Bool.and_eq_true, and_assoc]
      eval := fun _ values => match values with
        | [.indexed (.relative map)] =>
            let (numerator, denominator) := map.coefficient coordinate monomial
            some (.pairInt numerator denominator)
        | _ => none
      evalRuntime := fun values => match values with
        | [.relative map] =>
            let (numerator, denominator) := map.coefficient coordinate monomial
            some (.pairInt numerator denominator)
        | _ => none }
  | .relativeIntPoint family object base =>
    { shape :=
        { operands := [], tail := some fun env => affineArity env object,
          result := .constant ⟨family, [.object (.global base), .object (.global object), .object (.global base)]⟩ }
      validProp env := isRelativeFamily env family = true ∧ freeAffine env object = true ∧
        pointBase env base = true
      validBool env := isRelativeFamily env family && freeAffine env object && pointBase env base
      valid_iff env := by simp [Bool.and_eq_true, and_assoc]
      eval := fun _ values => intPointValue values
      evalRuntime := intPointRuntime }
  | .relativePair family fiber =>
    { shape :=
        { operands := [relativeMapOperand "first map" family, relativeMapOperand "second map" family],
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
      valid_iff env := by simp [Bool.and_eq_true]
      eval := fun _ values => match values with
        | [.indexed (.relative left), .indexed (.relative right)] =>
            some (.indexed (.relative (AlgebraRuntime.Map.pair left right)))
        | _ => none
      evalRuntime := fun values => match values with
        | [.relative left, .relative right] => some (.relative (AlgebraRuntime.Map.pair left right))
        | _ => none }
  | .relativeIso forward backward => .evidence fun env => relativeIsoValid env forward backward
  | .relativeCartesian first second inverse fiber =>
    .evidence fun env => relativeCartesianValid env first second inverse fiber
  /- Smooth maps, fibers, tapes and metrics (Stage 3). The pullback mode chooses
  how forward values are obtained and is not part of the validity contract. -/
  | .smoothConstant application affineMap =>
    .ofBool { operands := [], result := .constant application }
      (fun env => smoothConstantValid env application affineMap)
      (fun _ values => match values with
        | [] => some (.indexed (.smooth (.primitive affineMap)))
        | _ => none)
      (fun values => match values with
        | [] => some (.smooth (.primitive affineMap))
        | _ => none)
  | .smoothCompose family =>
    .ofBool
      { operands := [mapOperand "first map" family, mapOperand "second map" family],
        relations := [.sameRef ⟨0, 0⟩ ⟨1, 1⟩],
        result := .indexed family [.index ⟨1, 0⟩, .index ⟨0, 1⟩] }
      (fun env => isSmoothFamily env family)
      (fun _ values => match values with
        | [.indexed (.smooth after), .indexed (.smooth before)] => some (.indexed (.smooth (.compose after before)))
        | _ => none)
      (fun values => match values with
        | [.smooth after, .smooth before] => some (.smooth (.compose after before))
        | _ => none)
  | .smoothEqual family =>
    .ofBool
      { operands := [.application "first map" family, .application "second map" family],
        relations := [.sameApplication 0 1 ["source", "target"]], result := .boolean }
      (fun env => isSmoothFamily env family)
      (fun _ values => match values with
        | [.indexed (.smooth left), .indexed (.smooth right)] => some (.boolean (SmoothRuntime.same left right))
        | _ => none)
      (fun values => match values with
        | [.smooth left, .smooth right] => some (.boolean (SmoothRuntime.same left right))
        | _ => none)
  | .smoothIntPoint family object point =>
    .ofBool
      { operands := [], tail := some fun env => smoothArity env object,
        result := .constant ⟨family, [.object (.global point), .object (.global object)]⟩ }
      (fun env => smoothIntPointValid env family object point)
      (fun _ values => smoothPointValue values)
      smoothPointRuntime
  | .smoothComposite family =>
    .ofBool { operands := [.application "map" family], result := .application 0 }
      (fun env => isSmoothFamily env family)
      (fun _ values => match values with
        | [.indexed (.smooth program)] => some (.indexed (.smooth (SmoothRuntime.composite program)))
        | _ => none)
      (fun values => match values with
        | [.smooth program] => some (.smooth (SmoothRuntime.composite program))
        | _ => none)
  | .fiberVector family smooth object =>
    .ofBool
      { operands := [.indexed "point" smooth
          [.var "source", .fixed (.global object) "target" "the primitive's declared object"]],
        tail := some fun env => smoothArity env object, relations := [.pointDimension ⟨0, 0⟩ 0],
        result := .constant ⟨family, [.object (.global object)]⟩ }
      (fun env => fiberVectorValid env family smooth object)
      (fun env values => match values with
        | .indexed (.smooth point) :: components => fiberVectorValue env family point components
        | _ => none)
      (fun values => match values with
        | .smooth point :: components => fiberVectorRuntime point components
        | _ => none)
  | .fiberAt family smooth =>
    .ofBool
      { operands := [fiberOperand "element" family, smoothPointOperand smooth],
        relations := [.sameRef ⟨0, 0⟩ ⟨1, 1⟩, pointAtOrigin], result := .boolean }
      (fun env => fiberAtValid env family smooth)
      (fun _ values => match values with
        | [.indexed (.fiber _ value), .indexed (.smooth point)] => some (.boolean (SmoothRuntime.fiberAt value point))
        | _ => none)
      (fun values => match values with
        | [.fiber value, .smooth point] => some (.boolean (SmoothRuntime.fiberAt value point))
        | _ => none)
  | .fiberEqual family =>
    .ofBool
      { operands := [.application "first element" family, .application "second element" family],
        relations := [.sameApplication 0 1 ["object"]], result := .boolean }
      (fun env => fiberEqualValid env family)
      (fun _ values => match values with
        | [.indexed (.fiber _ left), .indexed (.fiber _ right)] => some (.boolean (SmoothRuntime.fiberEqual left right))
        | _ => none)
      (fun values => match values with
        | [.fiber left, .fiber right] => some (.boolean (SmoothRuntime.fiberEqual left right))
        | _ => none)
  | .fiberComponent family object coordinate =>
    .ofBool
      { operands := [.indexed "element" family [.fixed (.global object) "object" "the primitive's declared object"]],
        result := .integerPair }
      (fun env => fiberComponentValid env family object coordinate)
      (fun _ values => match values with
        | [.indexed (.fiber _ value)] =>
            let (numerator, denominator) := SmoothRuntime.component value coordinate
            some (.pairInt numerator denominator)
        | _ => none)
      (fun values => match values with
        | [.fiber value] =>
            let (numerator, denominator) := SmoothRuntime.component value coordinate
            some (.pairInt numerator denominator)
        | _ => none)
  | .fiberPairing cotangent tangent =>
    .ofBool
      { operands := [fiberOperand "covector" cotangent, fiberOperand "vector" tangent],
        relations := [.sameRef ⟨0, 0⟩ ⟨1, 0⟩], result := .integerPair }
      (fun env => fiberPairingValid env cotangent tangent)
      (fun _ values => match values with
        | [.indexed (.fiber _ covector), .indexed (.fiber _ vector)] =>
            let (numerator, denominator) := SmoothRuntime.pairing covector vector
            some (.pairInt numerator denominator)
        | _ => none)
      (fun values => match values with
        | [.fiber covector, .fiber vector] =>
            let (numerator, denominator) := SmoothRuntime.pairing covector vector
            some (.pairInt numerator denominator)
        | _ => none)
  | .cotangentPullback smooth cotangent mode =>
    .ofBool
      { operands := [mapOperand "map" smooth, smoothPointOperand smooth, fiberOperand "seed" cotangent],
        relations := [.sameRef ⟨0, 0⟩ ⟨1, 1⟩, .sameRef ⟨0, 1⟩ ⟨2, 0⟩, pointAtOrigin],
        result := .indexed cotangent [.index ⟨0, 0⟩] }
      (fun env => cotangentPullbackValid env smooth cotangent)
      (fun _ values => match values with
        | [.indexed (.smooth map), .indexed (.smooth point), .indexed (.fiber _ seed)] =>
            some (.indexed (.fiber .cotangent (SmoothRuntime.pullback mode map point seed)))
        | _ => none)
      (fun values => match values with
        | [.smooth map, .smooth point, .fiber seed] => some (.fiber (SmoothRuntime.pullback mode map point seed))
        | _ => none)
  | .differential smooth cotangent line =>
    .ofBool
      { operands := [.indexed "function" smooth
          [.var "source", .fixed (.global line) "target" "the primitive's declared line"], smoothPointOperand smooth],
        relations := [.sameRef ⟨0, 0⟩ ⟨1, 1⟩, pointAtOrigin], result := .indexed cotangent [.index ⟨0, 0⟩] }
      (fun env => differentialValid env smooth cotangent line)
      (fun _ values => match values with
        | [.indexed (.smooth function), .indexed (.smooth point)] =>
            some (.indexed (.fiber .cotangent (SmoothRuntime.differential function point)))
        | _ => none)
      (fun values => match values with
        | [.smooth function, .smooth point] => some (.fiber (SmoothRuntime.differential function point))
        | _ => none)
  | .linearize smooth tape =>
    .ofBool
      { operands := [mapOperand "map" smooth, smoothPointOperand smooth],
        relations := [.sameRef ⟨0, 0⟩ ⟨1, 1⟩, pointAtOrigin],
        result := .indexed tape [.index ⟨0, 0⟩, .index ⟨0, 1⟩] }
      (fun env => linearizeValid env smooth tape)
      (fun _ values => match values with
        | [.indexed (.smooth map), .indexed (.smooth point)] =>
            some (.indexed (.tape (SmoothRuntime.linearize map point)))
        | _ => none)
      (fun values => match values with
        | [.smooth map, .smooth point] => some (.tape (SmoothRuntime.linearize map point))
        | _ => none)
  | .cotangentBackward tape cotangent =>
    .ofBool
      { operands := [mapOperand "tape" tape, fiberOperand "seed" cotangent],
        relations := [.sameRef ⟨0, 1⟩ ⟨1, 0⟩], result := .indexed cotangent [.index ⟨0, 0⟩] }
      (fun env => cotangentBackwardValid env tape cotangent)
      (fun _ values => match values with
        | [.indexed (.tape record), .indexed (.fiber _ seed)] =>
            some (.indexed (.fiber .cotangent (SmoothRuntime.backward record seed)))
        | _ => none)
      (fun values => match values with
        | [.tape record, .fiber seed] => some (.fiber (SmoothRuntime.backward record seed))
        | _ => none)
  | .metricFlat metric object gram tangent cotangent =>
    .ofBool
      { operands := [.indexed "vector" tangent [.fixed (.global object) "object" "the metric's object"]],
        result := .indexed cotangent [.fixed (.global object)] }
      (fun env => metricFlatValid env metric object gram tangent cotangent)
      (fun _ values => match values with
        | [.indexed (.fiber _ vector)] => some (.indexed (.fiber .cotangent (SmoothRuntime.flat gram vector)))
        | _ => none)
      (fun values => match values with
        | [.fiber vector] => some (.fiber (SmoothRuntime.flat gram vector))
        | _ => none)
  | .metricSharp metric evidence object gram inverse cotangent tangent =>
    .ofBool
      { operands := [.indexed "covector" cotangent [.fixed (.global object) "object" "the metric's object"]],
        result := .indexed tangent [.fixed (.global object)] }
      (fun env => metricSharpValid env metric evidence object gram inverse cotangent tangent)
      (fun _ values => match values with
        | [.indexed (.fiber _ covector)] => some (.indexed (.fiber .tangent (SmoothRuntime.sharp inverse covector)))
        | _ => none)
      (fun values => match values with
        | [.fiber covector] => some (.fiber (SmoothRuntime.sharp inverse covector))
        | _ => none)

end VastitasKernel.Indexed
