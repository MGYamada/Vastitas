import VastitasKernel.IndexedSourceDiagnostics
import VastitasKernel.IndexedSemantics

/-! Frozen copies of the primitive tables as they were before the registry
(#622), with the proof that the derived tables agree with them on every
binding. Each table that moves into `PrimitiveBinding.contract` keeps its
pre-registry definition here until the migration is complete. The validity
contracts agree by definitional unfolding; the operand count agrees by a
theorem, and so do the argument hints at every position below the operand
count, which are all the elaborators consult (the pre-registry `descriptor`
hint also answered the positions beyond it); the two evaluators and the fresh
slot agree by theorem; the association, result inference, the role table and
the explanation of a rejected call are compared on an enumerated corpus of
operand lists, well shaped and malformed, and the evaluators on a corpus of
value lists, at the end of this module. The module is deleted at the end of
the migration; the emit goldens (`tests/fixtures/emit`) stay. -/
namespace VastitasKernel.Indexed.PrimitiveLegacyRegression
open VastitasKernel.Indexed.Source.Diagnostics (RoleRequirement PrimitiveFailure explainPrimitive roleTable)

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


/-! ## The typing tables before the shapes (step 2) -/

def legacyArity (env : Environment) : PrimitiveBinding → Nat
  | .global _ | .relativeConstant .. | .relativeIso .. | .relativeCartesian .. | .smoothConstant .. => 0
  | .compose _ | .apply .. | .relativeCompose _ | .relativeEqual _ | .relativePair ..
  | .smoothCompose _ | .smoothEqual _ | .fiberAt .. | .fiberEqual _ | .fiberPairing ..
  | .differential .. | .linearize .. | .cotangentBackward .. => 2
  | .cotangentPullback .. => 3
  | .relativeIntPoint _ object _ => affineArity env object
  | .smoothIntPoint _ object _ => smoothArity env object
  | .fiberVector _ _ object => smoothArity env object + 1
  | _ => 1

def legacyAssociation (env : Environment) (binding : PrimitiveBinding) (allowed : List ObjectRef)
    (brand : Nat) (arguments : List ValueType) (result : ValueType) : Prop :=
  match binding, arguments with
  | .descriptor implementation, [.natural] =>
      ∃ ty ∈ implementationType env implementation,
        FreshBrand allowed brand ∧ result = .object ty (.local ty brand)
  | .global id, [] => ∃ ty ∈ ObjectRef.type? env (.global id), result = .object ty (.global id)
  | .origin expected family base, [.object actual reference] =>
      actual.Refines env expected ∧ result = .indexed ⟨family, [.object reference, .object (.global base)]⟩
  | .identity expected family, [.object actual reference] =>
      actual.Refines env expected ∧ result = .indexed ⟨family, [.object reference, .object reference]⟩
  | .dimension expected, [.object actual _] => actual.Refines env expected ∧ result = .natural
  | .compose family, [.indexed ⟨gf, [.object middle, .object target]⟩,
      .indexed ⟨ff, [.object source, .object middle']⟩] =>
      gf = family ∧ ff = family ∧ middle = middle' ∧
        result = .indexed ⟨family, [.object source, .object target]⟩
  | .apply maps points, [.indexed ⟨mf, [.object source, .object target]⟩,
      .indexed ⟨pf, [.object target', .object test]⟩] =>
      mf = maps ∧ pf = points ∧ source = target' ∧
        result = .indexed ⟨points, [.object target, .object test]⟩
  | .relativeConstant application _, [] => result = .indexed application
  | .relativeCompose family, [.indexed ⟨gf, [.object middle, .object target, .object base]⟩,
      .indexed ⟨ff, [.object source, .object middle', .object base']⟩] =>
      gf = family ∧ ff = family ∧ middle = middle' ∧ base = base' ∧
        result = .indexed ⟨family, [.object source, .object target, .object base]⟩
  | .relativeView family origin to, [.indexed ⟨f, [.object source, .object target, .object base]⟩] =>
      f = family ∧ base = .global origin ∧
        result = .indexed ⟨family, [.object source, .object target, .object (.global to)]⟩
  | .relativeEqual family, [.indexed left, .indexed right] =>
      left.family = family ∧ left = right ∧ result = .boolean
  | .relativeCoefficient family source target _ _,
      [.indexed ⟨f, [.object (.global x), .object (.global y), .object _]⟩] =>
      f = family ∧ x = source ∧ y = target ∧ result = .integerPair
  | .relativeIntPoint family object base, arguments =>
      arguments = (List.range (affineArity env object)).map (fun _ => .integer) ∧
        result = .indexed ⟨family, [.object (.global base), .object (.global object), .object (.global base)]⟩
  | .relativePair family fiber, [.indexed ⟨lf, [.object source, .object left, .object base]⟩,
      .indexed ⟨rf, [.object source', .object right, .object base']⟩] =>
      lf = family ∧ rf = family ∧ source = source' ∧ base = base' ∧
        pairFactors env fiber left right base = true ∧
        result = .indexed ⟨family, [.object source, .object (.global fiber), .object base]⟩
  | .smoothConstant application _, [] => result = .indexed application
  | .smoothCompose family, [.indexed ⟨gf, [.object middle, .object target]⟩,
      .indexed ⟨ff, [.object source, .object middle']⟩] =>
      gf = family ∧ ff = family ∧ middle = middle' ∧
        result = .indexed ⟨family, [.object source, .object target]⟩
  | .smoothEqual family, [.indexed left, .indexed right] =>
      left.family = family ∧ left = right ∧ result = .boolean
  | .smoothIntPoint family object point, arguments =>
      arguments = (List.range (smoothArity env object)).map (fun _ => .integer) ∧
        result = .indexed ⟨family, [.object (.global point), .object (.global object)]⟩
  | .smoothComposite family, [.indexed application] =>
      application.family = family ∧ result = .indexed application
  | .fiberVector family smooth object, .indexed ⟨sf, [.object (.global point), .object x]⟩ :: components =>
      sf = smooth ∧ x = .global object ∧ smoothDimension? env point = some 0 ∧
        components = (List.range (smoothArity env object)).map (fun _ => .integer) ∧
        result = .indexed ⟨family, [.object (.global object)]⟩
  | .fiberAt family smooth, [.indexed ⟨ff, [.object x]⟩, .indexed ⟨sf, [.object (.global point), .object x']⟩] =>
      ff = family ∧ sf = smooth ∧ x = x' ∧ smoothDimension? env point = some 0 ∧ result = .boolean
  | .fiberEqual family, [.indexed left, .indexed right] =>
      left.family = family ∧ left = right ∧ result = .boolean
  | .fiberComponent family object _, [.indexed ⟨ff, [.object x]⟩] =>
      ff = family ∧ x = .global object ∧ result = .integerPair
  | .fiberPairing cotangent tangent, [.indexed ⟨cf, [.object x]⟩, .indexed ⟨tf, [.object x']⟩] =>
      cf = cotangent ∧ tf = tangent ∧ x = x' ∧ result = .integerPair
  | .cotangentPullback smooth cotangent _, [.indexed ⟨mf, [.object x, .object y]⟩,
      .indexed ⟨pf, [.object (.global point), .object x']⟩, .indexed ⟨cf, [.object y']⟩] =>
      mf = smooth ∧ pf = smooth ∧ cf = cotangent ∧ x = x' ∧ y = y' ∧ smoothDimension? env point = some 0 ∧
        result = .indexed ⟨cotangent, [.object x]⟩
  | .differential smooth cotangent line, [.indexed ⟨mf, [.object x, .object y]⟩,
      .indexed ⟨pf, [.object (.global point), .object x']⟩] =>
      mf = smooth ∧ pf = smooth ∧ y = .global line ∧ x = x' ∧ smoothDimension? env point = some 0 ∧
        result = .indexed ⟨cotangent, [.object x]⟩
  | .linearize smooth tape, [.indexed ⟨mf, [.object x, .object y]⟩,
      .indexed ⟨pf, [.object (.global point), .object x']⟩] =>
      mf = smooth ∧ pf = smooth ∧ x = x' ∧ smoothDimension? env point = some 0 ∧
        result = .indexed ⟨tape, [.object x, .object y]⟩
  | .cotangentBackward tape cotangent, [.indexed ⟨tf, [.object x, .object y]⟩, .indexed ⟨cf, [.object y']⟩] =>
      tf = tape ∧ cf = cotangent ∧ y = y' ∧ result = .indexed ⟨cotangent, [.object x]⟩
  | .metricFlat _ object _ tangent cotangent, [.indexed ⟨tf, [.object x]⟩] =>
      tf = tangent ∧ x = .global object ∧ result = .indexed ⟨cotangent, [.object (.global object)]⟩
  | .metricSharp _ _ object _ _ cotangent tangent, [.indexed ⟨cf, [.object x]⟩] =>
      cf = cotangent ∧ x = .global object ∧ result = .indexed ⟨tangent, [.object (.global object)]⟩
  | _, _ => False

instance (env : Environment) (binding : PrimitiveBinding) (allowed : List ObjectRef)
    (brand : Nat) (arguments : List ValueType) (result : ValueType) :
    Decidable (legacyAssociation env binding allowed brand arguments result) := by
  unfold legacyAssociation
  split <;> infer_instance

def legacyInfer (env : Environment) (binding : PrimitiveBinding) (brand : Nat)
    (arguments : List ValueType) : Option ValueType :=
  match binding, arguments with
  | .descriptor implementation, [.natural] => do
    let ty ← implementationType env implementation
    pure (.object ty (.local ty brand))
  | .global id, [] => do
    let ty ← ObjectRef.type? env (.global id)
    pure (.object ty (.global id))
  | .origin _ family base, [.object _ ref] =>
      some (.indexed ⟨family, [.object ref, .object (.global base)]⟩)
  | .identity _ family, [.object _ ref] => some (.indexed ⟨family, [.object ref, .object ref]⟩)
  | .dimension _, [.object ..] => some .natural
  | .compose family, [.indexed ⟨_, [.object _, .object target]⟩,
      .indexed ⟨_, [.object source, .object _]⟩] => some (.indexed ⟨family, [.object source, .object target]⟩)
  | .apply _ points, [.indexed ⟨_, [.object _, .object target]⟩,
      .indexed ⟨_, [.object _, .object test]⟩] => some (.indexed ⟨points, [.object target, .object test]⟩)
  | .relativeConstant application _, [] => some (.indexed application)
  | .relativeCompose family, [.indexed ⟨_, [.object _, .object target, .object base]⟩,
      .indexed ⟨_, [.object source, .object _, .object _]⟩] =>
      some (.indexed ⟨family, [.object source, .object target, .object base]⟩)
  | .relativeView family _ to, [.indexed ⟨_, [.object source, .object target, .object _]⟩] =>
      some (.indexed ⟨family, [.object source, .object target, .object (.global to)]⟩)
  | .relativeEqual _, [.indexed _, .indexed _] => some .boolean
  | .relativeCoefficient .., [.indexed _] => some .integerPair
  | .relativeIntPoint family object base, _ =>
      some (.indexed ⟨family, [.object (.global base), .object (.global object), .object (.global base)]⟩)
  | .relativePair family fiber, [.indexed ⟨_, [.object source, .object _, .object base]⟩, .indexed _] =>
      some (.indexed ⟨family, [.object source, .object (.global fiber), .object base]⟩)
  | .smoothConstant application _, [] => some (.indexed application)
  | .smoothCompose family, [.indexed ⟨_, [.object _, .object target]⟩,
      .indexed ⟨_, [.object source, .object _]⟩] => some (.indexed ⟨family, [.object source, .object target]⟩)
  | .smoothEqual _, [.indexed _, .indexed _] => some .boolean
  | .smoothIntPoint family object point, _ =>
      some (.indexed ⟨family, [.object (.global point), .object (.global object)]⟩)
  | .smoothComposite _, [.indexed application] => some (.indexed application)
  | .fiberVector family _ object, _ => some (.indexed ⟨family, [.object (.global object)]⟩)
  | .fiberAt .., [.indexed _, .indexed _] | .fiberEqual _, [.indexed _, .indexed _] => some .boolean
  | .fiberComponent .., [.indexed _] | .fiberPairing .., [.indexed _, .indexed _] => some .integerPair
  | .cotangentPullback _ cotangent _, [.indexed ⟨_, [.object source, .object _]⟩, .indexed _, .indexed _]
  | .differential _ cotangent _, [.indexed ⟨_, [.object source, .object _]⟩, .indexed _] =>
      some (.indexed ⟨cotangent, [.object source]⟩)
  | .linearize _ tape, [.indexed ⟨_, [.object source, .object target]⟩, .indexed _] =>
      some (.indexed ⟨tape, [.object source, .object target]⟩)
  | .cotangentBackward _ cotangent, [.indexed ⟨_, [.object source, .object _]⟩, .indexed _] =>
      some (.indexed ⟨cotangent, [.object source]⟩)
  | .metricFlat _ object _ _ cotangent, [.indexed _] => some (.indexed ⟨cotangent, [.object (.global object)]⟩)
  | .metricSharp _ _ object _ _ _ tangent, [.indexed _] => some (.indexed ⟨tangent, [.object (.global object)]⟩)
  | _, _ => none

def legacyArgumentHint : PrimitiveBinding → Nat → Option Core.DataType
  | .descriptor _, _ => some (.pure .nat)
  | .relativeIntPoint .., _ | .smoothIntPoint .., _ => some (.pure .int)
  | .fiberVector .., position => if position = 0 then none else some (.pure .int)
  | _, _ => none

def legacyRoleTable (env : Environment) : PrimitiveBinding → List ValueType → List RoleRequirement
  | .origin expected _ _, [.object actual reference]
  | .identity expected _, [.object actual reference]
  | .dimension expected, [.object actual reference] =>
    [.marker "object" reference expected.marker actual.marker, .domain "object" reference expected actual]
  | .compose family, [.indexed ⟨first, [.object middle, .object _]⟩,
      .indexed ⟨second, [.object _, .object middle']⟩] =>
    [.family "first map" family first, .family "second map" family second,
     .object "second map" "target" middle middle' "the first map's source"]
  | .apply maps points, [.indexed ⟨map, [.object source, .object _]⟩,
      .indexed ⟨point, [.object target, .object _]⟩] =>
    [.family "map" maps map, .family "point" points point,
     .object "point" "target" source target "the map's source"]
  | .relativeCompose family, [.indexed ⟨first, [.object middle, .object _, .object base]⟩,
      .indexed ⟨second, [.object _, .object middle', .object base']⟩] =>
    [.family "first map" family first, .family "second map" family second,
     .object "second map" "target" middle middle' "the first map's source",
     .object "second map" "base" base base' "the first map's base"]
  | .relativeView family origin _, [.indexed ⟨map, [.object _, .object _, .object base]⟩] =>
    [.family "map" family map, .object "map" "base" (.global origin) base "the view's source base"]
  | .relativeEqual family, [.indexed ⟨first, firstIndices⟩, .indexed ⟨second, secondIndices⟩] =>
    [.family "first map" family first, .family "second map" family second] ++
    match firstIndices, secondIndices with
    | [.object source, .object target, .object base], [.object source', .object target', .object base'] =>
      [.object "second map" "source" source source' "the first map's source",
       .object "second map" "target" target target' "the first map's target",
       .object "second map" "base" base base' "the first map's base"]
    | _, _ => []
  | .relativeCoefficient family source target _ _, [.indexed ⟨map, indices⟩] =>
    .family "map" family map ::
    match indices with
    | [.object source', .object target', .object _] =>
      [.object "map" "source" (.global source) source' "the primitive's declared source",
       .object "map" "target" (.global target) target' "the primitive's declared target"]
    | _ => []
  | .relativePair family fiber, [.indexed ⟨first, firstIndices⟩, .indexed ⟨second, secondIndices⟩] =>
    [.family "first map" family first, .family "second map" family second] ++
    match firstIndices, secondIndices, plainFiber? env fiber with
    | [.object source, .object left, .object base], [.object source', .object right, .object base'],
        some (factor, factor', fiberBase) =>
      [.object "second map" "source" source source' "the first map's source",
       .object "first map" "base" (.global fiberBase) base "the fiber's base",
       .object "second map" "base" (.global fiberBase) base' "the fiber's base",
       .object "first map" "target" (.global factor) left "the fiber's first factor",
       .object "second map" "target" (.global factor') right "the fiber's second factor"]
    | _, _, _ => []
  | .smoothCompose family, [.indexed ⟨first, [.object middle, .object _]⟩,
      .indexed ⟨second, [.object _, .object middle']⟩] =>
    [.family "first map" family first, .family "second map" family second,
     .object "second map" "target" middle middle' "the first map's source"]
  | .smoothEqual family, [.indexed ⟨first, firstIndices⟩, .indexed ⟨second, secondIndices⟩] =>
    [.family "first map" family first, .family "second map" family second] ++
    match firstIndices, secondIndices with
    | [.object source, .object target], [.object source', .object target'] =>
      [.object "second map" "source" source source' "the first map's source",
       .object "second map" "target" target target' "the first map's target"]
    | _, _ => []
  | .smoothComposite family, [.indexed ⟨map, _⟩] => [.family "map" family map]
  | .fiberVector _ smooth object, .indexed ⟨point, [.object (.global _), .object x]⟩ :: _ =>
    [.family "point" smooth point,
     .object "point" "target" (.global object) x "the primitive's declared object"]
  | .fiberAt family smooth, [.indexed ⟨element, [.object x]⟩,
      .indexed ⟨point, [.object (.global _), .object x']⟩] =>
    [.family "element" family element, .family "point" smooth point,
     .object "point" "target" x x' "the element's object"]
  | .fiberEqual family, [.indexed ⟨first, firstIndices⟩, .indexed ⟨second, secondIndices⟩] =>
    [.family "first element" family first, .family "second element" family second] ++
    match firstIndices, secondIndices with
    | [.object x], [.object x'] => [.object "second element" "object" x x' "the first element's object"]
    | _, _ => []
  | .fiberComponent family object _, [.indexed ⟨element, [.object x]⟩] =>
    [.family "element" family element,
     .object "element" "object" (.global object) x "the primitive's declared object"]
  | .fiberPairing cotangent tangent, [.indexed ⟨covector, [.object x]⟩, .indexed ⟨vector, [.object x']⟩] =>
    [.family "covector" cotangent covector, .family "vector" tangent vector,
     .object "vector" "object" x x' "the covector's object"]
  | .cotangentPullback smooth cotangent _, [.indexed ⟨map, [.object x, .object y]⟩,
      .indexed ⟨point, [.object (.global _), .object x']⟩, .indexed ⟨seed, [.object y']⟩] =>
    [.family "map" smooth map, .family "point" smooth point, .family "seed" cotangent seed,
     .object "point" "target" x x' "the map's source",
     .object "seed" "object" y y' "the map's target"]
  | .differential smooth _ line, [.indexed ⟨function, [.object x, .object y]⟩,
      .indexed ⟨point, [.object (.global _), .object x']⟩] =>
    [.family "function" smooth function, .family "point" smooth point,
     .object "function" "target" (.global line) y "the primitive's declared line",
     .object "point" "target" x x' "the function's source"]
  | .linearize smooth _, [.indexed ⟨map, [.object x, .object _]⟩,
      .indexed ⟨point, [.object (.global _), .object x']⟩] =>
    [.family "map" smooth map, .family "point" smooth point,
     .object "point" "target" x x' "the map's source"]
  | .cotangentBackward tape cotangent, [.indexed ⟨recorded, [.object _, .object y]⟩,
      .indexed ⟨seed, [.object y']⟩] =>
    [.family "tape" tape recorded, .family "seed" cotangent seed,
     .object "seed" "object" y y' "the tape's target"]
  | .metricFlat _ object _ tangent _, [.indexed ⟨vector, [.object x]⟩] =>
    [.family "vector" tangent vector,
     .object "vector" "object" (.global object) x "the metric's object"]
  | .metricSharp _ _ object _ _ cotangent _, [.indexed ⟨covector, [.object x]⟩] =>
    [.family "covector" cotangent covector,
     .object "covector" "object" (.global object) x "the metric's object"]
  | _, _ => []

theorem arity_agrees (env : Environment) (binding : PrimitiveBinding) :
    binding.arity env = legacyArity env binding := by
  cases binding <;> simp [PrimitiveBinding.arity, Shape.arity, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
    PrimitiveDescriptor.evidence, Shape.uncallable, legacyArity] <;> omega

/-- The hints agree at every operand position; the elaborators check the
operand count first, so no other position is consulted. -/
theorem argumentHint_agrees (env : Environment) (binding : PrimitiveBinding) (position : Nat)
    (bound : position < binding.arity env) :
    binding.argumentHint position = legacyArgumentHint binding position := by
  cases binding <;> rcases position with _ | _ | _ | position <;>
    simp_all [PrimitiveBinding.argumentHint, legacyArgumentHint, PrimitiveBinding.arity, Shape.arity,
      PrimitiveBinding.contract, PrimitiveDescriptor.ofBool, PrimitiveDescriptor.evidence, Shape.uncallable] <;> omega

/-! ## The evaluators before the registry (step 3) -/

open VastitasKernel.Indexed.Core.Semantics (Value PrimitiveRuntimeValue World globalObject intPointValue
  smoothPointValue fiberVectorValue intPointRuntime smoothPointRuntime fiberVectorRuntime evalPrimitive
  evalRuntimePrimitive PrimitiveFresh)

def legacyEvalPrimitive (env : Environment) : PrimitiveBinding → List Value → Option Value
  | .descriptor implementation, [.natural dimension] =>
      some (.object ⟨implementation, IndexedRuntime.descriptor dimension⟩)
  | .global id, [] => (globalObject env id).map Value.object
  | .origin _ _ base, [.object object] => do
      let baseObject ← globalObject env base
      pure (.indexed (.point ⟨object, baseObject⟩))
  | .identity _ _, [.object object] => some (.indexed (.morphism ⟨object, object⟩))
  | .dimension _, [.object object] => some (.natural object.descriptor.dimension)
  | .compose _, [.indexed (.morphism after), .indexed (.morphism before)] =>
      some (.indexed (.morphism ⟨before.source, after.target⟩))
  | .apply _ _, [.indexed (.morphism map), .indexed (.point point)] =>
      some (.indexed (.point ⟨map.target, point.source⟩))
  | .relativeConstant _ map, [] => some (.indexed (.relative map))
  | .relativeCompose _, [.indexed (.relative after), .indexed (.relative before)] =>
      some (.indexed (.relative (AlgebraRuntime.Map.compose after before)))
  | .relativeView .., [.indexed (.relative map)] => some (.indexed (.relative map))
  | .relativeEqual _, [.indexed (.relative left), .indexed (.relative right)] =>
      some (.boolean (AlgebraRuntime.Map.same left right))
  | .relativeCoefficient _ _ _ coordinate monomial, [.indexed (.relative map)] =>
      let (numerator, denominator) := map.coefficient coordinate monomial
      some (.pairInt numerator denominator)
  | .relativeIntPoint .., values => intPointValue values
  | .relativePair .., [.indexed (.relative left), .indexed (.relative right)] =>
      some (.indexed (.relative (AlgebraRuntime.Map.pair left right)))
  | .smoothConstant _ map, [] => some (.indexed (.smooth (.primitive map)))
  | .smoothCompose _, [.indexed (.smooth after), .indexed (.smooth before)] =>
      some (.indexed (.smooth (.compose after before)))
  | .smoothEqual _, [.indexed (.smooth left), .indexed (.smooth right)] =>
      some (.boolean (SmoothRuntime.same left right))
  | .smoothIntPoint .., values => smoothPointValue values
  | .smoothComposite _, [.indexed (.smooth program)] =>
      some (.indexed (.smooth (SmoothRuntime.composite program)))
  | .fiberVector family .., .indexed (.smooth point) :: components => fiberVectorValue env family point components
  | .fiberAt .., [.indexed (.fiber _ value), .indexed (.smooth point)] =>
      some (.boolean (SmoothRuntime.fiberAt value point))
  | .fiberEqual _, [.indexed (.fiber _ left), .indexed (.fiber _ right)] =>
      some (.boolean (SmoothRuntime.fiberEqual left right))
  | .fiberComponent _ _ coordinate, [.indexed (.fiber _ value)] =>
      let (numerator, denominator) := SmoothRuntime.component value coordinate
      some (.pairInt numerator denominator)
  | .fiberPairing .., [.indexed (.fiber _ covector), .indexed (.fiber _ vector)] =>
      let (numerator, denominator) := SmoothRuntime.pairing covector vector
      some (.pairInt numerator denominator)
  | .cotangentPullback _ _ mode, [.indexed (.smooth map), .indexed (.smooth point), .indexed (.fiber _ seed)] =>
      some (.indexed (.fiber .cotangent (SmoothRuntime.pullback mode map point seed)))
  | .differential .., [.indexed (.smooth function), .indexed (.smooth point)] =>
      some (.indexed (.fiber .cotangent (SmoothRuntime.differential function point)))
  | .linearize .., [.indexed (.smooth map), .indexed (.smooth point)] =>
      some (.indexed (.tape (SmoothRuntime.linearize map point)))
  | .cotangentBackward .., [.indexed (.tape tape), .indexed (.fiber _ seed)] =>
      some (.indexed (.fiber .cotangent (SmoothRuntime.backward tape seed)))
  | .metricFlat _ _ gram _ _, [.indexed (.fiber _ vector)] =>
      some (.indexed (.fiber .cotangent (SmoothRuntime.flat gram vector)))
  | .metricSharp _ _ _ _ inverse _ _, [.indexed (.fiber _ covector)] =>
      some (.indexed (.fiber .tangent (SmoothRuntime.sharp inverse covector)))
  | _, _ => none

def legacyEvalRuntimePrimitive : PrimitiveBinding → List PrimitiveRuntimeValue → Option PrimitiveRuntimeValue
  | .descriptor _, [.natural dimension] => some (.object (IndexedRuntime.descriptor dimension))
  | .global _, [] => some (.object IndexedRuntime.baseObject)
  | .origin _ _ _, [.object object] => some (.point (IndexedRuntime.origin object IndexedRuntime.baseObject))
  | .identity _ _, [.object object] => some (.morphism (IndexedRuntime.identity object))
  | .dimension _, [.object object] => some (.natural object.dimension)
  | .compose _, [.morphism after, .morphism before] => some (.morphism (IndexedRuntime.compose after before))
  | .apply _ _, [.morphism map, .point point] => some (.point (IndexedRuntime.apply map point))
  | .relativeConstant _ map, [] => some (.relative map)
  | .relativeCompose _, [.relative after, .relative before] =>
      some (.relative (AlgebraRuntime.Map.compose after before))
  | .relativeView .., [.relative map] => some (.relative map)
  | .relativeEqual _, [.relative left, .relative right] => some (.boolean (AlgebraRuntime.Map.same left right))
  | .relativeCoefficient _ _ _ coordinate monomial, [.relative map] =>
      let (numerator, denominator) := map.coefficient coordinate monomial
      some (.pairInt numerator denominator)
  | .relativeIntPoint .., values => intPointRuntime values
  | .relativePair .., [.relative left, .relative right] => some (.relative (AlgebraRuntime.Map.pair left right))
  | .smoothConstant _ map, [] => some (.smooth (.primitive map))
  | .smoothCompose _, [.smooth after, .smooth before] => some (.smooth (.compose after before))
  | .smoothEqual _, [.smooth left, .smooth right] => some (.boolean (SmoothRuntime.same left right))
  | .smoothIntPoint .., values => smoothPointRuntime values
  | .smoothComposite _, [.smooth program] => some (.smooth (SmoothRuntime.composite program))
  | .fiberVector .., .smooth point :: components => fiberVectorRuntime point components
  | .fiberAt .., [.fiber value, .smooth point] => some (.boolean (SmoothRuntime.fiberAt value point))
  | .fiberEqual _, [.fiber left, .fiber right] => some (.boolean (SmoothRuntime.fiberEqual left right))
  | .fiberComponent _ _ coordinate, [.fiber value] =>
      let (numerator, denominator) := SmoothRuntime.component value coordinate
      some (.pairInt numerator denominator)
  | .fiberPairing .., [.fiber covector, .fiber vector] =>
      let (numerator, denominator) := SmoothRuntime.pairing covector vector
      some (.pairInt numerator denominator)
  | .cotangentPullback _ _ mode, [.smooth map, .smooth point, .fiber seed] =>
      some (.fiber (SmoothRuntime.pullback mode map point seed))
  | .differential .., [.smooth function, .smooth point] =>
      some (.fiber (SmoothRuntime.differential function point))
  | .linearize .., [.smooth map, .smooth point] => some (.tape (SmoothRuntime.linearize map point))
  | .cotangentBackward .., [.tape tape, .fiber seed] => some (.fiber (SmoothRuntime.backward tape seed))
  | .metricFlat _ _ gram _ _, [.fiber vector] => some (.fiber (SmoothRuntime.flat gram vector))
  | .metricSharp _ _ _ _ inverse _ _, [.fiber covector] => some (.fiber (SmoothRuntime.sharp inverse covector))
  | _, _ => none

def legacyPrimitiveFresh (binding : PrimitiveBinding) (world : World) (brand : Nat) : Prop :=
  match binding with | .descriptor _ => world brand = none | _ => True

/-- `descriptor` is the one allocating binding, as before. -/
theorem allocates_agrees (binding : PrimitiveBinding) :
    binding.allocates = true ↔ ∃ implementation, binding = .descriptor implementation := by
  cases binding <;> simp [PrimitiveBinding.allocates, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
    PrimitiveDescriptor.evidence, Shape.allocates, Shape.uncallable]

/-- The fresh slot every binding needs is the pre-registry one. -/
theorem primitiveFresh_agrees (binding : PrimitiveBinding) (world : World) (brand : Nat) :
    PrimitiveFresh binding world brand ↔ legacyPrimitiveFresh binding world brand := by
  cases binding <;> simp [PrimitiveFresh, legacyPrimitiveFresh, PrimitiveBinding.allocates, PrimitiveBinding.contract,
    PrimitiveDescriptor.ofBool, PrimitiveDescriptor.evidence, Shape.allocates, Shape.uncallable]

/-- The logical evaluator of every binding is the pre-registry one: on every
operand list, the registry entry's match and the frozen row either both match
it, with the same value, or both reject it. -/
theorem evalPrimitive_agrees (env : Environment) (binding : PrimitiveBinding) (values : List Value) :
    evalPrimitive env binding values = legacyEvalPrimitive env binding values := by
  cases binding <;> simp only [evalPrimitive, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
    PrimitiveDescriptor.evidence] <;> unfold legacyEvalPrimitive <;>
    first | rfl | (split <;> first | rfl | (split <;> first | rfl | ((try simp_all); try (rename_i h; apply h <;> rfl))))

/-- The erased evaluator of every binding is the pre-registry one. -/
theorem evalRuntimePrimitive_agrees (binding : PrimitiveBinding) (values : List PrimitiveRuntimeValue) :
    evalRuntimePrimitive binding values = legacyEvalRuntimePrimitive binding values := by
  cases binding <;> simp only [evalRuntimePrimitive, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
    PrimitiveDescriptor.evidence] <;> unfold legacyEvalRuntimePrimitive <;>
    first | rfl | (split <;> first | rfl | (split <;> first | rfl | ((try simp_all); try (rename_i h; apply h <;> rfl))))

/-! ## The derived tables on an enumerated corpus

For every binding, its well-shaped operand list and every mutation of it by
every pool value, plus every list of at most three values from a small pool:
the derived inference, association and role table must equal the pre-registry
ones on all of them, and so must the explanation of every rejected call that
passes inference. The corpus has two markers and an implementation outside
the seeds' domain, so that the marker and domain requirements fail somewhere,
and index lists of every length up to four. -/

private def id (name : String) : DeclId := ⟨⟨⟨"/legacy", "legacy", "1"⟩, []⟩, name⟩
private def scheme : List Parameter := [.object (id "Scheme")]
private def family (parameters : List Parameter) (representation : FamilyRepresentation) : Declaration :=
  .family ⟨parameters, [], representation⟩
private def free (generators : List String) : AlgebraDeclarations.AffineData :=
  { generators, construction := .presented [], base := none, bindings := [], structureImages := [], basis := [],
    cofactors := [] }
private def env : Environment := [
  ⟨id "K", .marker⟩,
  ⟨id "L", .marker⟩,
  ⟨id "Grid", .implementation (id "K") .affineDescriptor [.origin, .dimension]⟩,
  ⟨id "Sparse", .implementation (id "K") .affineDescriptor [.origin, .dimension]⟩,
  ⟨id "Scheme", .classification [] [id "Grid", id "Sparse"]⟩,
  ⟨id "Base", .global (id "Grid")⟩,
  ⟨id "Point", family (scheme ++ scheme) .point⟩,
  ⟨id "Arrow", family (scheme ++ scheme) .morphism⟩,
  ⟨id "Over", family (scheme ++ scheme ++ scheme) .relative⟩,
  ⟨id "Smooth", family (scheme ++ scheme) .smooth⟩,
  ⟨id "Tangent", family scheme (.fiber .tangent)⟩,
  ⟨id "Cotangent", family scheme (.fiber .cotangent)⟩,
  ⟨id "Tape", family (scheme ++ scheme) .tape⟩,
  ⟨id "P", .smoothAffine (id "Grid") []⟩,
  ⟨id "X", .smoothAffine (id "Grid") ["x", "y"]⟩,
  ⟨id "A", .affine (id "Grid") (free ["t"])⟩,
  ⟨id "S", .affine (id "Grid") (free [])⟩,
  ⟨id "F", .affine (id "Grid") { free [] with construction := .fiber (id "A") (id "A") none [], base := some (id "S") }⟩ ]
private def grid : ObjectType := ⟨id "Grid", id "K"⟩
private def x : ObjectRef := .local grid 1
private def y : ObjectRef := .local grid 2
private def z : ObjectRef := .local ⟨id "Grid", id "L"⟩ 3
private def gX : ObjectRef := .global (id "X")
private def gP : ObjectRef := .global (id "P")
private def gA : ObjectRef := .global (id "A")
private def gS : ObjectRef := .global (id "S")
private def refs : List ObjectRef := [x, y, .global (id "Base"), gP, gX, gA, gS, .global (id "F")]
private def shortRefs : List ObjectRef := [x, y, gP, gX, gA]
private def indexLists : List (List Index) :=
  [[], [.natural 3], [.marker (id "K")], [.object x, .marker (id "K")], [.object x, .object y, .object gA, .object gS]] ++
  refs.map (fun ref => [.object ref]) ++
  (shortRefs.flatMap fun a => shortRefs.map fun b => [.object a, .object b]) ++
  (shortRefs.flatMap fun a => shortRefs.flatMap fun b => shortRefs.map fun c => [.object a, .object b, .object c])
private def families : List DeclId :=
  ["Point", "Arrow", "Over", "Smooth", "Tangent", "Cotangent", "Tape", "Missing"].map id
private def scalarPool : List ValueType :=
  [.natural, .integer, .boolean, .integerPair, .object grid x, .object grid (.global (id "Base")),
   .object ⟨id "Scheme", id "K"⟩ y, .object ⟨id "Grid", id "L"⟩ z]
private def pool : List ValueType :=
  scalarPool ++ families.flatMap fun f => indexLists.map fun indices => .indexed ⟨f, indices⟩
private def app (f : String) (indices : List ObjectRef) : ValueType := .indexed ⟨id f, indices.map .object⟩
private def smallPool : List ValueType :=
  scalarPool ++ ["Arrow", "Over", "Smooth", "Tangent"].map (fun f => app f [x, y]) ++
    [app "Tangent" [gX], app "Over" [x, y, gA], app "Smooth" [gP, x]]
private def shortLists : List (List ValueType) :=
  [[]] ++ smallPool.map (fun a => [a]) ++ (smallPool.flatMap fun a => smallPool.map fun b => [a, b]) ++
    (smallPool.flatMap fun a => smallPool.flatMap fun b => smallPool.map fun c => [a, b, c])
/-- The seed and each of its positions replaced by every pool value. -/
private def mutations (seed : List ValueType) : List (List ValueType) :=
  seed :: (List.range seed.length).flatMap fun position => pool.map fun value => seed.set position value
private def seeds : List (PrimitiveBinding × List ValueType) := [
  (.descriptor (id "Grid"), [.natural]),
  (.global (id "Base"), []),
  (.origin grid (id "Point") (id "Base"), [.object grid x]),
  (.identity grid (id "Arrow"), [.object grid x]),
  (.dimension grid, [.object grid x]),
  (.compose (id "Arrow"), [app "Arrow" [y, x], app "Arrow" [x, y]]),
  (.apply (id "Arrow") (id "Point"), [app "Arrow" [x, y], app "Point" [x, gX]]),
  (.relativeConstant ⟨id "Over", [.object gA, .object gA, .object gS]⟩ ⟨1, [], []⟩, []),
  (.relativeCompose (id "Over"), [app "Over" [y, x, gS], app "Over" [x, y, gS]]),
  (.relativeView (id "Over") (id "S") (id "A"), [app "Over" [x, y, gS]]),
  (.relativeEqual (id "Over"), [app "Over" [x, y, gS], app "Over" [x, y, gS]]),
  (.relativeCoefficient (id "Over") (id "A") (id "A") 0 [1], [app "Over" [gA, gA, gS]]),
  (.relativeIntPoint (id "Over") (id "A") (id "S"), [.integer]),
  (.relativePair (id "Over") (id "F"), [app "Over" [x, gA, gS], app "Over" [x, gA, gS]]),
  (.relativeIso (⟨id "Over", []⟩, ⟨0, [], []⟩) (⟨id "Over", []⟩, ⟨0, [], []⟩), []),
  (.relativeCartesian (⟨id "Over", []⟩, ⟨0, [], []⟩) (⟨id "Over", []⟩, ⟨0, [], []⟩) (⟨id "Over", []⟩, ⟨0, [], []⟩)
    (id "F"), []),
  (.smoothConstant ⟨id "Smooth", [.object gX, .object gX]⟩ ⟨2, [], []⟩, []),
  (.smoothCompose (id "Smooth"), [app "Smooth" [y, x], app "Smooth" [x, y]]),
  (.smoothEqual (id "Smooth"), [app "Smooth" [x, y], app "Smooth" [x, y]]),
  (.smoothIntPoint (id "Smooth") (id "X") (id "P"), [.integer, .integer]),
  (.smoothComposite (id "Smooth"), [app "Smooth" [x, y]]),
  (.fiberVector (id "Tangent") (id "Smooth") (id "X"), [app "Smooth" [gP, gX], .integer, .integer]),
  (.fiberAt (id "Tangent") (id "Smooth"), [app "Tangent" [x], app "Smooth" [gP, x]]),
  (.fiberEqual (id "Tangent"), [app "Tangent" [x], app "Tangent" [x]]),
  (.fiberComponent (id "Tangent") (id "X") 0, [app "Tangent" [gX]]),
  (.fiberPairing (id "Cotangent") (id "Tangent"), [app "Cotangent" [x], app "Tangent" [x]]),
  (.cotangentPullback (id "Smooth") (id "Cotangent") .saved, [app "Smooth" [x, y], app "Smooth" [gP, x], app "Cotangent" [y]]),
  (.differential (id "Smooth") (id "Cotangent") (id "X"), [app "Smooth" [x, gX], app "Smooth" [gP, x]]),
  (.linearize (id "Smooth") (id "Tape"), [app "Smooth" [x, y], app "Smooth" [gP, x]]),
  (.cotangentBackward (id "Tape") (id "Cotangent"), [app "Tape" [x, y], app "Cotangent" [y]]),
  (.metricFlat (id "M") (id "X") [] (id "Tangent") (id "Cotangent"), [app "Tangent" [gX]]),
  (.metricSharp (id "M") (id "E") (id "X") [] [] (id "Cotangent") (id "Tangent"), [app "Cotangent" [gX]]) ]
private def allowed : List ObjectRef := [x, y]
private def brand : Nat := 10
private def candidates (binding : PrimitiveBinding) (arguments : List ValueType) : List ValueType :=
  ((inferPrimitiveResult env binding brand arguments).toList ++ (legacyInfer env binding brand arguments).toList ++
    [.natural, .boolean, .integerPair, app "Arrow" [x, y], .object grid (.local grid brand)]).eraseDups
/-- The explanation with the pre-registry role table. -/
private def legacyExplain (binding : PrimitiveBinding) (arguments : List ValueType) (result : ValueType) :
    Option PrimitiveFailure :=
  if validPrimitive env binding allowed brand arguments result then none
  else if !validPrimitiveBinding env binding then some .binding
  else match (legacyRoleTable env binding arguments).find? (!·.holds env) with
    | some requirement => some (.role requirement)
    | none => if validValueType env result then none else some .result
private structure Tally where
  cases : Nat := 0
  explained : Nat := 0
private def compare (tally : Tally) (binding : PrimitiveBinding) (arguments : List ValueType) : IO Tally := do
  let name := reprStr binding
  unless inferPrimitiveResult env binding brand arguments == legacyInfer env binding brand arguments do
    throw (IO.userError s!"inference differs for {name} on {reprStr arguments}")
  unless roleTable env binding arguments == legacyRoleTable env binding arguments do
    throw (IO.userError (s!"the role table differs for {name} on {reprStr arguments}: before " ++
      s!"{reprStr (legacyRoleTable env binding arguments)}, now {reprStr (roleTable env binding arguments)}"))
  let mut tally := { tally with cases := tally.cases + 1 }
  for result in candidates binding arguments do
    unless decide (PrimitiveAssociation env binding allowed brand arguments result) ==
        decide (legacyAssociation env binding allowed brand arguments result) do
      throw (IO.userError s!"association differs for {name} on {reprStr arguments} with result {reprStr result}")
    unless decide (PrimitiveAssociation env binding [x, y, .local grid brand] brand arguments result) ==
        decide (legacyAssociation env binding [x, y, .local grid brand] brand arguments result) do
      throw (IO.userError s!"association differs for {name} on {reprStr arguments} with a used brand")
    if (inferPrimitiveResult env binding brand arguments).isSome then
      let old := legacyExplain binding arguments result
      let new := explainPrimitive env binding allowed brand arguments result
      unless old == new do
        throw (IO.userError (s!"explanation differs for {name} on {reprStr arguments} with result " ++
          s!"{reprStr result}: before {reprStr old}, now {reprStr new}"))
      tally := { tally with explained := tally.explained + 1 }
  pure tally
/-! ### The evaluators on value lists

Every list of at most three values from a pool with one value of each kind,
logical and erased, for every binding of the seeds. -/
private def object (dimension : Nat) : Core.Semantics.Object := ⟨id "Grid", IndexedRuntime.descriptor dimension⟩
private def valuePool : List Value :=
  [.natural 0, .natural 3, .integer 2, .integer (-1), .boolean true, .unit, .pairNat 1 2, .pairInt 1 (-2),
   .object (object 2), .object (object 0), .indexed .token, .indexed (.point ⟨object 2, object 0⟩),
   .indexed (.morphism ⟨object 1, object 2⟩), .indexed (.relative (AlgebraRuntime.Map.intPoint [1, 2])),
   .indexed (.smooth (SmoothRuntime.intPoint [1, 2])), .indexed (.fiber .tangent none),
   .indexed (.fiber .cotangent (SmoothRuntime.vector (SmoothRuntime.intPoint [1]) [3])),
   .indexed (.tape (SmoothRuntime.linearize (SmoothRuntime.intPoint [1]) (SmoothRuntime.intPoint [2]))),
   .package (object 1) [.token]]
private def runtimePool : List PrimitiveRuntimeValue :=
  [.natural 0, .natural 3, .object (IndexedRuntime.descriptor 2), .point ⟨⟨2⟩, ⟨0⟩⟩, .morphism ⟨⟨1⟩, ⟨2⟩⟩,
   .relative (AlgebraRuntime.Map.intPoint [1, 2]), .smooth (SmoothRuntime.intPoint [1, 2]), .fiber none,
   .fiber (SmoothRuntime.vector (SmoothRuntime.intPoint [1]) [3]),
   .tape (SmoothRuntime.linearize (SmoothRuntime.intPoint [1]) (SmoothRuntime.intPoint [2])),
   .boolean true, .integer 2, .integer (-1), .pairInt 1 (-2)]
private def lists {α : Type} (pool : List α) : List (List α) :=
  [[]] ++ pool.map (fun a => [a]) ++ (pool.flatMap fun a => pool.map fun b => [a, b]) ++
    (pool.flatMap fun a => pool.flatMap fun b => pool.map fun c => [a, b, c])
private def compareEvaluators : IO Nat := do
  let mut cases := 0
  for (binding, _) in seeds do
    for values in lists valuePool do
      unless evalPrimitive env binding values == legacyEvalPrimitive env binding values do
        throw (IO.userError s!"the logical evaluator differs for {reprStr binding} on {reprStr values}")
      cases := cases + 1
    for values in lists runtimePool do
      unless evalRuntimePrimitive binding values == legacyEvalRuntimePrimitive binding values do
        throw (IO.userError s!"the erased evaluator differs for {reprStr binding} on {reprStr values}")
      cases := cases + 1
  pure cases
private def run : IO Unit := do
  let mut tally : Tally := {}
  for (binding, seed) in seeds do
    for arguments in mutations seed ++ shortLists do
      tally ← compare tally binding arguments
  let evaluated ← compareEvaluators
  IO.println (s!"legacy tables: {tally.cases} operand lists agree on inference, association and the role " ++
    s!"table; {tally.explained} explanations agree; {evaluated} value lists agree on both evaluators")
#eval run

end VastitasKernel.Indexed.PrimitiveLegacyRegression
