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
hints, the role table, whether a call allocates, the two evaluators
(`evalPrimitive`, `evalRuntimePrimitive`), the lowering of a call
(`IndexedCodegen`) and the literals a generated module shares
(`PrimitiveDescriptor.sharedLiterals`). A binding's wire form comes from its
`PrimitiveFamily` in `IndexedPrimitiveFamilies`, which the decoder, the
resolver and the generated Rust table read; a binding without a family is
built by `resolveBody` or a stage pass.
A proof that unfolds a derived table at one constructor needs no
per-constructor lemma: besides the table's own definition and what evaluates
the entry's fields (the `Shape` matcher for the association, the arm's checks
for validity), its `simp` set names only `PrimitiveBinding.contract` (and
`PrimitiveDescriptor.ofBool` or `PrimitiveDescriptor.evidence`). Each arm names the exact
checks of `Indexed`, `IndexedPrimitiveBinding` and `IndexedSmoothContracts`;
family, base and object IDs are part of the contract, displayed names and
arbitrary certificates are not.

Index fields carry the names the role table reports, the vocabulary of the
pre-registry diagnostics; family declarations name no indices. A point is
`[target, source]`, a morphism, smooth map or tape `[source, target]`, a
relative morphism `[source, target, base]`, a fiber `[object]`. The role table
reports a shape's families once the operands have its index pattern;
`families := .early` keeps the precedence of the two primitives that report
them as soon as the operands are applications.

The evaluators of an entry match the operand pattern of its shape and return
`none` on any other pattern; a variadic entry accepts any number of integer
operands, as the pre-registry tables did, and the checked operand count fixes
it. The logical one builds the values of
`IndexedPrimitiveValues`; the erased one applies the runtime operations that
generated programs link, on erased values. The two agree up to erasure; the
oracle proves it per entry (`VastitasOracle.IndexedPrimitiveSoundness.Sound`).

The lowering of an entry writes the generated Lean text of a call from its
rendered operands, in the vocabulary of `Lowering`, and rejects any other
operand list with the one arity error; a variadic entry (the two integer
points, and the components after a fiber vector's point) renders any number of
operands, as the pre-registry table did, and the checked operand count fixes
it. A relative constant shares its basis:
the module declares each distinct basis once as `basis_k`, and every map over
it, relative or smooth, names it. -/
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
        | _ => none
      render := fun _ args => match args with
        | [dim] => .ok (Lowering.application (Lowering.runtime "descriptor") [dim])
        | _ => Lowering.arityMismatch }
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
        | _ => none
      render := fun _ args => match args with
        | [] => .ok (Lowering.runtime "baseObject")
        | _ => Lowering.arityMismatch }
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
        | _ => none
      render := fun _ args => match args with
        | [object] => .ok (Lowering.application (Lowering.runtime "origin") [object, Lowering.runtime "baseObject"])
        | _ => Lowering.arityMismatch }
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
        | _ => none
      render := fun _ args => match args with
        | [object] => .ok (Lowering.application (Lowering.runtime "identity") [object])
        | _ => Lowering.arityMismatch }
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
        | _ => none
      render := fun _ args => match args with
        | [object] => .ok s!"({object}).dimension"
        | _ => Lowering.arityMismatch }
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
        | _ => none
      render := fun _ args => match args with
        | [after, before] => .ok (Lowering.application (Lowering.runtime "compose") [after, before])
        | _ => Lowering.arityMismatch }
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
        | _ => none
      render := fun _ args => match args with
        | [map, point] => .ok (Lowering.application (Lowering.runtime "apply") [map, point])
        | _ => Lowering.arityMismatch }
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
      (fun ctx args => match args with
        | [] => .ok (Lowering.renderMap ctx affineMap)
        | _ => Lowering.arityMismatch)
      (literals := [affineMap.basis])
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
      (fun _ args => match args with
        | [after, before] => .ok (Lowering.application (Lowering.algebra "Map.compose") [after, before])
        | _ => Lowering.arityMismatch)
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
        | _ => none
      render := fun _ args => match args with
        | [map] => .ok map
        | _ => Lowering.arityMismatch }
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
      (fun _ args => match args with
        | [left, right] => .ok (Lowering.application (Lowering.algebra "Map.same") [left, right])
        | _ => Lowering.arityMismatch)
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
        | _ => none
      render := fun _ args => match args with
        | [map] =>
          .ok (Lowering.application (Lowering.algebra "Map.coefficient") [map, toString coordinate, toString monomial])
        | _ => Lowering.arityMismatch }
  | .relativeIntPoint family object base =>
    { shape :=
        { operands := [], tail := some fun env => affineArity env object,
          result := .constant ⟨family, [.object (.global base), .object (.global object), .object (.global base)]⟩ }
      validProp env := isRelativeFamily env family = true ∧ freeAffine env object = true ∧
        pointBase env base = true
      validBool env := isRelativeFamily env family && freeAffine env object && pointBase env base
      valid_iff env := by simp [Bool.and_eq_true, and_assoc]
      eval := fun _ values => intPointValue values
      evalRuntime := intPointRuntime
      render := fun _ coordinates =>
        .ok (Lowering.application (Lowering.algebra "Map.intPoint") [s!"[{String.intercalate ", " coordinates}]"]) }
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
        | _ => none
      render := fun _ args => match args with
        | [left, right] => .ok (Lowering.application (Lowering.algebra "Map.pair") [left, right])
        | _ => Lowering.arityMismatch }
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
      (fun ctx args => match args with
        | [] => .ok (Lowering.application (Lowering.smooth "Program.primitive") [Lowering.renderMap ctx affineMap])
        | _ => Lowering.arityMismatch)
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
      (fun _ args => match args with
        | [after, before] => .ok (Lowering.application (Lowering.smooth "Program.compose") [after, before])
        | _ => Lowering.arityMismatch)
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
      (fun _ args => match args with
        | [left, right] => .ok (Lowering.application (Lowering.smooth "same") [left, right])
        | _ => Lowering.arityMismatch)
  | .smoothIntPoint family object point =>
    .ofBool
      { operands := [], tail := some fun env => smoothArity env object,
        result := .constant ⟨family, [.object (.global point), .object (.global object)]⟩ }
      (fun env => smoothIntPointValid env family object point)
      (fun _ values => smoothPointValue values)
      smoothPointRuntime
      (fun _ coordinates =>
        .ok (Lowering.application (Lowering.smooth "intPoint") [s!"[{String.intercalate ", " coordinates}]"]))
  | .smoothComposite family =>
    .ofBool { operands := [.application "map" family], result := .application 0 }
      (fun env => isSmoothFamily env family)
      (fun _ values => match values with
        | [.indexed (.smooth program)] => some (.indexed (.smooth (SmoothRuntime.composite program)))
        | _ => none)
      (fun values => match values with
        | [.smooth program] => some (.smooth (SmoothRuntime.composite program))
        | _ => none)
      (fun _ args => match args with
        | [program] => .ok (Lowering.application (Lowering.smooth "composite") [program])
        | _ => Lowering.arityMismatch)
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
      (fun _ args => match args with
        | point :: components =>
          .ok (Lowering.application (Lowering.smooth "vector") [point, s!"[{String.intercalate ", " components}]"])
        | _ => Lowering.arityMismatch)
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
      (fun _ args => match args with
        | [value, point] => .ok (Lowering.application (Lowering.smooth "fiberAt") [value, point])
        | _ => Lowering.arityMismatch)
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
      (fun _ args => match args with
        | [left, right] => .ok (Lowering.application (Lowering.smooth "fiberEqual") [left, right])
        | _ => Lowering.arityMismatch)
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
      (fun _ args => match args with
        | [value] => .ok (Lowering.application (Lowering.smooth "component") [value, toString coordinate])
        | _ => Lowering.arityMismatch)
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
      (fun _ args => match args with
        | [covector, vector] => .ok (Lowering.application (Lowering.smooth "pairing") [covector, vector])
        | _ => Lowering.arityMismatch)
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
      (fun _ args => match args with
        | [map, point, seed] =>
          let mode := match mode with
            | .saved => Lowering.smooth "PullbackMode.saved"
            | .recomputed => Lowering.smooth "PullbackMode.recomputed"
          .ok (Lowering.application (Lowering.smooth "pullback") [mode, map, point, seed])
        | _ => Lowering.arityMismatch)
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
      (fun _ args => match args with
        | [function, point] => .ok (Lowering.application (Lowering.smooth "differential") [function, point])
        | _ => Lowering.arityMismatch)
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
      (fun _ args => match args with
        | [map, point] => .ok (Lowering.application (Lowering.smooth "linearize") [map, point])
        | _ => Lowering.arityMismatch)
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
      (fun _ args => match args with
        | [record, seed] => .ok (Lowering.application (Lowering.smooth "backward") [record, seed])
        | _ => Lowering.arityMismatch)
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
      (fun _ args => match args with
        | [vector] => .ok (Lowering.application (Lowering.smooth "flat") [Lowering.renderMatrix gram, vector])
        | _ => Lowering.arityMismatch)
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
      (fun _ args => match args with
        | [covector] => .ok (Lowering.application (Lowering.smooth "sharp") [Lowering.renderMatrix inverse, covector])
        | _ => Lowering.arityMismatch)

end VastitasKernel.Indexed
