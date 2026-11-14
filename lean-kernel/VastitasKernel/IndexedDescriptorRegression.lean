import Lean.Elab.Command
import VastitasKernel.IndexedDescriptorExample
import VastitasKernel.IndexedSourceDiagnostics
import VastitasKernel.IndexedSemantics
import VastitasKernel.IndexedCodegen
import VastitasKernel.IndexedDeclarationProtocol
import VastitasKernel.IndexedSourceChecker

set_option autoImplicit false

/-! A primitive outside the registry on the derived tables (#622).

`directionalDerivative`, a hypothetical primitive, is one
`PrimitiveDescriptor` value outside `PrimitiveBinding.contract`; it and its
wire form are defined in `IndexedDescriptorExample`, which holds no check.
Every derivation the kernel reads from a descriptor runs on it below: the
validity contract and the agreement of its two forms, result inference, the
association decision, the role table of a rejected call and its soundness,
the argument hints, both evaluators on concrete values, their erasure, the
operand count, whether a call allocates, the lowering of a call and its arity
error, and the literals a module shares. The oracle proves its `Sound`
instance in `VastitasOracle.IndexedDescriptorDemo`.

The wire form is a `PrimitiveFamily` value, `directionalDerivativeFamily`,
also outside the registry (`families`). The parts of the decoder and the
resolver that take a family or its fields as a parameter run on it:
`Wire.familyPrimitive` (the admitted field set, the wire order, the kinds and
the messages of a near miss), `Wire.wireArgument`,
`PrimitiveFamily.fieldNames`, `PrimitiveFamily.resolutionOrder` and
`Source.resolveArgument`. The parts that look the op up in `families` do not
take a family value, so they reject the demo's op, as they must for an op the
registry does not hold: `primitiveFamily?`, `Wire.primitive`,
`Wire.algebraicPrimitive` and `Source.resolvePrimitive`; the list
`algebraicOperations` below, derived from `families`, does not hold it. The
field and kind comparison and the resolution loop of `resolvePrimitive` are
inline in its body, after that lookup; the regression runs the same comparison
and the same order on the demo's decoded form. `PrimitiveFamily.build` returns
a `PrimitiveBinding`, a closed inductive with no constructor for the demo, so
the demo family's `build` rejects every argument list; `buildDescriptor` is
the same step with the descriptor as its result. The Rust table
(`src/primitive_table.rs`) is generated from `families`, and the frontend
builds its primitives through that table, so neither holds the demo's op.
For every family of the registry, the regression also checks that
`resolveFirst` is duplicate-free and names only fields of the family.
These are executable regressions, not proofs, except where a theorem is
stated. -/
namespace VastitasKernel.Indexed.DescriptorRegression
open VastitasKernel.Indexed.Core.Semantics (Value PrimitiveRuntimeValue erasePrimitiveValue)
open VastitasKernel.Indexed.Source.Diagnostics (RoleRequirement)

/-! ## The generic facts, instantiated at the descriptor -/

/-- The checker's verdict gives the proofs' contract, by the descriptor's own
agreement proof: here, the dimension of the line. -/
theorem line_of_valid {env : Environment} {smooth tangent line : DeclId}
    (valid : (directionalDerivative smooth tangent line).validBool env = true) :
    smoothDimension? env line = some 1 :=
  have contract : isSmoothFamily env smooth = true ∧ smoothDimension? env line = some 1 ∧
      fiberVariance? env tangent = some .tangent :=
    ((directionalDerivative smooth tangent line).valid_iff env).mp valid
  contract.2.1

/-- The demo's role table reports only genuine failures of its association:
the kernel's `Shape.roles_sound` at the demo's shape. -/
theorem directionalDerivative_roles_sound {env : Environment} {smooth tangent line : DeclId}
    {allowed : List ObjectRef} {brand : Nat} {operands : List ValueType} {result : ValueType}
    (association : Shape.Association env (directionalDerivative smooth tangent line).shape allowed brand
      operands result) :
    ∀ requirement ∈ Shape.roles env (directionalDerivative smooth tangent line).shape operands,
      requirement.holds env = true :=
  Shape.roles_sound association

/-- A call of the demo allocates nothing: its result is not a fresh object. -/
theorem directionalDerivative_pure (smooth tangent line : DeclId) :
    (directionalDerivative smooth tangent line).shape.allocates = false := rfl

/-- No operand of the demo takes a hint for an integer literal: the shape has
no natural operand and no integer tail, so `Shape.argumentHint`, the
derivation the body checkers read through `PrimitiveBinding.argumentHint`,
gives none at every position. -/
theorem directionalDerivative_hints (smooth tangent line : DeclId) (position : Nat) :
    (directionalDerivative smooth tangent line).shape.argumentHint position = none := by
  match position with
  | 0 | 1 | 2 => rfl
  | _ + 3 => rfl

/-! ## An environment and a call -/

private def id (name : String) : DeclId := ⟨⟨⟨"/descriptor", "descriptor", "1"⟩, []⟩, name⟩
private def affine : DeclId := id "CInfAffine"
private def env : Environment := [
  ⟨id "CInfReal", .marker⟩,
  ⟨id "SmoothR", .implementation (id "CInfReal") .smoothAffine []⟩,
  ⟨affine, .classification [] [id "SmoothR"]⟩,
  ⟨id "Smooth", .family ⟨[.object affine, .object affine], [.canonical 0, .canonical 1], .smooth⟩⟩,
  ⟨id "Tangent", .family ⟨[.object affine], [.canonical 0], .fiber .tangent⟩⟩,
  ⟨id "Cotangent", .family ⟨[.object affine], [.canonical 0], .fiber .cotangent⟩⟩,
  ⟨id "Pt", .smoothAffine (id "SmoothR") []⟩,
  ⟨id "Line", .smoothAffine (id "SmoothR") ["t"]⟩,
  ⟨id "Plane", .smoothAffine (id "SmoothR") ["x", "y"]⟩ ]

/-- The descriptor a binding `directional_derivative(Smooth, Tangent, Line)` would carry. -/
private def demo : PrimitiveDescriptor := directionalDerivative (id "Smooth") (id "Tangent") (id "Line")

private def obj (name : String) : Index := .object (.global (id name))
private def smoothType (x y : String) : ValueType := .indexed ⟨id "Smooth", [obj x, obj y]⟩
private def fiberType (family x : String) : ValueType := .indexed ⟨id family, [obj x]⟩
/-- A function `Plane → Line`, a point of the plane and a vector on the plane. -/
private def operands : List ValueType :=
  [smoothType "Plane" "Line", smoothType "Pt" "Plane", fiberType "Tangent" "Plane"]

private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"indexed descriptor regression failed: {name}")
private def checkEq {α : Type} [BEq α] [Repr α] (name : String) (actual expected : α) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"indexed descriptor regression failed: {name}: {repr actual} is not {repr expected}")

#eval check "finite environment" (validEnvironment env)
#eval check "the smooth objects have their dimensions"
  (smoothDimension? env (id "Pt") == some 0 && smoothDimension? env (id "Line") == some 1 &&
    smoothDimension? env (id "Plane") == some 2)

/-! ## Validity -/

#eval check "the binding contract holds" (demo.validBool env)
#eval check "a 2-dimensional line fails the contract"
  (!(directionalDerivative (id "Smooth") (id "Tangent") (id "Plane")).validBool env)
#eval check "a cotangent family in the vector slot fails the contract"
  (!(directionalDerivative (id "Smooth") (id "Cotangent") (id "Line")).validBool env)
#eval check "a fiber family is not a smooth family"
  (!(directionalDerivative (id "Tangent") (id "Tangent") (id "Line")).validBool env)
#eval check "the operand types and the result type are valid"
  (operands.all (validValueType env) && validValueType env .integerPair)

/-! ## Result inference and the association -/

#eval checkEq "inference gives the integer pair" (Shape.infer env demo.shape 0 operands) (some .integerPair)
#eval checkEq "inference is loose: a wrong family reaches the association"
  (Shape.infer env demo.shape 0 [smoothType "Plane" "Line", smoothType "Pt" "Plane", fiberType "Cotangent" "Plane"])
  (some .integerPair)
#eval checkEq "a wrong operand kind is a shape mismatch"
  (Shape.infer env demo.shape 0 [.natural, smoothType "Pt" "Plane", fiberType "Tangent" "Plane"]) none
#eval checkEq "a missing operand is a shape mismatch"
  (Shape.infer env demo.shape 0 [smoothType "Plane" "Line", smoothType "Pt" "Plane"]) none

private def associates (arguments : List ValueType) (result : ValueType) : Bool :=
  decide (Shape.Association env demo.shape [] 0 arguments result)

#eval check "the association accepts the call" (associates operands .integerPair)
#eval check "a forged result type is rejected" (!associates operands .boolean)
#eval check "a point of the wrong object is rejected"
  (!associates [smoothType "Plane" "Line", smoothType "Pt" "Line", fiberType "Tangent" "Plane"] .integerPair)
#eval check "a vector over the wrong object is rejected"
  (!associates [smoothType "Plane" "Line", smoothType "Pt" "Plane", fiberType "Tangent" "Line"] .integerPair)
#eval check "a function into the plane is rejected"
  (!associates [smoothType "Plane" "Plane", smoothType "Pt" "Plane", fiberType "Tangent" "Plane"] .integerPair)
#eval check "a point from a 1-dimensional object is rejected"
  (!associates [smoothType "Plane" "Line", smoothType "Line" "Plane", fiberType "Tangent" "Plane"] .integerPair)
#eval check "a covector in the vector slot is rejected"
  (!associates [smoothType "Plane" "Line", smoothType "Pt" "Plane", fiberType "Cotangent" "Plane"] .integerPair)
#eval check "three operands and no tail" (Shape.arity env demo.shape == 3)
#eval check "the call does not allocate" (!demo.shape.allocates)
#eval checkEq "no position has an argument hint" ((List.range 5).map demo.shape.argumentHint)
  (List.replicate 5 none)

/-! ## The role table of a rejected call -/

private def wrongObject : List ValueType :=
  [smoothType "Plane" "Line", smoothType "Pt" "Plane", fiberType "Tangent" "Line"]

#eval checkEq "the role table of a vector over the wrong object: families, the fixed line, the relations"
  (Shape.roles env demo.shape wrongObject)
  [.family "function" (id "Smooth") (id "Smooth"), .family "point" (id "Smooth") (id "Smooth"),
    .family "vector" (id "Tangent") (id "Tangent"),
    .object "function" "target" (.global (id "Line")) (.global (id "Line")) "the primitive's declared line",
    .object "point" "target" (.global (id "Plane")) (.global (id "Plane")) "the function's source",
    .object "vector" "object" (.global (id "Plane")) (.global (id "Line")) "the function's source"]
#eval checkEq "the failing requirement names the vector's object"
  ((Shape.roles env demo.shape wrongObject).find? (!·.holds env))
  (some (.object "vector" "object" (.global (id "Plane")) (.global (id "Line")) "the function's source"))
#eval checkEq "a covector in the vector slot fails its family requirement"
  ((Shape.roles env demo.shape
    [smoothType "Plane" "Line", smoothType "Pt" "Plane", fiberType "Cotangent" "Plane"]).find? (!·.holds env))
  (some (.family "vector" (id "Tangent") (id "Cotangent")))
#eval checkEq "an accepted call fails no requirement"
  ((Shape.roles env demo.shape operands).find? (!·.holds env)) none

/-! ## The evaluators and their erasure

`f(x, y) = x² + y`, `p = (1, 2)` and `v = (3, 4)` at `p`: `df_p = (2, 1)`, so
`⟨df_p, v⟩ = 10`. -/

open AlgebraRuntime in
private def f : SmoothRuntime.Program :=
  .primitive ⟨2, [], [Poly.add (Poly.pow 2 (Poly.var 2 0) 2) (Poly.var 2 1)]⟩
private def p : SmoothRuntime.Program := SmoothRuntime.intPoint [1, 2]
private def v : SmoothRuntime.FiberValue := SmoothRuntime.vector p [3, 4]
private def values : List Value := [.indexed (.smooth f), .indexed (.smooth p), .indexed (.fiber .tangent v)]
private def erased : List PrimitiveRuntimeValue := [.smooth f, .smooth p, .fiber v]

#eval check "the operand values are typed: a map of the plane to the line, a point of the plane, two components"
  (f.wellTyped 2 1 && p.wellTyped 0 2 && v.map (·.components.length) == some 2)
#eval checkEq "the differential of x² + y at (1, 2) is (2, 1)"
  (SmoothRuntime.differential f p) (some ⟨[1, 2], [2, 1]⟩)
#eval checkEq "the logical evaluator pairs the differential with the vector" (demo.eval env values)
  (some (.pairInt 10 1))
#eval checkEq "the erased evaluator agrees on the erased operands" (demo.evalRuntime erased) (some (.pairInt 10 1))
#eval checkEq "the operand values erase to the erased operands" (values.mapM erasePrimitiveValue) (some erased)
#eval checkEq "the result erases to the erased result" (erasePrimitiveValue (.pairInt 10 1)) (some (.pairInt 10 1))
#eval checkEq "a vector at another point pairs to the failure value"
  (demo.eval env [.indexed (.smooth f), .indexed (.smooth p),
    .indexed (.fiber .tangent (SmoothRuntime.vector (SmoothRuntime.intPoint [0, 0]) [3, 4]))])
  (some (.pairInt 0 0))
#eval checkEq "the evaluators reject any other operand list"
  (demo.eval env [.indexed (.smooth f), .indexed (.smooth p)], demo.evalRuntime [.smooth f, .fiber v, .smooth p])
  (none, none)

/-! ## Lowering

The lowering writes the erased evaluator's expression, the pairing of the
differential with the vector. It is the text a generated program holds for
`fiber_pairing(differential(f, p), v)`, the two registry calls that the demo
replaces, read here from their registry entries through
`Codegen.renderPrimitive`. `Codegen.renderPrimitive` and
`Codegen.renderContext` take a `PrimitiveBinding` and the module's
declarations, so the demo's lowering is its own `render` field, called
directly, and its literals go through `PrimitiveDescriptor.sharedLiterals`,
which takes the entries themselves. -/

/-- An `Except` as a pair of options, to compare with `==`. -/
private def outcome {α : Type} : Except String α → Option String × Option α
  | .error message => (some message, none)
  | .ok value => (none, some value)
/-- The message of a failed decoding or lowering. -/
private def failure? {α : Type} : Except String α → Option String
  | .error message => some message
  | .ok _ => none

private def noLiterals : RenderContext := .share []
private def callText : String :=
  "(VastitasKernel.SmoothRuntime.pairing (VastitasKernel.SmoothRuntime.differential v_0 v_1) v_2)"

#eval checkEq "the lowering of a call" (outcome (demo.render noLiterals ["v_0", "v_1", "v_2"])) (none, some callText)
#eval checkEq "the lowering is that of the two registry calls it replaces"
  (outcome (demo.render noLiterals ["v_0", "v_1", "v_2"]))
  (outcome do
    let covector ← Core.Codegen.renderPrimitive noLiterals (.differential (id "Smooth") (id "Cotangent") (id "Line"))
      ["v_0", "v_1"]
    Core.Codegen.renderPrimitive noLiterals (.fiberPairing (id "Cotangent") (id "Tangent")) [covector, "v_2"])
#eval checkEq "two operands are the arity error" (outcome (demo.render noLiterals ["v_0", "v_1"]))
  (some "closed primitive arity mismatch", none)
#eval checkEq "four operands are the arity error" (outcome (demo.render noLiterals ["v_0", "v_1", "v_2", "v_3"]))
  (some "closed primitive arity mismatch", none)
#eval check "the arity error is the registry's"
  (outcome (demo.render noLiterals []) == outcome Lowering.arityMismatch)

/-- The basis of a relative constant on the plane. -/
private def planeBasis : List AlgebraRuntime.Poly := [AlgebraRuntime.Poly.var 2 0, AlgebraRuntime.Poly.var 2 1]
/-- A map over that basis. -/
private def planeMap : AlgebraRuntime.Map := ⟨2, planeBasis, [AlgebraRuntime.Poly.var 2 0]⟩
/-- A relative constant, whose registry entry shares its basis and its map. -/
private def relativeConstant : PrimitiveDescriptor :=
  (PrimitiveBinding.relativeConstant ⟨id "Over", []⟩ planeMap).contract
/-- A smooth constant with the same map, whose registry entry shares the map. -/
private def smoothConstant : PrimitiveDescriptor :=
  (PrimitiveBinding.smoothConstant ⟨id "Smooth", []⟩ planeMap).contract
private def gram : SmoothRuntime.Matrix := [[2, 1], [1, 1]]
private def inverse : SmoothRuntime.Matrix := [[1, -1], [-1, 2]]
/-- `flat` shares the Gram matrix of its metric, `sharp` the certified inverse. -/
private def flat : PrimitiveDescriptor :=
  (PrimitiveBinding.metricFlat (id "Skew") (id "Plane") gram (id "Tangent") (id "Cotangent")).contract
private def sharp : PrimitiveDescriptor :=
  (PrimitiveBinding.metricSharp (id "Skew") (id "Invertible") (id "Plane") gram inverse (id "Cotangent")
    (id "Tangent")).contract

#eval checkEq "the demo shares no literal" (PrimitiveDescriptor.sharedLiterals [demo]) []
#eval checkEq "a relative constant shares its basis and its map" (PrimitiveDescriptor.sharedLiterals [relativeConstant])
  [.basis planeBasis, .map planeMap]
#eval checkEq "a smooth constant shares its map, flat the Gram matrix and sharp the inverse"
  (PrimitiveDescriptor.sharedLiterals [smoothConstant, flat, sharp]) [.map planeMap, .matrix gram, .matrix inverse]
#eval checkEq "equal literals of several entries are shared once"
  (PrimitiveDescriptor.sharedLiterals [relativeConstant, flat, smoothConstant, sharp, flat, relativeConstant])
  [.basis planeBasis, .map planeMap, .matrix gram, .matrix inverse]
#eval checkEq "the demo leaves the literals a module shares as they are"
  (PrimitiveDescriptor.sharedLiterals [demo, relativeConstant, demo])
  (PrimitiveDescriptor.sharedLiterals [relativeConstant])
#eval checkEq "the lowering reads no shared literal"
  (outcome (demo.render (.share [.basis planeBasis]) ["v_0", "v_1", "v_2"])) (none, some callText)

/-! A call names a literal that the module shares, by its kind and its
position among the shared literals of that kind, and writes any other literal
in place. A map in place names its basis when the module shares the basis. -/

private def shared : RenderContext := .share [.basis planeBasis, .matrix inverse, .map planeMap, .matrix gram]
private def mapText (basis : String) : String :=
  s!"(VastitasKernel.AlgebraRuntime.Map.mk 2 {basis} {Lowering.renderPolys planeMap.images})"
private def matrixText (rows : String) : String := s!"([{rows}] : VastitasKernel.SmoothRuntime.Matrix)"
private def inverseText : String :=
  matrixText "[(mkRat (1 : Int) 1), (mkRat (-1 : Int) 1)], [(mkRat (-1 : Int) 1), (mkRat (2 : Int) 1)]"

#eval checkEq "the names of shared literals"
  (shared.literals.map shared.name?) [some "basis_0", some "matrix_0", some "map_0", some "matrix_1"]
#eval checkEq "a literal that the module does not share has no name" (noLiterals.name? (.matrix gram)) none
#eval checkEq "calls name the shared literals"
  ([relativeConstant.render shared [], smoothConstant.render shared [], flat.render shared ["v_0"],
    sharp.render shared ["v_0"]].map outcome)
  ([.ok "map_0", .ok "(VastitasKernel.SmoothRuntime.Program.primitive map_0)",
    .ok "(VastitasKernel.SmoothRuntime.flat matrix_1 v_0)",
    .ok "(VastitasKernel.SmoothRuntime.sharp matrix_0 v_0)"].map outcome)
#eval checkEq "a map that the module does not share is written in place and names its shared basis"
  (outcome (relativeConstant.render (.share [.basis planeBasis]) [])) (none, some (mapText "basis_0"))
#eval checkEq "without shared literals every literal is written in place"
  ([relativeConstant.render noLiterals [], sharp.render noLiterals ["v_0"]].map outcome)
  ([.ok (mapText (Lowering.renderPolys planeBasis)),
    .ok s!"(VastitasKernel.SmoothRuntime.sharp {inverseText} v_0)"].map outcome)
#eval checkEq "the module declares a shared literal with its type and its value in place"
  (shared.literals.map fun literal => (Lowering.literalType literal, Lowering.literalValue shared literal))
  [("List VastitasKernel.AlgebraRuntime.Poly", Lowering.renderPolys planeBasis),
    ("VastitasKernel.SmoothRuntime.Matrix", inverseText),
    ("VastitasKernel.AlgebraRuntime.Map", mapText "basis_0"),
    ("VastitasKernel.SmoothRuntime.Matrix",
      matrixText "[(mkRat (2 : Int) 1), (mkRat (1 : Int) 1)], [(mkRat (1 : Int) 1), (mkRat (1 : Int) 1)]")]

/-! A backward step along a declared map shares the Jacobian table of the
map. Its entry lists the map. The context computes the table once per map and
gives the maps with one table one name. -/

/-- `t ↦ t²` and `t ↦ t² + 1`, which have one Jacobian table, and `t ↦ t³`. -/
private def square : AlgebraRuntime.Map := ⟨1, [], [[⟨[2], 1⟩]]⟩
private def shiftedSquare : AlgebraRuntime.Map := ⟨1, [], [[⟨[2], 1⟩, ⟨[0], 1⟩]]⟩
private def cube : AlgebraRuntime.Map := ⟨1, [], [[⟨[3], 1⟩]]⟩
/-- The backward step along a map of the line to itself. -/
private def step (map : AlgebraRuntime.Map) : PrimitiveDescriptor :=
  (PrimitiveBinding.cotangentJacobian (id "Cotangent")
    ⟨id "Smooth", [.object (.global (id "Line")), .object (.global (id "Line"))]⟩ map).contract
private def tables : RenderContext :=
  .share [.jacobian square, .matrix gram, .jacobian shiftedSquare, .jacobian cube]
/-- The table of one column and one entry `coefficient · t ^ exponent`. -/
private def tableText (coefficient exponent : Nat) : String :=
  s!"([([([(VastitasKernel.AlgebraRuntime.Term.mk [{exponent}] (mkRat ({coefficient} : Int) 1))] : " ++
    "VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly)] : " ++
    "List (List VastitasKernel.AlgebraRuntime.Poly))"
private def stepText (table : String) : String := s!"(VastitasKernel.SmoothRuntime.jacobianStep 1 {table} v_0 v_1 v_2)"

#eval checkEq "a backward step shares the Jacobian table of its map and lists the map"
  (PrimitiveDescriptor.sharedLiterals [step square, step shiftedSquare, step square])
  [.jacobian square, .jacobian shiftedSquare]
#eval checkEq "the context keeps one literal for two maps with one table"
  tables.literals [.jacobian square, .matrix gram, .jacobian cube]
#eval checkEq "the context holds the table of each listed map"
  tables.jacobians [(square, [[[⟨[1], 2⟩]]]), (shiftedSquare, [[[⟨[1], 2⟩]]]), (cube, [[[⟨[2], 3⟩]]])]
#eval checkEq "two maps with one table have one name"
  ([square, shiftedSquare, cube].map fun map => tables.name? (.jacobian map))
  [some "jacobian_0", some "jacobian_0", some "jacobian_1"]
#eval checkEq "a step names the table that the module shares"
  ([square, shiftedSquare, cube].map fun map => outcome ((step map).render tables ["v_0", "v_1", "v_2"]))
  (["jacobian_0", "jacobian_0", "jacobian_1"].map fun name => (none, some (stepText name)))
#eval checkEq "a step whose table the module does not share writes it in place"
  (outcome ((step square).render noLiterals ["v_0", "v_1", "v_2"])) (none, some (stepText (tableText 2 1)))
#eval checkEq "the module declares a table with its type and its value in place"
  ([square, cube].map fun map => (Lowering.literalType (.jacobian map), Lowering.literalValue tables (.jacobian map)))
  [("List (List VastitasKernel.AlgebraRuntime.Poly)", tableText 2 1),
    ("List (List VastitasKernel.AlgebraRuntime.Poly)", tableText 3 2)]

/-! The lowered text elaborates as the body of a generated function whose
parameters and result have the types that `renderType` in `IndexedCodegen`
writes for a smooth map and a point (`SmoothRuntime.Program`), a fiber
(`Option SmoothRuntime.Fiber`) and an integer pair (`Prod Int Int`), and that
function computes the erased evaluator's result. The command below elaborates
the text that `render` returns, not a copy of it. The parameter types are
copied from `renderType`, which is private, so a change to the types it
writes does not reach this check. -/

open Lean Elab Command in
run_cmd do
  let .ok text := demo.render noLiterals ["v_0", "v_1", "v_2"]
    | throwError "indexed descriptor regression failed: the lowering of a call"
  let source := s!"def loweredCall (v_0 v_1 : {Lowering.smooth "Program"}) " ++
    s!"(v_2 : (Option {Lowering.smooth "Fiber"})) : (Prod Int Int) :=\n  {text}"
  match Parser.runParserCategory (← getEnv) `command source with
  | .ok command => elabCommand command
  | .error message => throwError "indexed descriptor regression failed: {message}"

#eval checkEq "the lowered call computes the erased evaluator's result" (loweredCall f p v) (10, 1)

/-! ## Wire form

`directional_derivative` takes the paths of its smooth family, its tangent
family and its line, as `differential` takes `map_family`, `cotangent` and
`line`; `directionalDerivativeFamily` and `buildDescriptor` are defined in
`IndexedDescriptorExample`. -/

private def spanJson (n : Nat) : Lean.Json := Lean.Json.mkObj [("start", Lean.toJson (10 * n)),
  ("end", Lean.toJson (10 * n + 5)), ("line", Lean.toJson (1 : Nat)), ("column", Lean.toJson (n + 1))]
private def pathJson (name : String) (n : Nat) : Lean.Json :=
  Lean.Json.mkObj [("path", Lean.toJson [name]), ("span", spanJson n)]
/-- The form the frontend would send, one span per path. -/
private def wireJson : Lean.Json := Lean.Json.mkObj [("op", Lean.toJson "directional_derivative"),
  ("map_family", pathJson "Smooth" 1), ("tangent", pathJson "Tangent" 2), ("line", pathJson "Line" 3)]
private def withField (j : Lean.Json) (key : String) (value : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj ((key, value) :: ((j.getObj?.toOption.getD {}).toArray.toList.filter (·.1 != key)))
private def without (j : Lean.Json) (key : String) : Lean.Json :=
  Lean.Json.mkObj ((j.getObj?.toOption.getD {}).toArray.toList.filter (·.1 != key))

/-- The generic decoder, on the demo family. -/
private def decode (j : Lean.Json) : Except String Source.Primitive := Wire.familyPrimitive j directionalDerivativeFamily
private def names (primitive : Source.Primitive) : List String := primitive.arguments.map (·.1)
private def kinds (primitive : Source.Primitive) : List Source.WireKind := primitive.arguments.map (·.2.kind)

#eval checkEq "the decoder gives the demo's op" ((decode wireJson).toOption.map (·.op)) (some "directional_derivative")
#eval checkEq "the decoder gives the family's fields in wire order" ((decode wireJson).toOption.map names)
  (some directionalDerivativeFamily.fieldNames)
#eval checkEq "each field has the family's kind" ((decode wireJson).toOption.map kinds)
  (some [.path, .path, .path])
#eval checkEq "the wire order is the family's, not the object's: reversed fields decode reversed"
  ((Wire.familyPrimitive wireJson { directionalDerivativeFamily with
    fields := directionalDerivativeFamily.fields.reverse }).toOption.map names)
  (some ["line", "tangent", "map_family"])
#eval checkEq "the decoded paths are the object's" ((decode wireJson).toOption.map fun primitive =>
    primitive.arguments.map fun | (_, .path path) => path.path | _ => [])
  (some [["Smooth"], ["Tangent"], ["Line"]])

/-! A near miss of the wire form: the decoder admits exactly `op` and the
family's fields, and decodes each by its kind. -/

#eval checkEq "a dropped field" (failure? (decode (without wireJson "line"))) (some "property not found: line")
#eval checkEq "a field of `differential`" (failure? (decode (withField wireJson "cotangent" (pathJson "Cotangent" 4))))
  (some "unknown protocol field 'cotangent'")
#eval checkEq "a forged owner" (failure? (decode (withField wireJson "owner" (Lean.toJson "forged"))))
  (some "unknown protocol field 'owner'")
#eval checkEq "the field set is checked before any field is decoded"
  (failure? (decode (withField (without wireJson "line") "cotangent" (pathJson "Cotangent" 4))))
  (some "unknown protocol field 'cotangent'")
#eval checkEq "a string in a path field" (failure? (decode (withField wireJson "line" (Lean.toJson "Line"))))
  (some "object expected")
#eval checkEq "a path without its span"
  (failure? (decode (withField wireJson "line" (Lean.Json.mkObj [("path", Lean.toJson ["Line"])]))))
  (some "property not found: span")
#eval checkEq "an empty path"
  (failure? (decode (withField wireJson "tangent" (Lean.Json.mkObj [("path", Lean.toJson ([] : List String)),
    ("span", spanJson 2)]))))
  (some "indexed reference requires a nonempty path")

/-! The entry points that look the op up in `families` do not know it: the
registry holds no test primitive, and neither the trusted decoder nor the
Rust table generated from `families` admits it. -/

/-- The ops that only protocol 9 admits (the Stage 2 relative and Stage 3
smooth, fiber, tape and metric primitive contracts), derived from `families`:
the op of each family with `algebraic` set. The decoder does not read this
list. -/
private def algebraicOperations : List String :=
  (families.filter (·.algebraic)).map (·.op)

#eval check "no family of the registry has the demo's op"
  ((primitiveFamily? directionalDerivativeFamily.op).isNone &&
    families.all (·.op != directionalDerivativeFamily.op) &&
    !algebraicOperations.contains directionalDerivativeFamily.op)
#eval checkEq "the trusted decoder rejects the demo's op in protocol 9"
  (failure? (Wire.primitive wireJson (algebraic := true))) (some "unknown indexed primitive contract")
#eval checkEq "and before protocol 9" (failure? (Wire.primitive wireJson)) (some "unknown indexed primitive contract")
#eval checkEq "and as an algebraic op" (failure? (Wire.algebraicPrimitive wireJson directionalDerivativeFamily.op))
  (some "unknown indexed primitive contract")

/-! ## Resolution

A package whose declarations are markers named like the environment's
declarations, in the environment's package and module, so that a resolved
path is the environment's identity. -/

private def pkg : Namespace.PackageId := (id "Smooth").scope.package
private def program : Source.Program := {
  file := "descriptor-regression", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := { path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {} },
    declarations := ["Smooth", "Tangent", "Cotangent", "Line"].map fun name => ⟨name, .marker, true, {}⟩ }], none⟩] }
private def index : Namespace.Indexed := program.indexed
private def scope : Namespace.Scope := ⟨pkg, []⟩

/-- The comparison `Source.resolvePrimitive` makes before it resolves a name:
the decoded arguments are the family's fields, names and kinds, in wire order. -/
private def isWireForm (primitive : Source.Primitive) : Bool :=
  primitive.arguments.map (fun (name, argument) => (name, argument.kind)) ==
    directionalDerivativeFamily.fields.map fun field => (field.name, field.kind)

/-- Each argument resolved by `Source.resolveArgument`, in the family's
resolution order; with nothing resolved first, that is the wire order. -/
private def resolveDemo (primitive : Source.Primitive) : Source.ResolveM (List ResolvedArgument) :=
  (directionalDerivativeFamily.resolutionOrder.filterMap (primitive.arguments.lookup ·)).mapM
    (Source.resolveArgument index scope)

private def declaration? : ResolvedArgument → Option DeclId
  | .declaration id => some id
  | _ => none

#eval check "nothing is resolved first, so the resolution order is the wire order"
  (directionalDerivativeFamily.resolutionOrder == directionalDerivativeFamily.fieldNames)

/-- A family resolves each of its fields once: `resolveFirst` is duplicate-free
and names only fields of the family, so the resolution order is a permutation
of the field names. `resolvePrimitive` skips a name in `resolveFirst` that is
not a field, and resolves a repeated one twice. -/
private def resolvesEachFieldOnce (family : PrimitiveFamily) : Bool :=
  decide family.resolveFirst.Nodup && family.resolveFirst.all (family.fieldNames.contains ·) &&
    family.resolutionOrder.isPerm family.fieldNames

#eval check "every family of the registry, and the demo's, resolves each of its fields once"
  (families.all resolvesEachFieldOnce && resolvesEachFieldOnce directionalDerivativeFamily)
#eval check "a misspelt or a repeated name in `resolveFirst` fails that check"
  ((primitiveFamily? "flat").map (fun family => resolvesEachFieldOnce { family with resolveFirst := ["metrc"] }) ==
      some false &&
    (primitiveFamily? "sharp").map (fun family =>
      resolvesEachFieldOnce { family with resolveFirst := ["metric", "evidence", "metric"] }) == some false)

#eval check "the decoded form passes the comparison" ((decode wireJson).toOption.map isWireForm == some true)
#eval check "a form with its fields in another order fails it"
  ((decode wireJson).toOption.map (fun primitive => isWireForm { primitive with
    arguments := primitive.arguments.reverse }) == some false)
#eval check "a form with a coordinate in a path field fails it"
  ((decode wireJson).toOption.map (fun primitive => isWireForm { primitive with
    arguments := primitive.arguments.map fun (name, argument) =>
      (name, if name == "line" then .coordinate "t" else argument) }) == some false)

#eval checkEq "the arguments resolve to the environment's declarations, in wire order"
  (match decode wireJson with
    | .ok primitive => match (resolveDemo primitive).run [] with
      | .ok (arguments, _) => some (arguments.map declaration?)
      | .error _ => none
    | .error _ => none)
  (some [some (id "Smooth"), some (id "Tangent"), some (id "Line")])
#eval checkEq "the references are recorded in resolution order, the last first"
  (match decode wireJson with
    | .ok primitive => match (resolveDemo primitive).run [] with
      | .ok (_, references) => some (references.map (·.path.path))
      | .error _ => none
    | .error _ => none)
  (some [["Line"], ["Tangent"], ["Smooth"]])
#eval checkEq "an unresolvable name is the resolver's diagnostic"
  (match decode (withField wireJson "tangent" (pathJson "Missing" 2)) with
    | .ok primitive => match (resolveDemo primitive).run [] with
      | .ok _ => none
      | .error diagnostic => some (diagnostic.code, diagnostic.message)
    | .error _ => none)
  (some ("E_NAME", "undefined name 'Missing' in this module"))

/-- The descriptor of the resolved wire form: it is the demo, so it is valid
in the environment, and it lowers and evaluates a call as the demo does. -/
private def resolvedDescriptor : Option PrimitiveDescriptor :=
  match decode wireJson with
  | .ok primitive => match (resolveDemo primitive).run [] with
    | .ok (arguments, _) => (buildDescriptor arguments).toOption
    | .error _ => none
  | .error _ => none

#eval check "the resolved wire form builds the demo"
  (match resolvedDescriptor with
    | some descriptor =>
      -- Relations hold functions, so they are compared through the role table
      -- of a rejected call and the association decision, which read them.
      descriptor.shape.operands == demo.shape.operands && descriptor.shape.result == demo.shape.result &&
        descriptor.shape.tail.isNone && descriptor.shape.families == demo.shape.families &&
        Shape.roles env descriptor.shape wrongObject == Shape.roles env demo.shape wrongObject &&
        decide (Shape.Association env descriptor.shape [] 0 operands .integerPair) &&
        !decide (Shape.Association env descriptor.shape [] 0 wrongObject .integerPair) && descriptor.validBool env &&
        outcome (descriptor.render noLiterals ["v_0", "v_1", "v_2"]) == (none, some callText) &&
        descriptor.eval env values == some (.pairInt 10 1)
    | none => false)
#eval checkEq "the family's build has no binding to return"
  (match decode wireJson with
    | .ok primitive => match (resolveDemo primitive).run [] with
      | .ok (arguments, _) => failure? (directionalDerivativeFamily.build arguments)
      | .error _ => none
    | .error _ => none)
  (some "`directional_derivative` has no `PrimitiveBinding` constructor")
#eval checkEq "and reports other arguments as a registry family does"
  (failure? (directionalDerivativeFamily.build [.declaration (id "Smooth")]))
  (some "the arguments of `directional_derivative` do not match its wire fields")
#eval checkEq "the trusted resolver rejects the demo's op before resolving a name"
  (match decode wireJson with
    | .ok primitive => match (Source.resolvePrimitive index scope primitive).run [] with
      | .ok _ => none
      | .error diagnostic => some (diagnostic.code, diagnostic.message)
    | .error _ => none)
  (some ("E_PROTOCOL", "unknown indexed primitive contract"))

end VastitasKernel.Indexed.DescriptorRegression
