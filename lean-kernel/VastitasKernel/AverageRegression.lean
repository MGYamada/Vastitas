import VastitasKernel.IndexedSourceChecker
import VastitasKernel.IndexedDeclarationProtocol
import VastitasKernel.IndexedCodegen
import VastitasKernel.IndexedSemantics
import VastitasKernel.RegressionSupport

set_option autoImplicit false

/-! The dephased transition averages of `std::linalg::spectral` (Stage 6,
#841; ADR 0001 §13) through the actual common source checker, the
independent declaration and Core audits, the Core semantics and its erasure,
and code generation. These are executable regressions, not proofs.

On `Plane = Affine(2)[delta, omega]`: the two-level field
`H = rows((delta/2, omega/2), (omega/2, −delta/2))` on `V = basis(g, e)`,
declared `symmetric`, its spectrum `S = eigen(H, t)` with `χ = t² − (δ² + ω²)/4`
and `adj(tI − H) = tI + H`, the branch `B` on `D(δ² + ω²)` with witness `2t`
and exponent 1, and the average `A` from `g` to `e` with the closed form
`frac(1, 2)·ω² / (δ² + ω²)`. Its trace form is `T = ω²(δ² + ω²)/2`, and its
denominator is the localization itself (`D·1 = g¹`).

On `Axis = Affine(1)[x]`: `K = rows((0, x), (x, 0))` on `U = basis(u1, u2)`,
the branch `BK` on `D(x)` with witness `t/2` and exponent 2, and the average
`AK` from `u1` to `u2` with the cancelled closed form `1/2`: `T = x⁴/2` and
`g^{2e} = x⁴`. `average_at` gives `1/2` where `x ≠ 0` and the failure value
`(0, 0)` at `x = 0`, where the certificate does not apply, although `1/2` has
no pole there (ADR 0001 §13, observation off the chart). -/
namespace VastitasKernel.Indexed.AverageRegression

open AlgebraRuntime

private def pkg : Namespace.PackageId := ⟨"/average/Vastitas.toml", "average", "0.1.0"⟩
private def id (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩
private def path (name : String) : Source.Path := ⟨[name], {}⟩
private def decl (name : String) (body : Source.Body) : Source.Declaration := ⟨name, body, true, {}⟩
private def c (name : String) : Source.PolyExpr := .coordinate name
private def n (value : Nat) : Source.PolyExpr := .natural value
private def neg (e : Source.PolyExpr) : Source.PolyExpr := .neg e
private def sq (e : Source.PolyExpr) : Source.PolyExpr := .pow e 2
private def half (e : Source.PolyExpr) : Source.PolyExpr := .product [.fraction 1 2, e]
private def space (name : String) (coordinates : List String) : Source.Declaration :=
  decl name (.smoothAffine (path "SmoothR") coordinates.length coordinates)
private def objectFamily (name : String) (representation : FamilyRepresentation) (arity : Nat := 1)
    (constraints : List Constraint := [.canonical 0]) : Source.Declaration :=
  decl name (.family ⟨(List.range arity).map fun _ => .object (path "CInfAffine"), constraints, representation⟩)
private def ref (field name : String) : String × Source.WireArgument := (field, .path (path name))
private def primitive (name : String) (binding : Source.Primitive) : Source.Declaration :=
  decl name (.primitive binding)

private def freeModule (name object : String) (basis : List String) : Source.Declaration :=
  decl name (.freeModule (path "FreeModule") [path object] basis)
private def endomorphism (name object module : String) (rows : List (List Source.PolyExpr)) (symmetric : Bool) :
    Source.Declaration :=
  decl name (.endomorphism (path "Endomorphism") [path object] (path module) rows symmetric)
private def spectrum (name object endo : String) : Source.Declaration :=
  decl name (.spectrum (path "Spectrum") [path object] (path endo) "t")
private def branch (name object spec : String) (localize witness : Source.PolyExpr) (exponent : Nat) :
    Source.Declaration :=
  decl name (.branch (path "Branch") [path object] (path spec) localize witness exponent)
private def average (name object branchName source target : String) (numerator denominator : Source.PolyExpr)
    (family := "TransitionAverage") : Source.Declaration :=
  decl name (.transitionAverage (path family) [path object] (path branchName) source target numerator denominator)
private def averageAt (name averageName : String) (line := "Line") : Source.Declaration :=
  primitive name ⟨"average_at", [ref "map_family" "Smooth", ref "line" line, ref "average" averageName]⟩

/-- The smooth profile with the spectral families and the objects. -/
private def base : List Source.Declaration := [
  decl "CInfReal" .marker,
  decl "SmoothR" (.implementation (path "CInfReal") .smoothAffine []),
  decl "CInfAffine" (.classification [] [path "SmoothR"]),
  objectFamily "Smooth" .smooth 2 [.canonical 0, .canonical 1],
  objectFamily "FreeModule" .freeModule,
  objectFamily "Endomorphism" .endomorphism,
  objectFamily "Spectrum" .spectrum,
  objectFamily "Branch" .branch,
  objectFamily "TransitionAverage" .transitionAverage,
  space "Pt" [],
  space "Line" ["s"],
  space "Plane" ["delta", "omega"],
  space "Axis" ["x"],
  primitive "plane_at" ⟨"smooth_int_point", [ref "family" "Smooth", ref "object" "Plane", ref "point" "Pt"]⟩,
  primitive "axis_at" ⟨"smooth_int_point", [ref "family" "Smooth", ref "object" "Axis", ref "point" "Pt"]⟩]

/-- `δ² + ω²`, the localization of the two-level branch. -/
private def gapExpr : Source.PolyExpr := .sum [sq (c "delta"), sq (c "omega")]

/-- The two-level field, its spectrum and its branch, with `symmetric` as
given. -/
private def twoLevel (symmetric : Bool := true) : List Source.Declaration := [
  freeModule "V" "Plane" ["g", "e"],
  endomorphism "H" "Plane" "V" [[half (c "delta"), half (c "omega")], [half (c "omega"), neg (half (c "delta"))]]
    symmetric,
  spectrum "S" "Plane" "H",
  branch "B" "Plane" "S" gapExpr (.product [n 2, c "t"]) 1]

/-- The field `[[0, x], [x, 0]]` on the axis, its spectrum and its branch on
`D(x)`. -/
private def axisField : List Source.Declaration := [
  freeModule "U" "Axis" ["u1", "u2"],
  endomorphism "K" "Axis" "U" [[n 0, c "x"], [c "x", n 0]] true,
  spectrum "SK" "Axis" "K",
  branch "BK" "Axis" "SK" (c "x") (half (c "t")) 2]

/-- The average `A = frac(1, 2)·ω² / (δ² + ω²)` from `g` to `e`. -/
private def averageA : Source.Declaration := average "A" "Plane" "B" "g" "e" (half (sq (c "omega"))) gapExpr
/-- The cancelled average `AK = 1/2` from `u1` to `u2`. -/
private def averageAK : Source.Declaration := average "AK" "Axis" "BK" "u1" "u2" (.fraction 1 2) (n 1)

private def declarations : List Source.Declaration :=
  base ++ twoLevel ++ axisField ++ [averageA, averageAK, averageAt "at" "A", averageAt "atK" "AK"]

private def program (ds := declarations) : Source.Program := {
  file := "average", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := {path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {}}
    declarations := ds }], none⟩] }

private def check := RegressionSupport.check "transition average regression failed"

private def code (p : Source.Program) : String :=
  match Source.checkDeclarations p with
  | .ok _ => "accepted"
  | .error e => e.code

private def message (p : Source.Program) : String :=
  match Source.checkDeclarations p with
  | .ok _ => ""
  | .error e => e.message

private def mentions (text part : String) : Bool := (text.splitOn part).length > 1

private def rejectsWith (p : Source.Program) (expected text : String) : Bool :=
  code p == expected && mentions (message p) text

private def resolved : Option Core.Declarations :=
  match Source.checkDeclarations program with
  | .ok checked => some checked.resolved.declarations
  | .error _ => none
private def env : Core.Declarations := resolved.getD default
private def binding (name : String) : Option PrimitiveBinding := resolved.bind (·.primitive? (id name))

private def q (numerator : Int) (denominator : Nat := 1) : Rat := mkRat numerator denominator
private def δ : Poly := Poly.var 2 0
private def ω : Poly := Poly.var 2 1
private def x : Poly := Poly.var 1 0
private def gap : Poly := Poly.add (Poly.mul δ δ) (Poly.mul ω ω)

/-! ## The two averages are accepted with the kernel's certificates -/

#eval check "the common source checker accepts both averages and both observations"
  (code program == "accepted")
#eval check "declaration order independent" (code (program declarations.reverse) == "accepted")
#eval check "the averages without observations are accepted on their own"
  (code (program (base ++ twoLevel ++ axisField ++ [averageA, averageAK])) == "accepted")

#eval check "the two-level average: g to e, ω²/2 over δ² + ω², T = ω²(δ² + ω²)/2, D·1 = g"
  (transitionAverageData? env.indexed (id "A") == some (id "TransitionAverage", id "Plane", id "B", 0, 1,
    Poly.scale (1 / 2) (Poly.mul ω ω), gap,
    ⟨Poly.scale (1 / 2) (Poly.mul (Poly.mul ω ω) gap), Poly.one 2, 1⟩))
#eval check "the cancelled average: u1 to u2, 1/2 over 1, T = x⁴/2, D·1 = g⁰"
  (transitionAverageData? env.indexed (id "AK") == some (id "TransitionAverage", id "Axis", id "BK", 0, 1,
    Poly.const 1 (1 / 2), Poly.one 1, ⟨Poly.scale (1 / 2) (Poly.pow 1 x 4), Poly.one 1, 0⟩))
#eval check "the declaration audit accepts the checked environment" (validEnvironment env.indexed)

/-! ## A tampered average fails the declaration audit -/

private def tamperedEntry (f : Declaration → Declaration) : Bool :=
  let entries := env.indexed.map fun entry => if entry.id == id "A" then ⟨entry.id, f entry.declaration⟩ else entry
  !validEnvironment entries

#eval check "a tampered closed form, trace, unit certificate or basis index is rejected"
  (tamperedEntry (fun
      | .transitionAverage f o b i j _ d cert => .transitionAverage f o b i j (Poly.mul ω ω) d cert
      | other => other) &&
    tamperedEntry (fun
      | .transitionAverage f o b i j num d cert => .transitionAverage f o b i j num d { cert with trace := gap }
      | other => other) &&
    tamperedEntry (fun
      | .transitionAverage f o b i j num d cert => .transitionAverage f o b i j num d { cert with unitExponent := 2 }
      | other => other) &&
    tamperedEntry (fun
      | .transitionAverage f o b i j num d cert =>
        .transitionAverage f o b i j num d { cert with unitQuotient := Poly.const 2 2 }
      | other => other) &&
    tamperedEntry (fun
      | .transitionAverage f o b _ j num d cert => .transitionAverage f o b 2 j num d cert
      | other => other) &&
    tamperedEntry (fun
      | .transitionAverage f o _ i j num d cert => .transitionAverage f o (id "BK") i j num d cert
      | other => other))
#eval check "the swapped direction of a symmetric field gives the same average and is accepted"
  (!tamperedEntry (fun
      | .transitionAverage f o b i j num d cert => .transitionAverage f o b j i num d cert
      | other => other))

/-! ## Rejected averages -/

private def withAverage (ds : List Source.Declaration) (avg : Source.Declaration) : Source.Program :=
  program (base ++ ds ++ [avg])

#eval check "a wrong closed form is rejected, naming the residual"
  (rejectsWith (withAverage twoLevel (average "A" "Plane" "B" "g" "e" (sq (c "omega")) gapExpr)) "E_SPECTRAL"
    "the closed form ratio(N, D) of the transition average `average::A` is not the average of its branch: N·g^(2e) − D·T is not zero")
#eval check "a denominator that is not a unit on D(g) is rejected, although N·g^(2e) = D·T"
  (rejectsWith (withAverage twoLevel (average "A" "Plane" "B" "g" "e" (.product [c "delta", sq (c "omega")])
      (.product [n 2, c "delta", gapExpr]))) "E_SPECTRAL"
    "the denominator of the closed form of the transition average `average::A` is not a unit on the chart D(g) of its branch")
#eval check "a field that is not declared symmetric is rejected"
  (rejectsWith (withAverage (twoLevel (symmetric := false)) averageA) "E_SPECTRAL"
    "the transition average `average::A` needs a symmetric field, but the endomorphism `average::H` of its branch `average::B` is not declared `symmetric`")
#eval check "a basis vector of another module is rejected"
  (rejectsWith (withAverage (twoLevel ++ axisField) (average "A" "Plane" "B" "u1" "e" (half (sq (c "omega"))) gapExpr))
    "E_SPECTRAL" "the source vector `u1` of the transition average `average::A` is not a basis vector of the free module `average::V`, whose basis is g, e" &&
    rejectsWith (withAverage twoLevel (average "A" "Plane" "B" "g" "z" (half (sq (c "omega"))) gapExpr)) "E_SPECTRAL"
      "the target vector `z` of the transition average `average::A` is not a basis vector")
#eval check "a zero denominator is rejected"
  (rejectsWith (withAverage twoLevel (average "A" "Plane" "B" "g" "e" (n 1) (n 0))) "E_SPECTRAL"
    "the denominator of the closed form of the transition average `average::A` is zero")
#eval check "a branch of another object, or no branch, is rejected"
  (rejectsWith (withAverage (twoLevel ++ axisField) (average "A" "Axis" "B" "u1" "u2" (n 1) (n 1))) "E_SPECTRAL"
      "an average and its branch have one object" &&
    rejectsWith (withAverage twoLevel (average "A" "Plane" "S" "g" "e" (n 1) (n 1))) "E_SPECTRAL"
      "is an average of `average::S`, which is not a branch declaration")
#eval check "an average at a family of another representation is rejected"
  (rejectsWith (withAverage twoLevel (average "A" "Plane" "B" "g" "e" (n 1) (n 1) (family := "Branch"))) "E_SPECTRAL"
    "which is not a family with the representation `transition_average`")
#eval check "a coordinate of another object in the closed form is rejected"
  (code (withAverage twoLevel (average "A" "Plane" "B" "g" "e" (c "x") gapExpr)) == "E_AFFINE_COORDINATE")

/-! ## `average_at` embeds its declaration and is valid -/

private def branchRef (name : String) : BranchRef := (Source.branchRef? env.indexed (id name)).getD default
private def averageRef (name : String) : AverageRef := (Source.averageRef? env.indexed (id name)).getD default

#eval check "average_at embeds the average, its branch and its closed form"
  (binding "at" == some (.averageAt (id "Smooth") (id "Line") ⟨id "A", branchRef "B", Poly.scale (1 / 2) (Poly.mul ω ω),
    gap⟩) &&
    binding "atK" == some (.averageAt (id "Smooth") (id "Line") ⟨id "AK", branchRef "BK", Poly.const 1 (1 / 2),
      Poly.one 1⟩))
#eval check "every binding is valid, none allocates, and average_at takes one point"
  (env.primitives.all (fun entry => validPrimitiveBinding env.indexed entry.binding && !entry.binding.allocates) &&
    (binding "at").map (·.arity env.indexed) == some 1)
#eval check "average_at has no derivative rule" ((binding "at").all fun b => b.contract.reverse == .none)

private def tamper (extra : PrimitiveBinding) : Bool :=
  !Core.validDeclarations { env with primitives := env.primitives ++ [⟨id "bad", extra⟩] }

private def A : AverageRef := averageRef "A"

#eval check "accepted Core is valid, and a fresh copy of average_at is accepted"
  (Core.validDeclarations env && !tamper (.averageAt (id "Smooth") (id "Line") A))
#eval check "a forged closed form, branch or average name is rejected"
  (tamper (.averageAt (id "Smooth") (id "Line") { A with numerator := Poly.mul ω ω }) &&
    tamper (.averageAt (id "Smooth") (id "Line") { A with denominator := Poly.one 2 }) &&
    tamper (.averageAt (id "Smooth") (id "Line") { A with branch := { branchRef "B" with localize := Poly.one 2 } }) &&
    tamper (.averageAt (id "Smooth") (id "Line") { A with branch := branchRef "BK" }) &&
    tamper (.averageAt (id "Smooth") (id "Line") { A with average := id "AK" }) &&
    tamper (.averageAt (id "Smooth") (id "Line") { A with average := id "B" }))
#eval check "a forged family or line is rejected"
  (tamper (.averageAt (id "Branch") (id "Line") A) && tamper (.averageAt (id "Smooth") (id "Plane") A))
#eval check "the source checker names a line that is not 1-dimensional"
  (rejectsWith (program (base ++ twoLevel ++ [averageA, averageAt "bad" "A" (line := "Plane")])) "E_TYPE"
    "the line `average::Plane` of the `average_at` primitive `average::bad` must be a smooth object of dimension 1")
#eval check "the source checker names an average_at of a declaration that is no transition average"
  (rejectsWith (program (base ++ twoLevel ++ [averageAt "bad" "B"])) "E_SPECTRAL"
    "the average of `average_at` must be a transition average, but `average::B` is not a transition average declaration")

/-! ## The value at a point: only on the chart `D(g)` -/

#eval check "the runtime gives N(p)/D(p) on the chart and (0, 0) off it"
  (SpectralRuntime.averageAt gap (Poly.scale (1 / 2) (Poly.mul ω ω)) gap (SmoothRuntime.intPoint [1, 2]) == (2, 5) &&
    SpectralRuntime.averageAt gap (Poly.scale (1 / 2) (Poly.mul ω ω)) gap (SmoothRuntime.intPoint [3, 4]) == (8, 25) &&
    SpectralRuntime.averageAt gap (Poly.scale (1 / 2) (Poly.mul ω ω)) gap (SmoothRuntime.intPoint [0, 0]) == (0, 0) &&
    SpectralRuntime.averageAt x (Poly.const 1 (1 / 2)) (Poly.one 1) (SmoothRuntime.intPoint [3]) == (1, 2) &&
    SpectralRuntime.averageAt x (Poly.const 1 (1 / 2)) (Poly.one 1) (SmoothRuntime.intPoint [0]) == (0, 0))

private def obj (name : String) : Index := .object (.global (id name))
private def smoothType (a b : String) : Core.Result := ⟨.indexed ⟨id "Smooth", [obj a, obj b]⟩, none⟩
private def bool : Core.Result := ⟨.pure .bool, none⟩
private def pairType : Core.Result := ⟨.pure (.pair .int), none⟩
private def prim (name : String) (arguments : List Core.Term) (result : Core.Result) : Core.Term :=
  .primitive (id name) arguments result
private def planeAt (a b : Int) : Core.Term := prim "plane_at" [.integer a, .integer b] (smoothType "Pt" "Plane")
private def axisAt (a : Int) : Core.Term := prim "axis_at" [.integer a] (smoothType "Pt" "Axis")
private def equals (left : Core.Term) (right : Int) : Core.Term := .binary .eq left (.integer right) bool
private def isFraction (value : Core.Term) (a b : Int) : Core.Term :=
  .binary .and (equals (.project .int true value) a) (equals (.project .int false value) b) bool
private def guarded (condition : Core.Term) (code : Int) (rest : Core.Term) : Core.Term :=
  .branch condition rest (.integer code) ⟨.pure .int, none⟩

private def averageMain : Core.Function := {
  id := 0, definition := id "main", parameters := [], returnType := .pure .int
  body :=
    guarded (isFraction (prim "at" [planeAt 1 2] pairType) 2 5) 1 <|
    guarded (isFraction (prim "at" [planeAt 3 4] pairType) 8 25) 2 <|
    guarded (isFraction (prim "at" [planeAt 0 1] pairType) 1 2) 3 <|
    guarded (isFraction (prim "at" [planeAt 1 0] pairType) 0 1) 4 <|
    guarded (isFraction (prim "at" [planeAt 0 0] pairType) 0 0) 5 <|
    guarded (isFraction (prim "atK" [axisAt 3] pairType) 1 2) 6 <|
    guarded (isFraction (prim "atK" [axisAt (-2)] pairType) 1 2) 7 <|
    -- The cancelled closed form has no pole at x = 0, but x = 0 is off the chart.
    guarded (isFraction (prim "atK" [axisAt 0] pairType) 0 0) 8 <|
    .integer 42 }

/-- The transition averages of this regression as one audited Core module. -/
def averageFixture : Core.Module := ⟨env, [averageMain], some 0⟩

private def evaluate (term : Core.Term) : Option Core.Semantics.Value :=
  Core.Semantics.eval averageFixture 64 (fun _ => none) term

#eval check "the average Core module is accepted" (Core.Typing.checkModule averageFixture true).isOk
#eval check "the average Core module evaluates to 42" (evaluate averageMain.body == some (.integer 42))
private def withBody (body : Core.Term) : Core.Function := { averageMain with body := body }

#eval check "a point of another object is rejected"
  (!(Core.Typing.checkModule ⟨env, [withBody (guarded (isFraction (prim "at" [axisAt 1] pairType) 0 0) 1
    (.integer 42))], some 0⟩ true).isOk)

private def pointValue (values : List Int) : Core.Semantics.Value :=
  .indexed (.smooth (SmoothRuntime.intPoint values))

private def agrees (name : String) (values : List Core.Semantics.Value) : Bool :=
  match binding name with
  | some b => match Core.Semantics.evalPrimitive env.indexed b values with
    | some value => match values.mapM Core.Semantics.erasePrimitiveValue, Core.Semantics.erasePrimitiveValue value with
      | some inputs, some output => Core.Semantics.evalRuntimePrimitive b inputs == some output
      | _, _ => false
    | none => false
  | none => false

#eval check "average_at erases to its runtime evaluator, on and off the chart"
  (agrees "at" [pointValue [1, 2]] && agrees "at" [pointValue [0, 0]] && agrees "atK" [pointValue [0]] &&
    agrees "atK" [pointValue [5]])
#eval check "the evaluators take exactly one point"
  (["at", "atK"].all fun name => (binding name).all fun b =>
    (Core.Semantics.evalPrimitive env.indexed b []).isNone &&
      (Core.Semantics.evalPrimitive env.indexed b [.integer 1]).isNone &&
      (Core.Semantics.evalRuntimePrimitive b []).isNone)

/-! ## Generated code -/

private def generatedCode (function : Core.Function) : Option String := do
  let .ok checked := Core.Typing.checkModule ⟨env, [function], some 0⟩ true | none
  (Core.Codegen.generate checked).toOption
private def occurrences (part : String) (source : Option String) : Option Nat :=
  source.map fun text => (text.splitOn part).length - 1

#eval check "average_at lowers to the spectral runtime and imports it"
  (let source := generatedCode averageMain
  (occurrences "VastitasKernel.SpectralRuntime.averageAt poly_" source).any (· > 0) &&
    occurrences "import VastitasKernel.SpectralRuntime\n" source == some 1)
#eval check "a lowering with the wrong operand count is the arity error"
  ((binding "at").all fun b => !(b.contract.render (.share []) ["a", "b"]).toBool)

end VastitasKernel.Indexed.AverageRegression
