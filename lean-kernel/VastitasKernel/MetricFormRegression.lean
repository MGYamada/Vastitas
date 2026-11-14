import VastitasKernel.IndexedSourceChecker
import VastitasKernel.IndexedDeclarationProtocol
import VastitasKernel.IndexedCodegen
import VastitasKernel.IndexedSemantics
import VastitasKernel.RegressionSupport

set_option autoImplicit false

/-! Metrics, metric evidence, `flat` and `sharp` (Stage 3) through the actual
common source checker, the independent declaration and Core audits, the Core
semantics, code generation and the protocol decoder. These are executable
regressions, not proofs. -/
namespace VastitasKernel.Indexed.MetricFormRegression

open AlgebraRuntime

private def pkg : Namespace.PackageId := ⟨"/metric/Vastitas.toml", "metric", "0.1.0"⟩
private def id (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩
private def path (name : String) : Source.Path := ⟨[name], {}⟩
private def decl (name : String) (body : Source.Body) : Source.Declaration := ⟨name, body, true, {}⟩
private def c (name : String) : Source.PolyExpr := .coordinate name
private def n (value : Nat) : Source.PolyExpr := .natural value
private def neg (value : Nat) : Source.PolyExpr := .neg (.natural value)
private def space (name : String) (dimension : Nat) (coordinates : List String) : Source.Declaration :=
  decl name (.smoothAffine (path "SmoothR") dimension coordinates)
private def morphism (name x y : String) (definition : Source.MorphismDefinition) : Source.Declaration :=
  decl name (.morphism (path "Smooth") [path x, path y] definition)
private def primitive (name : String) (binding : Source.Primitive) : Source.Declaration :=
  decl name (.primitive binding)
private def ref (field name : String) : String × Source.WireArgument := (field, .path (path name))
private def metric (name : String) (gram : Source.MetricGram) (object := "Plane") (family := "MetricForm") :
    Source.Declaration :=
  decl name (.metric (path family) [path object] gram)
private def evidence (name metric : String) (kind : Source.EvidenceKind) : Source.Declaration :=
  decl name (.evidence (path metric) kind)
private def flat (name metric : String) : Source.Declaration :=
  primitive name ⟨"flat", [ref "tangent" "Tangent", ref "cotangent" "Cotangent", ref "metric" metric]⟩
private def sharp (name metric evidence : String) : Source.Declaration :=
  primitive name ⟨"sharp",
    [ref "cotangent" "Cotangent", ref "tangent" "Tangent", ref "metric" metric, ref "evidence" evidence]⟩

private def family (name : String) (representation : FamilyRepresentation) (arity : Nat)
    (constraints : List Constraint) : Source.Declaration :=
  decl name (.family ⟨(List.range arity).map fun _ => .object (path "CInfAffine"), constraints, representation⟩)

/-- The metric-free profile: smooth objects, maps, fibers and the differential. -/
private def metricFree : List Source.Declaration := [
  decl "CInfReal" .marker,
  decl "SmoothR" (.implementation (path "CInfReal") .smoothAffine []),
  decl "CInfAffine" (.classification [] [path "SmoothR"]),
  family "Smooth" .smooth 2 [.canonical 0, .canonical 1],
  family "Cotangent" (.fiber .cotangent) 1 [.canonical 0],
  family "Tangent" (.fiber .tangent) 1 [.canonical 0],
  space "Pt" 0 [],
  space "Line" 1 ["t"],
  space "Plane" 2 ["x", "y"],
  space "Space" 3 ["u", "v", "w"],
  morphism "g" "Plane" "Line" (.pullback [("t", .sum [.pow (c "x") 2, c "y"])]),
  primitive "plane_at" ⟨"smooth_int_point", [ref "family" "Smooth", ref "object" "Plane", ref "point" "Pt"]⟩,
  primitive "line_at" ⟨"smooth_int_point", [ref "family" "Smooth", ref "object" "Line", ref "point" "Pt"]⟩,
  primitive "vline" ⟨"fiber_vector", [ref "family" "Tangent", ref "map_family" "Smooth", ref "object" "Line"]⟩,
  primitive "dline" ⟨"fiber_vector", [ref "family" "Cotangent", ref "map_family" "Smooth", ref "object" "Line"]⟩,
  primitive "space_at" ⟨"smooth_int_point", [ref "family" "Smooth", ref "object" "Space", ref "point" "Pt"]⟩,
  primitive "dspace" ⟨"fiber_vector", [ref "family" "Cotangent", ref "map_family" "Smooth", ref "object" "Space"]⟩,
  primitive "vspace" ⟨"fiber_vector", [ref "family" "Tangent", ref "map_family" "Smooth", ref "object" "Space"]⟩,
  primitive "differential"
    ⟨"differential", [ref "map_family" "Smooth", ref "cotangent" "Cotangent", ref "line" "Line"]⟩,
  primitive "tangent_over" ⟨"fiber_at", [ref "family" "Tangent", ref "map_family" "Smooth"]⟩,
  primitive "same_vector" ⟨"fiber_equal", [ref "family" "Tangent"]⟩,
  primitive "same_covector" ⟨"fiber_equal", [ref "family" "Cotangent"]⟩,
  primitive "pairing" ⟨"fiber_pairing", [ref "cotangent" "Cotangent", ref "tangent" "Tangent"]⟩,
  primitive "dplane" ⟨"fiber_vector", [ref "family" "Cotangent", ref "map_family" "Smooth", ref "object" "Plane"]⟩,
  primitive "vplane" ⟨"fiber_vector", [ref "family" "Tangent", ref "map_family" "Smooth", ref "object" "Plane"]⟩,
  primitive "dx" ⟨"fiber_component", [ref "family" "Cotangent", ref "object" "Plane", ("coordinate", .coordinate "x")]⟩,
  primitive "dy" ⟨"fiber_component", [ref "family" "Cotangent", ref "object" "Plane", ("coordinate", .coordinate "y")]⟩,
  primitive "vx" ⟨"fiber_component", [ref "family" "Tangent", ref "object" "Plane", ("coordinate", .coordinate "x")]⟩,
  primitive "vy" ⟨"fiber_component", [ref "family" "Tangent", ref "object" "Plane", ("coordinate", .coordinate "y")]⟩ ]

/-- Metrics, evidence, `flat` and `sharp` on the plane. -/
private def metrics : List Source.Declaration := [
  family "MetricForm" .metricForm 1 [.canonical 0],
  metric "Euclid" .euclidean,
  metric "Skew" (.rows [[n 2, n 1], [n 1, n 1]]),
  metric "Lorentz" (.rows [[n 1, n 0], [n 0, neg 1]]),
  metric "Half" (.rows [[.fraction 1 2, n 0], [n 0, .product [n 2, n 3]]]),
  evidence "EuclidInvertible" "Euclid" .nondegenerate,
  evidence "SkewInvertible" "Skew" .nondegenerate,
  evidence "SkewPositive" "Skew" .riemannian,
  evidence "LorentzInvertible" "Lorentz" .nondegenerate,
  evidence "HalfPositive" "Half" .riemannian,
  flat "flat_euclid" "Euclid",
  flat "flat_skew" "Skew",
  sharp "sharp_euclid" "Euclid" "EuclidInvertible",
  sharp "sharp_skew" "Skew" "SkewInvertible",
  sharp "sharp_lorentz" "Lorentz" "LorentzInvertible",
  -- `euclidean` on objects of dimension 1 and 3.
  metric "EuclidLine" .euclidean "Line",
  metric "Euclid3" .euclidean "Space",
  metric "Diag3" (.rows [[n 2, n 0, n 0], [n 0, n 3, n 0], [n 0, n 0, n 4]]) "Space",
  evidence "EuclidLinePositive" "EuclidLine" .riemannian,
  evidence "EuclidLineInvertible" "EuclidLine" .nondegenerate,
  evidence "Euclid3Invertible" "Euclid3" .nondegenerate,
  evidence "Diag3Invertible" "Diag3" .nondegenerate,
  sharp "sharp_line" "EuclidLine" "EuclidLineInvertible",
  sharp "sharp_space" "Euclid3" "Euclid3Invertible",
  sharp "sharp_diag3" "Diag3" "Diag3Invertible" ]

private def declarations : List Source.Declaration := metricFree ++ metrics

private def program (ds := declarations) : Source.Program := {
  file := "metric", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := {path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {}}
    declarations := ds }], none⟩] }

private def check := RegressionSupport.check "metric regression failed"

private def with' (extra : List Source.Declaration) : Source.Program := program (declarations ++ extra)

private def replacing (name : String) (replacement : Source.Declaration) : Source.Program :=
  program (declarations.map fun d => if d.name == name then replacement else d)

private def code (p : Source.Program) : String :=
  match Source.checkDeclarations p with
  | .ok _ => "accepted"
  | .error e => e.code

private def message (p : Source.Program) : String :=
  match Source.checkDeclarations p with
  | .ok _ => ""
  | .error e => e.message

private def mentions (p : Source.Program) (text : String) : Bool := ((message p).splitOn text).length > 1

private def rejectsWith (p : Source.Program) (expected text : String) : Bool := code p == expected && mentions p text

private def resolvedOf (p : Source.Program) : Option Core.Declarations :=
  match Source.checkDeclarations p with
  | .ok checked => some checked.resolved.declarations
  | .error _ => none

private def resolved : Option Core.Declarations := resolvedOf program

private def lookupIn (name : String) : Option Declaration := resolved.bind (lookup ·.indexed (id name))
private def binding (name : String) : Option PrimitiveBinding := resolved.bind (·.primitive? (id name))

private def q (numerator : Int) (denominator : Nat := 1) : Rat := mkRat numerator denominator

#eval check "the common source checker accepts metrics, evidence, flat and sharp" (code program == "accepted")
#eval check "declaration order independent" (code (program declarations.reverse) == "accepted")
#eval check "the metric-free profile is accepted on its own" (code (program metricFree) == "accepted")

/-! ## Certificates are computed and checked again -/

#eval check "euclidean elaborates to the identity of dim Plane"
  (lookupIn "Euclid" == some (.metric (id "MetricForm") (id "Plane") [[1, 0], [0, 1]]))
#eval check "explicit Gram entries are exact rationals, fractions and products included"
  (lookupIn "Skew" == some (.metric (id "MetricForm") (id "Plane") [[2, 1], [1, 1]]) &&
    lookupIn "Lorentz" == some (.metric (id "MetricForm") (id "Plane") [[1, 0], [0, -1]]) &&
    lookupIn "Half" == some (.metric (id "MetricForm") (id "Plane") [[q 1 2, 0], [0, 6]]))
#eval check "nondegenerate evidence is the exact inverse"
  (lookupIn "SkewInvertible" == some (.metricEvidence (id "Skew") (.nondegenerate [[1, -1], [-1, 2]])) &&
    lookupIn "LorentzInvertible" == some (.metricEvidence (id "Lorentz") (.nondegenerate [[1, 0], [0, -1]])) &&
    lookupIn "EuclidInvertible" == some (.metricEvidence (id "Euclid") (.nondegenerate [[1, 0], [0, 1]])))
#eval check "Riemannian evidence is L D Lᵀ with positive D and the inverse of L"
  (lookupIn "SkewPositive" ==
    some (.metricEvidence (id "Skew") (.riemannian [[1, 0], [q 1 2, 1]] [2, q 1 2] [[1, 0], [q (-1) 2, 1]])) &&
    lookupIn "HalfPositive" ==
      some (.metricEvidence (id "Half") (.riemannian [[1, 0], [0, 1]] [q 1 2, 6] [[1, 0], [0, 1]])))
#eval check "the stored certificates pass the kernel's checks"
  (SmoothDeclarations.checkNondegenerate 2 [[2, 1], [1, 1]] [[1, -1], [-1, 2]] &&
    SmoothDeclarations.checkRiemannian 2 [[2, 1], [1, 1]] [[1, 0], [q 1 2, 1]] [2, q 1 2] [[1, 0], [q (-1) 2, 1]])
#eval check "euclidean on objects of dimension 1 and 3 is the identity of that dimension"
  (lookupIn "EuclidLine" == some (.metric (id "MetricForm") (id "Line") [[1]]) &&
    lookupIn "Euclid3" == some (.metric (id "MetricForm") (id "Space") [[1, 0, 0], [0, 1, 0], [0, 0, 1]]) &&
    lookupIn "EuclidLinePositive" == some (.metricEvidence (id "EuclidLine") (.riemannian [[1]] [1] [[1]])) &&
    lookupIn "Diag3Invertible" ==
      some (.metricEvidence (id "Diag3") (.nondegenerate [[q 1 2, 0, 0], [0, q 1 3, 0], [0, 0, q 1 4]])))
#eval check "flat embeds the metric's object and Gram matrix"
  (binding "flat_skew" == some (.metricFlat (id "Skew") (id "Plane") [[2, 1], [1, 1]] (id "Tangent") (id "Cotangent")))
#eval check "sharp embeds the metric's Gram matrix and the evidence's inverse"
  (binding "sharp_skew" == some (.metricSharp (id "Skew") (id "SkewInvertible") (id "Plane") [[2, 1], [1, 1]]
    [[1, -1], [-1, 2]] (id "Cotangent") (id "Tangent")))
#eval check "flat and sharp take one operand and no integer hint"
  ((resolved.map fun env => ((binding "flat_skew").map (·.arity env.indexed), (binding "sharp_skew").map
    (·.arity env.indexed))) == some (some 1, some 1) &&
    (binding "sharp_skew").map (·.argumentHint 0) == some none)
#eval check "a metric form family is not a fiber family"
  ((resolved.map fun env =>
      (isMetricFamily env.indexed (id "MetricForm"), fiberVariance? env.indexed (id "MetricForm"))) ==
    some (true, none))

/-! ## An executable Core module

It checks the gradients of `g(x, y) = x² + y` at `(1, 2)` under three metrics,
and the musical isomorphisms. The native fixture script compiles it. -/

private def obj (name : String) : Index := .object (.global (id name))
private def smoothType (x y : String) : Core.Result := ⟨.indexed ⟨id "Smooth", [obj x, obj y]⟩, none⟩
private def cotangentType (x : String) : Core.Result := ⟨.indexed ⟨id "Cotangent", [obj x]⟩, none⟩
private def tangentType (x : String) : Core.Result := ⟨.indexed ⟨id "Tangent", [obj x]⟩, none⟩
private def bool : Core.Result := ⟨.pure .bool, none⟩
private def pairType : Core.Result := ⟨.pure (.pair .int), none⟩
private def prim (name : String) (arguments : List Core.Term) (result : Core.Result) : Core.Term :=
  .primitive (id name) arguments result
private def planeAt (x y : Int) : Core.Term := prim "plane_at" [.integer x, .integer y] (smoothType "Pt" "Plane")
private def dplane (point : Core.Term) (x y : Int) : Core.Term :=
  prim "dplane" [point, .integer x, .integer y] (cotangentType "Plane")
private def vplane (point : Core.Term) (x y : Int) : Core.Term :=
  prim "vplane" [point, .integer x, .integer y] (tangentType "Plane")
private def lower (name : String) (vector : Core.Term) : Core.Term := prim name [vector] (cotangentType "Plane")
private def raise (name : String) (covector : Core.Term) : Core.Term := prim name [covector] (tangentType "Plane")
private def sameVector (left right : Core.Term) : Core.Term := prim "same_vector" [left, right] bool
private def sameCovector (left right : Core.Term) : Core.Term := prim "same_covector" [left, right] bool
private def numerator (value : Core.Term) : Core.Term := .project .int true value
private def denominator (value : Core.Term) : Core.Term := .project .int false value
private def equals (left : Core.Term) (right : Int) : Core.Term := .binary .eq left (.integer right) bool
private def guarded (condition : Core.Term) (code : Int) (rest : Core.Term) : Core.Term :=
  .branch condition rest (.integer code) ⟨.pure .int, none⟩
private def notE (value : Core.Term) : Core.Term := .unary .not value bool

private def p : Core.Term := planeAt 1 2
private def dg : Core.Term := prim "differential" [prim "g" [] (smoothType "Plane" "Line"), p] (cotangentType "Plane")
private def gradient (sharp : String) : Core.Term := raise sharp dg

private def metricMain : Core.Function := {
  id := 0, definition := id "main", parameters := [], returnType := .pure .int
  body :=
    -- dg = (2, 1) at (1, 2), with no metric.
    guarded (sameCovector dg (dplane p 2 1)) 1 <|
    -- Euclid gives (2, 1), Skew (1, 0) and Lorentz (2, -1).
    guarded (sameVector (gradient "sharp_euclid") (vplane p 2 1)) 2 <|
    guarded (sameVector (gradient "sharp_skew") (vplane p 1 0)) 3 <|
    guarded (sameVector (gradient "sharp_lorentz") (vplane p 2 (-1))) 4 <|
    -- Two metrics give two gradients of one differential, each over p.
    guarded (notE (sameVector (gradient "sharp_euclid") (gradient "sharp_skew"))) 5 <|
    guarded (prim "tangent_over" [gradient "sharp_skew", p] bool) 6 <|
    -- sharp after flat is the identity; flat (5, -7) under Skew is (3, -2).
    guarded (sameVector (raise "sharp_euclid" (lower "flat_euclid" (vplane p 5 (-7)))) (vplane p 5 (-7))) 7 <|
    guarded (sameVector (raise "sharp_skew" (lower "flat_skew" (vplane p 5 (-7)))) (vplane p 5 (-7))) 8 <|
    guarded (sameCovector (lower "flat_skew" (vplane p 5 (-7))) (dplane p 3 (-2))) 9 <|
    -- dg(grad_Skew) = 2, and dg(grad_Skew) = g(grad_Skew, grad_Skew).
    guarded (equals (numerator (prim "pairing" [dg, gradient "sharp_skew"] pairType)) 2) 10 <|
    guarded (equals (numerator (prim "pairing" [lower "flat_skew" (gradient "sharp_skew"), gradient "sharp_skew"]
      pairType)) 2) 11 <|
    guarded (equals (denominator (prim "vy" [gradient "sharp_skew"] pairType)) 1) 12 <|
    .integer 42 }

/-- The metrics of this regression as one audited Core module. -/
def metricFixture : Core.Module := ⟨resolved.getD default, [metricMain], some 0⟩

#eval check "the metric Core module is accepted" (Core.Typing.checkModule metricFixture true).isOk
#eval check "the metric Core module evaluates to 42"
  (Core.Semantics.eval metricFixture 64 (fun _ => none) metricMain.body == some (Core.Semantics.Value.integer 42))
#eval check "the Skew gradient is the vector (1, 0) at (1, 2)"
  (Core.Semantics.eval metricFixture 64 (fun _ => none) (gradient "sharp_skew") ==
    some (.indexed (.fiber .tangent (some ⟨[1, 2], [1, 0]⟩))))
private def spaceAt (u v w : Int) : Core.Term :=
  prim "space_at" [.integer u, .integer v, .integer w] (smoothType "Pt" "Space")
private def evaluate (term : Core.Term) : Option Core.Semantics.Value :=
  Core.Semantics.eval metricFixture 64 (fun _ => none) term
#eval check "sharp with euclidean on a 3-dimensional object is the identity on components"
  (evaluate (prim "sharp_space" [prim "dspace" [spaceAt 1 2 3, .integer 4, .integer 5, .integer (-6)]
    (cotangentType "Space")] (tangentType "Space")) ==
    some (.indexed (.fiber .tangent (some ⟨[1, 2, 3], [4, 5, -6]⟩))))
#eval check "sharp with diag(2, 3, 4) divides each component"
  (evaluate (prim "sharp_diag3" [prim "dspace" [spaceAt 1 2 3, .integer 4, .integer 5, .integer (-6)]
    (cotangentType "Space")] (tangentType "Space")) ==
    some (.indexed (.fiber .tangent (some ⟨[1, 2, 3], [2, q 5 3, q (-3) 2]⟩))))
#eval check "sharp with euclidean on a line is the identity"
  (evaluate (prim "sharp_line" [prim "dline" [prim "line_at" [.integer 7] (smoothType "Pt" "Line"), .integer 5]
    (cotangentType "Line")] (tangentType "Line")) ==
    some (.indexed (.fiber .tangent (some ⟨[7], [5]⟩))))

/-! ## Generated code declares each matrix and each map once

A generated module declares each distinct matrix and each distinct declared
map of the primitives that its functions call, and every call names the
declaration (#629). The number of literals in the generated text does not
depend on the number of calls, and a primitive that no function calls adds
none. -/

/-- The generated code of a module whose entry point is `function`. -/
private def generatedCode (function : Core.Function) : Option String := do
  let .ok checked := Core.Typing.checkModule ⟨resolved.getD default, [function], some 0⟩ true | none
  (Core.Codegen.generate checked).toOption
/-- The generated code of an entry point that returns 42 when every check holds. -/
private def generatedChecks (checks : List Core.Term) : Option String :=
  generatedCode { metricMain with body := checks.foldr (fun condition rest => guarded condition 1 rest) (.integer 42) }
private def occurrences (part : String) (source : Option String) : Option Nat :=
  source.map fun text => (text.splitOn part).length - 1

private def matrixType : String := ": VastitasKernel.SmoothRuntime.Matrix)"
private def matrixDefinition (index : Nat) (rows : String) : String :=
  s!"def matrix_{index} : VastitasKernel.SmoothRuntime.Matrix :=\n  ([{rows}] {matrixType}\n"
private def identityRows : String := "[(mkRat (1 : Int) 1), (mkRat (0 : Int) 1)], [(mkRat (0 : Int) 1), (mkRat (1 : Int) 1)]"
private def skewRows : String := "[(mkRat (2 : Int) 1), (mkRat (1 : Int) 1)], [(mkRat (1 : Int) 1), (mkRat (1 : Int) 1)]"
private def skewInverseRows : String :=
  "[(mkRat (1 : Int) 1), (mkRat (-1 : Int) 1)], [(mkRat (-1 : Int) 1), (mkRat (2 : Int) 1)]"
private def lorentzRows : String := "[(mkRat (1 : Int) 1), (mkRat (0 : Int) 1)], [(mkRat (0 : Int) 1), (mkRat (-1 : Int) 1)]"
private def mapLiteral : String := "(VastitasKernel.AlgebraRuntime.Map.mk "
private def sharpCall (index : Nat) : String := s!"(VastitasKernel.SmoothRuntime.sharp matrix_{index} "
private def flatCall (index : Nat) : String := s!"(VastitasKernel.SmoothRuntime.flat matrix_{index} "
private def mapCall : String := "(VastitasKernel.SmoothRuntime.Program.primitive map_0)"

/-- One call of `sharp_skew` and one call of the declared map `g`. -/
private def skewGradient : Core.Term := sameVector (gradient "sharp_skew") (vplane p 1 0)
/-- One call of `sharp_lorentz` and one call of `g`. -/
private def lorentzGradient : Core.Term := sameVector (gradient "sharp_lorentz") (vplane p 2 (-1))
private def oneCall : Option String := generatedChecks [skewGradient]
private def sixCalls : Option String := generatedChecks (List.replicate 6 skewGradient)
private def twoMatrices : Option String := generatedChecks [skewGradient, lorentzGradient, skewGradient]

#eval check "the generated modules hold one call and six calls of sharp_skew and of g"
  ([oneCall, sixCalls].map (occurrences (sharpCall 0)) == [some 1, some 6] &&
    [oneCall, sixCalls].map (occurrences mapCall) == [some 1, some 6])
#eval check "one call and six calls of a sharp give one matrix literal"
  ([oneCall, sixCalls].map (occurrences matrixType) == [some 1, some 1] &&
    [oneCall, sixCalls].map (occurrences (matrixDefinition 0 skewInverseRows)) == [some 1, some 1])
#eval check "one call and six calls of a declared map give one map literal"
  ([oneCall, sixCalls].map (occurrences mapLiteral) == [some 1, some 1] &&
    [oneCall, sixCalls].map (occurrences ("def map_0 : VastitasKernel.AlgebraRuntime.Map :=\n  " ++ mapLiteral)) ==
      [some 1, some 1])
#eval check "two different matrices give two definitions, in declaration order"
  (occurrences (matrixDefinition 0 skewInverseRows) twoMatrices == some 1 &&
    occurrences (matrixDefinition 1 lorentzRows) twoMatrices == some 1 &&
    occurrences matrixType twoMatrices == some 2 &&
    occurrences (sharpCall 0) twoMatrices == some 2 && occurrences (sharpCall 1) twoMatrices == some 1 &&
    occurrences mapLiteral twoMatrices == some 1)
#eval check "a declared matrix or map that no function calls is not generated"
  (occurrences "matrix_" (generatedChecks []) == some 0 && occurrences "map_" (generatedChecks []) == some 0 &&
    occurrences "matrix_1" oneCall == some 0 && occurrences "map_1" oneCall == some 0)
#eval check "the equal matrices of two primitives are one definition"
  (let source := generatedChecks [sameVector (raise "sharp_euclid" (lower "flat_euclid" (vplane p 5 (-7))))
    (vplane p 5 (-7))]
  occurrences (matrixDefinition 0 identityRows) source == some 1 && occurrences matrixType source == some 1 &&
    occurrences (sharpCall 0 ++ flatCall 0) source == some 1)
#eval check "flat and sharp lower to the shared smooth runtime and name the declared matrices"
  (let source := generatedCode metricMain
  -- Euclid's Gram matrix is its own inverse: `flat_euclid` and `sharp_euclid` name one matrix.
  [matrixDefinition 0 identityRows, matrixDefinition 1 skewRows, matrixDefinition 2 skewInverseRows,
    matrixDefinition 3 lorentzRows].all (occurrences · source == some 1) &&
    occurrences matrixType source == some 4 && occurrences mapLiteral source == some 1 &&
    [flatCall 0, flatCall 1, sharpCall 0, sharpCall 2, sharpCall 3].all fun call =>
      (occurrences call source).any (· > 0))

/-! ## Static rejections in Core -/

private def rejected (body : Core.Term) : Bool :=
  !(Core.Typing.checkModule ⟨resolved.getD default, [{ metricMain with body := guarded body 1 (.integer 42) }],
    some 0⟩ true).isOk

#eval check "flat of a covector is rejected" (rejected (sameCovector (lower "flat_skew" dg) dg))
#eval check "sharp of a vector is rejected" (rejected (sameVector (raise "sharp_skew" (vplane p 1 0)) (vplane p 1 0)))
#eval check "flat of a vector over another object is rejected"
  (rejected (sameCovector (lower "flat_skew" (prim "vline" [prim "line_at" [.integer 1] (smoothType "Pt" "Line"),
    .integer 1] (tangentType "Line"))) dg))
#eval check "sharp claiming a covector result is rejected"
  (rejected (sameCovector (prim "sharp_skew" [dg] (cotangentType "Plane")) dg))

/-! ## Source rejections with specific codes -/

private def presented : List Source.Declaration := [
  decl "QQ" .marker,
  decl "AffineQQ" (.implementation (path "QQ") (.presentedAffine .rational) []),
  decl "AffineScheme" (.classification [] [path "AffineQQ"]),
  decl "SpecQQ" (.affine (path "AffineQQ") [] [] none []),
  decl "QLine" (.affine (path "AffineQQ") ["t"] [] (some (path "SpecQQ")) []) ]

#eval check "an asymmetric Gram matrix is E_METRIC"
  (rejectsWith (with' [metric "Bad" (.rows [[n 1, n 2], [n 3, n 4]])]) "E_METRIC"
    "the metric `metric::Bad` is not symmetric: the entries in row 1, column 2 and in row 2, column 1 differ")
#eval check "a Gram matrix of the wrong size is E_METRIC"
  (rejectsWith (with' [metric "Bad" (.rows [[n 1, n 0, n 0], [n 0, n 1, n 0], [n 0, n 0, n 1]])]) "E_METRIC"
    "needs 2 rows of 2 entries, but it has 3 rows" &&
    rejectsWith (with' [metric "Bad" (.rows [[n 1, n 0], [n 1]])]) "E_METRIC"
      "needs 2 entries in each row, but row 2 has 1" &&
    rejectsWith (with' [metric "Bad" (.rows [[n 1]]) "Plane"]) "E_METRIC" "but it has 1 rows")
#eval check "a non-constant Gram entry is E_METRIC"
  (rejectsWith (with' [metric "Bad" (.rows [[c "x", n 0], [n 0, n 1]])]) "E_METRIC"
    "the Gram entry in row 1, column 1 is not constant" &&
    rejectsWith (with' [metric "Bad" (.rows [[n 1, .product [c "x", c "y"]], [.product [c "y", c "x"], n 1]])])
      "E_METRIC" "row 1, column 2 is not constant")
#eval check "a constant expression in the coordinates is a constant"
  (code (with' [metric "Zero" (.rows [[.sum [c "x", .neg (c "x")], n 0], [n 0, n 1]])]) == "accepted")
#eval check "a Gram entry beyond the polynomial limits is E_LIMIT"
  (code (with' [metric "Bad" (.rows [[.pow (n 2) (Limits.algebraDegree + 1), n 0], [n 0, n 1]])]) == "E_LIMIT")
/-- A 64-digit literal. -/
private def big : Nat := 10 ^ 63 + 7
-- The matrix is singular: a certificate computed before the entry bound would
-- report `E_METRIC`, as it does for the same matrix with a small entry.
#eval check "an entry like (L^16)^16 with a 64-digit L is E_LIMIT before any certificate"
  (rejectsWith (with' [metric "Bad" (.rows [[.pow (.pow (n big) 16) 16, n 0], [n 0, n 0]]),
    evidence "E" "Bad" .nondegenerate]) "E_LIMIT"
    s!"the Gram entry in row 1, column 1 has more than {Limits.metricEntryBits} bits" &&
    rejectsWith (with' [metric "Bad" (.rows [[.pow (.pow (n big) 16) 16, n 0], [n 0, n 0]]),
      evidence "E" "Bad" .riemannian]) "E_LIMIT"
      s!"the Gram entry in row 1, column 1 has more than {Limits.metricEntryBits} bits" &&
    code (with' [metric "Bad" (.rows [[n big, n 0], [n 0, n 0]]), evidence "E" "Bad" .nondegenerate]) == "E_METRIC")
#eval check "the entry bound is 2^512 on the numerator and on the denominator"
  (let power := Source.PolyExpr.pow (.pow (.pow (n 2) 16) 16) 2
   code (with' [metric "Bad" (.rows [[power, n 0], [n 0, n 1]])]) == "E_LIMIT" &&
    code (with' [metric "Edge" (.rows [[.sum [power, .neg (n 1)], n 0], [n 0, n 1]]),
      evidence "E" "Edge" .nondegenerate, evidence "R" "Edge" .riemannian]) == "accepted" &&
    code (with' [metric "Bad" (.rows [[.product [.fraction 1 big, .fraction 1 big, .fraction 1 big], n 0],
      [n 0, n 1]])]) == "E_LIMIT" &&
    code (with' [metric "Edge" (.rows [[.product [n big, n big], .fraction 1 big], [.fraction 1 big, n 1]]),
      evidence "E" "Edge" .nondegenerate]) == "accepted")
#eval check "an unknown name in a Gram entry is a coordinate error"
  (code (with' [metric "Bad" (.rows [[c "z", n 0], [n 0, n 1]])]) == "E_AFFINE_COORDINATE")

/-! ## The matrix bound

The entry bound does not bound a certificate: the inverse grows with the least
common denominators of the rows. `metricMatrixBits` bounds the whole matrix,
and a metric beyond it is rejected before any certificate is computed. -/

#eval check "the measure clears the denominators of each row"
  (SmoothDeclarations.rowDenominator [q 1 2, q 1 3] == 6 &&
    SmoothDeclarations.rowNormSquare [q 1 2, q 1 3] == 3 ^ 2 + 2 ^ 2 &&
    SmoothDeclarations.rowNormSquare [q 1 3, 1] == 1 ^ 2 + 3 ^ 2 &&
    SmoothDeclarations.hadamardSquare [[q 1 2, q 1 3], [q 1 3, 1]] == 13 * 10 * 6 ^ 2 &&
    SmoothDeclarations.hadamardSquare [[q (-3) 4, 0], [0, q 5 6]] == 3 ^ 2 * 5 ^ 2 * 6 ^ 2 &&
    SmoothDeclarations.hadamardSquare [[1, 0], [0, 1]] == 1)
#eval check "the matrix bound is 2^metricMatrixBits on the row norms times the largest row denominator"
  (let edge : Nat := 2 ^ Limits.metricMatrixBits
   SmoothDeclarations.matrixBounded [[q (Int.ofNat (edge - 1))]] &&
    !SmoothDeclarations.matrixBounded [[q (Int.ofNat edge)]] &&
    SmoothDeclarations.matrixBounded [[q 1 (edge - 1)]] && !SmoothDeclarations.matrixBounded [[q 1 edge]] &&
    SmoothDeclarations.matrixBounded [[q (Int.ofNat (edge / 2048)), 0], [0, q 1 1024]] &&
    !SmoothDeclarations.matrixBounded [[q (Int.ofNat (edge / 1024)), 0], [0, q 1 1024]])
#eval check "a zero row counts as 1 and does not hide the other rows"
  (SmoothDeclarations.hadamardSquare [[0, 0], [0, 5]] == 25 &&
    !SmoothDeclarations.matrixBounded [[0, 0], [0, q (Int.ofNat (2 ^ Limits.metricMatrixBits))]])

/-- The smooth object `Affine(16)[c0, …, c15]`. -/
private def bigSpace : Source.Declaration := space "Big" 16 ((List.range 16).map fun i => s!"c{i}")

/-- The entries, as numerator and denominator, of a dense symmetric 16 × 16
matrix with pairwise distinct denominators. The entry in row `i` and column
`j ≥ i` has the denominator `d = base + 2 (16 i + j) + 1`. It is `(9 d + 1) / d`
on the diagonal and `1 / d` elsewhere, so the matrix is diagonally dominant.
With `singular`, row and column 15 repeat row and column 0. -/
private def distinctEntries (base : Nat) (singular : Bool) : List (List (Nat × Nat)) :=
  let fold := fun i => if singular && i == 15 then 0 else i
  (List.range 16).map fun i => (List.range 16).map fun j =>
    let low := min (fold i) (fold j)
    let high := max (fold i) (fold j)
    let d := base + 2 * (16 * low + high) + 1
    (if low == high then 9 * d + 1 else 1, d)

private def distinctGram (base : Nat) (singular := false) : Source.MetricGram :=
  .rows <| (distinctEntries base singular).map (·.map fun (a, d) => .fraction (Int.ofNat a) d)

private def distinctMatrix (base : Nat) (singular := false) : SmoothRuntime.Matrix :=
  (distinctEntries base singular).map (·.map fun (a, d) => q (Int.ofNat a) d)

private def matrixLimit : String :=
  "the product of the norms of its rows, cleared of denominators, and of its largest row denominator has " ++
    s!"more than {Limits.metricMatrixBits} bits"

#eval check "a dense metric with distinct 3-digit denominators is certified, with both kinds of evidence"
  (code (with' [bigSpace, metric "Dense" (distinctGram 100) "Big", evidence "E" "Dense" .nondegenerate,
    evidence "R" "Dense" .riemannian]) == "accepted")
#eval check "distinct 63-digit denominators keep every entry within the entry bound"
  ((distinctMatrix (10 ^ 62)).all (·.all SmoothDeclarations.entryBounded) &&
    !SmoothDeclarations.matrixBounded (distinctMatrix (10 ^ 62)))
#eval check "a dense metric with distinct 63-digit denominators is E_LIMIT, with or without evidence"
  (rejectsWith (with' [bigSpace, metric "Dense" (distinctGram (10 ^ 62)) "Big"]) "E_LIMIT"
      "the Gram matrix of the metric `metric::Dense` exceeds the matrix limit" &&
    rejectsWith (with' [bigSpace, metric "Dense" (distinctGram (10 ^ 62)) "Big"]) "E_LIMIT" matrixLimit &&
    rejectsWith (with' [bigSpace, metric "Dense" (distinctGram (10 ^ 62)) "Big", evidence "E" "Dense" .nondegenerate,
      evidence "R" "Dense" .riemannian]) "E_LIMIT" matrixLimit)
-- The order: the same singular matrix is `E_METRIC` when it is small, so a
-- certificate computed before the matrix bound would report `E_METRIC` here.
#eval check "a singular matrix beyond the matrix bound is E_LIMIT, not E_METRIC, with nondegenerate evidence"
  (rejectsWith (with' [bigSpace, metric "Dense" (distinctGram (10 ^ 62) true) "Big",
      evidence "E" "Dense" .nondegenerate]) "E_LIMIT" matrixLimit &&
    rejectsWith (with' [bigSpace, metric "Dense" (distinctGram (10 ^ 62) true) "Big",
      evidence "R" "Dense" .riemannian]) "E_LIMIT" matrixLimit &&
    rejectsWith (with' [bigSpace, metric "Dense" (distinctGram 100 true) "Big", evidence "E" "Dense" .nondegenerate])
      "E_METRIC" "the metric `metric::Dense` is singular, so it has no nondegenerate evidence")
#eval check "the certify functions bound the matrix before they search"
  ((match SmoothDeclarations.certifyNondegenerate 16 (distinctMatrix (10 ^ 62) true) with
    | .error error => error.code == "E_LIMIT"
    | .ok _ => false) &&
    (match SmoothDeclarations.certifyRiemannian 16 (distinctMatrix (10 ^ 62) true) with
    | .error error => error.code == "E_LIMIT"
    | .ok _ => false))

/-! ## One certificate for each metric and kind

Evidence declarations that repeat a metric and a kind carry the certificate
computed for the first of them. A certificate is not shared between two kinds
or between two metrics. -/

private def lookupOf (p : Source.Program) (name : String) : Option Declaration :=
  (resolvedOf p).bind (lookup ·.indexed (id name))

private def repeated : Source.Program := with' [
  evidence "SkewAgain" "Skew" .nondegenerate,
  evidence "SkewPositiveAgain" "Skew" .riemannian,
  evidence "LorentzAgain" "Lorentz" .nondegenerate,
  evidence "SkewThird" "Skew" .nondegenerate ]

#eval check "repeated evidence is accepted" (code repeated == "accepted")
#eval check "repeated evidence carries the certificate of its own metric and kind"
  (lookupOf repeated "SkewAgain" == some (.metricEvidence (id "Skew") (.nondegenerate [[1, -1], [-1, 2]])) &&
    lookupOf repeated "SkewThird" == some (.metricEvidence (id "Skew") (.nondegenerate [[1, -1], [-1, 2]])) &&
    lookupOf repeated "SkewPositiveAgain" ==
      some (.metricEvidence (id "Skew") (.riemannian [[1, 0], [q 1 2, 1]] [2, q 1 2] [[1, 0], [q (-1) 2, 1]])) &&
    lookupOf repeated "LorentzAgain" == some (.metricEvidence (id "Lorentz") (.nondegenerate [[1, 0], [0, -1]])))
#eval check "repeated evidence in the reverse order carries the same certificates"
  (let reversed := program (declarations ++ [evidence "SkewPositiveAgain" "Skew" .riemannian,
     evidence "SkewAgain" "Skew" .nondegenerate]).reverse
   lookupOf reversed "SkewAgain" == some (.metricEvidence (id "Skew") (.nondegenerate [[1, -1], [-1, 2]])) &&
    lookupOf reversed "SkewInvertible" == some (.metricEvidence (id "Skew") (.nondegenerate [[1, -1], [-1, 2]])) &&
    lookupOf reversed "SkewPositive" == lookupOf reversed "SkewPositiveAgain" &&
    (lookupOf reversed "SkewPositive").isSome)
#eval check "a repeated declaration of rejected evidence is still rejected"
  (rejectsWith (with' [evidence "E" "Lorentz" .nondegenerate, evidence "R" "Lorentz" .riemannian,
    evidence "R2" "Lorentz" .riemannian]) "E_METRIC" "the metric `metric::Lorentz` is not positive definite")
#eval check "diag(1, 0) is not nondegenerate"
  (rejectsWith (with' [metric "Diag10" (.rows [[n 1, n 0], [n 0, n 0]]), evidence "E" "Diag10" .nondegenerate])
    "E_METRIC" "the metric `metric::Diag10` is singular, so it has no nondegenerate evidence")
#eval check "diag(1, 0) is also not Riemannian"
  (rejectsWith (with' [metric "Diag10" (.rows [[n 1, n 0], [n 0, n 0]]), evidence "E" "Diag10" .riemannian])
    "E_METRIC" "is not positive definite")
#eval check "diag(1, -1) is nondegenerate but not Riemannian"
  (rejectsWith (with' [evidence "E" "Lorentz" .riemannian]) "E_METRIC"
    "the metric `metric::Lorentz` is not positive definite, so it has no Riemannian evidence" &&
    code (with' [evidence "E" "Lorentz" .nondegenerate]) == "accepted")
#eval check "a metric on a presented object is a foreign-object metric"
  (rejectsWith (with' (presented ++ [metric "Bad" .euclidean "QLine"])) "E_METRIC"
    "the metric `metric::Bad` is on `metric::QLine`, which is not a smooth object")
#eval check "a metric on a marker is a foreign-object metric"
  (rejectsWith (with' [metric "Bad" .euclidean "CInfReal"]) "E_METRIC" "which is not a smooth object")
#eval check "a metric names one object"
  (rejectsWith (with' [decl "Bad" (.metric (path "MetricForm") [path "Plane", path "Plane"] .euclidean)])
    "E_METRIC" "a metric names one object")
#eval check "a metric is declared at a metric_form family"
  (rejectsWith (with' [metric "Bad" .euclidean "Plane" "Cotangent"]) "E_METRIC"
    "a metric is declared at a `metric_form` family, but `metric::Cotangent` is not one")
#eval check "evidence names a metric"
  (rejectsWith (with' [evidence "E" "Plane" .nondegenerate]) "E_METRIC" "`metric::Plane` is not a metric")
#eval check "sharp with evidence for another metric is E_METRIC"
  (rejectsWith (with' [sharp "bad" "Skew" "EuclidInvertible"]) "E_METRIC"
    "`sharp` uses the metric `metric::Skew`, but the evidence `metric::EuclidInvertible` certifies `metric::Euclid`")
#eval check "sharp with Riemannian evidence is the wrong kind"
  (rejectsWith (with' [sharp "bad" "Skew" "SkewPositive"]) "E_METRIC"
    "`sharp` needs nondegenerate evidence, but `metric::SkewPositive` is Riemannian evidence")
#eval check "sharp with a non-evidence is E_METRIC"
  (rejectsWith (with' [sharp "bad" "Skew" "Skew"]) "E_METRIC" "`metric::Skew` is not evidence")
#eval check "flat and sharp need a metric after using ="
  (rejectsWith (with' [flat "bad" "Plane"]) "E_METRIC" "`flat` needs a metric after `using =`" &&
    rejectsWith (with' [sharp "bad" "SkewInvertible" "SkewInvertible"]) "E_METRIC"
      "`sharp` needs a metric after `using =`")
#eval check "flat and sharp need families of the right variance"
  (rejectsWith (with' [primitive "bad"
      ⟨"flat", [ref "tangent" "Cotangent", ref "cotangent" "Cotangent", ref "metric" "Skew"]⟩]) "E_SMOOTH"
    "`flat` needs a tangent family" &&
    rejectsWith (with' [primitive "bad" ⟨"sharp", [ref "cotangent" "Cotangent", ref "tangent" "Cotangent",
      ref "metric" "Skew", ref "evidence" "SkewInvertible"]⟩]) "E_SMOOTH" "`sharp` needs a tangent family")
#eval check "flat and sharp that name a family that is not a tangent or cotangent family are E_TYPE"
  (code (with' [primitive "bad"
      ⟨"flat", [ref "tangent" "Smooth", ref "cotangent" "Cotangent", ref "metric" "Skew"]⟩]) == "E_TYPE" &&
    code (with' [primitive "bad"
      ⟨"flat", [ref "tangent" "Tangent", ref "cotangent" "MetricForm", ref "metric" "Skew"]⟩]) == "E_TYPE" &&
    code (with' [primitive "bad" ⟨"sharp", [ref "cotangent" "Smooth", ref "tangent" "Tangent", ref "metric" "Skew",
      ref "evidence" "SkewInvertible"]⟩]) == "E_TYPE")
#eval check "metric form families need exactly one canonical constraint over smooth objects"
  (code (replacing "MetricForm" (family "MetricForm" .metricForm 1 [])) == "E_TYPE" &&
    code (replacing "MetricForm" (family "MetricForm" .metricForm 2 [.canonical 0, .canonical 1])) == "E_TYPE" &&
    code (with' (presented ++ [decl "BadForm" (.family ⟨[.object (path "AffineScheme")], [.canonical 0],
      .metricForm⟩)])) == "E_TYPE")

/-! ## The order in which `flat` and `sharp` resolve their names

The resolver resolves the metric of `flat` first, and the metric and then the
evidence of `sharp`, and then the other fields in wire order. The first name
that does not resolve is the one reported, so with two such names the metric,
and then the evidence, is reported before a tangent or cotangent family; the
references of a resolved form are recorded in the same order. The forms are
the ones `flat` and `sharp` above build. -/

/-- The source form of a primitive declaration. -/
private def form? (declaration : Source.Declaration) : Option Source.Primitive :=
  match declaration.body with
  | .primitive binding => some binding
  | _ => none

private def flatForm : Option Source.Primitive := form? (flat "flat_skew" "Skew")
private def sharpForm : Option Source.Primitive := form? (sharp "sharp_skew" "Skew" "SkewInvertible")

/-- The form with the paths of `fields` replaced by names that no declaration
has: `MissingMetric` for the field `metric`, and so on. -/
private def breaking (fields : List String) (form : Source.Primitive) : Source.Primitive :=
  { form with arguments := form.arguments.map fun (field, argument) =>
      if fields.contains field then ref field ("Missing" ++ field.capitalize) else (field, argument) }

private def metricIndex : Namespace.Indexed := (program declarations).indexed
private def metricScope : Namespace.Scope := ⟨pkg, []⟩

/-- The code and the message the resolver reports for a form. -/
private def reported (form : Option Source.Primitive) : Option (String × String) :=
  form.bind fun form => match (Source.resolvePrimitive metricIndex metricScope form).run [] with
    | .ok _ => none
    | .error diagnostic => some (diagnostic.code, diagnostic.message)

/-- The paths of a resolved form's references, in the order they are
recorded; `resolveId` puts each one first, and `Source.lower` reverses them. -/
private def recorded (form : Option Source.Primitive) : Option (List (List String)) :=
  form.bind fun form => match (Source.resolvePrimitive metricIndex metricScope form).run [] with
    | .ok (_, references) => some (references.reverse.map (·.path.path))
    | .error _ => none

private def undefinedName (name : String) : Option (String × String) :=
  some ("E_NAME", s!"undefined name '{name}' in this module")

#eval check "the families resolve the metric, then the evidence, first"
  ((primitiveFamily? "flat").map (·.resolutionOrder) == some ["metric", "tangent", "cotangent"] &&
    (primitiveFamily? "sharp").map (·.resolutionOrder) == some ["metric", "evidence", "cotangent", "tangent"])
#eval check "flat records the metric, the tangent family and the cotangent family, in that order"
  (recorded flatForm == some [["Skew"], ["Tangent"], ["Cotangent"]])
#eval check "sharp records the metric, the evidence, the cotangent family and the tangent family, in that order"
  (recorded sharpForm == some [["Skew"], ["SkewInvertible"], ["Cotangent"], ["Tangent"]])
#eval check "flat with two unresolvable names reports its metric before a family"
  (reported (flatForm.map (breaking ["tangent", "metric"])) == undefinedName "MissingMetric" &&
    reported (flatForm.map (breaking ["cotangent", "metric"])) == undefinedName "MissingMetric" &&
    reported (flatForm.map (breaking ["tangent", "cotangent"])) == undefinedName "MissingTangent")
#eval check "sharp with two unresolvable names reports its metric, then its evidence, before a family"
  (reported (sharpForm.map (breaking ["tangent", "metric"])) == undefinedName "MissingMetric" &&
    reported (sharpForm.map (breaking ["cotangent", "metric"])) == undefinedName "MissingMetric" &&
    reported (sharpForm.map (breaking ["metric", "evidence"])) == undefinedName "MissingMetric" &&
    reported (sharpForm.map (breaking ["cotangent", "evidence"])) == undefinedName "MissingEvidence" &&
    reported (sharpForm.map (breaking ["tangent", "evidence"])) == undefinedName "MissingEvidence" &&
    reported (sharpForm.map (breaking ["cotangent", "tangent"])) == undefinedName "MissingCotangent")
#eval check "the source checker reports the same name"
  (match flatForm, sharpForm with
    | some flatSource, some sharpSource =>
      rejectsWith (with' [primitive "bad" (breaking ["tangent", "metric"] flatSource)]) "E_NAME"
          "undefined name 'MissingMetric' in this module" &&
        rejectsWith (with' [primitive "bad" (breaking ["cotangent", "evidence"] sharpSource)]) "E_NAME"
          "undefined name 'MissingEvidence' in this module"
    | _, _ => false)

/-! ## Tampered Core: the independent audit rechecks every metric -/

private def tamper (extra : PrimitiveBinding) : Bool :=
  match resolved with
  | some env => !Core.validDeclarations { env with primitives := env.primitives ++ [⟨id "bad", extra⟩] }
  | none => false
private def tamperIndexed (edit : Environment → Environment) : Bool :=
  match resolved with
  | some env => !Core.validDeclarations { env with indexed := edit env.indexed }
  | none => false
private def forged (name : String) (declaration : Declaration) (env : Environment) : Environment :=
  env.map fun entry => if entry.id == id name then ⟨entry.id, declaration⟩ else entry

#eval check "accepted Core is valid" (resolved.map Core.validDeclarations == some true)
#eval check "a sharp whose inverse is not the evidence's inverse is rejected"
  (tamper (.metricSharp (id "Skew") (id "SkewInvertible") (id "Plane") [[2, 1], [1, 1]] [[1, 0], [0, 1]]
    (id "Cotangent") (id "Tangent")) &&
    tamper (.metricSharp (id "Skew") (id "EuclidInvertible") (id "Plane") [[2, 1], [1, 1]] [[1, 0], [0, 1]]
      (id "Cotangent") (id "Tangent")))
#eval check "a sharp naming Riemannian evidence is rejected"
  (tamper (.metricSharp (id "Skew") (id "SkewPositive") (id "Plane") [[2, 1], [1, 1]] [[1, -1], [-1, 2]]
    (id "Cotangent") (id "Tangent")))
#eval check "an embedded Gram matrix that differs from the declaration is rejected"
  (tamper (.metricFlat (id "Skew") (id "Plane") [[1, 0], [0, 1]] (id "Tangent") (id "Cotangent")) &&
    tamper (.metricSharp (id "Skew") (id "SkewInvertible") (id "Plane") [[1, 0], [0, 1]] [[1, -1], [-1, 2]]
      (id "Cotangent") (id "Tangent")))
#eval check "an embedded object that differs from the metric's is rejected"
  (tamper (.metricFlat (id "Skew") (id "Line") [[2, 1], [1, 1]] (id "Tangent") (id "Cotangent")))
#eval check "flat and sharp with swapped variances are rejected"
  (tamper (.metricFlat (id "Skew") (id "Plane") [[2, 1], [1, 1]] (id "Cotangent") (id "Tangent")) &&
    tamper (.metricSharp (id "Skew") (id "SkewInvertible") (id "Plane") [[2, 1], [1, 1]] [[1, -1], [-1, 2]]
      (id "Tangent") (id "Cotangent")))
#eval check "flat naming evidence instead of a metric is rejected"
  (tamper (.metricFlat (id "SkewInvertible") (id "Plane") [[2, 1], [1, 1]] (id "Tangent") (id "Cotangent")))
/-- Append one forged entry with a fresh id. No binding names it, so only the
entry's own check in the declaration audit can reject it. -/
private def appended (declaration : Declaration) : Bool :=
  tamperIndexed (· ++ [⟨id "Forged", declaration⟩])
#eval check "a fresh, correct metric and certificate are accepted, so the forgeries below fail on their data"
  (!appended (.metricEvidence (id "Skew") (.nondegenerate [[1, -1], [-1, 2]])) &&
    !appended (.metricEvidence (id "Skew") (.riemannian [[1, 0], [q 1 2, 1]] [2, q 1 2] [[1, 0], [q (-1) 2, 1]])) &&
    !appended (.metric (id "MetricForm") (id "Plane") [[2, 1], [1, 1]]))
#eval check "evidence whose inverse fails G B = I is rejected"
  (appended (.metricEvidence (id "Skew") (.nondegenerate [[1, 0], [0, 1]])) &&
    appended (.metricEvidence (id "Skew") (.nondegenerate [[1, -1], [-1, 2], [0, 0]])))
#eval check "singular evidence is rejected"
  (appended (.metricEvidence (id "Euclid") (.nondegenerate [[1, 0], [0, 0]])))
#eval check "Riemannian evidence with a pivot that is not positive is rejected"
  (appended (.metricEvidence (id "Lorentz") (.riemannian [[1, 0], [0, 1]] [1, -1] [[1, 0], [0, 1]])) &&
    appended (.metricEvidence (id "Skew") (.riemannian [[1, 0], [q 1 2, 1]] [2, 0] [[1, 0], [q (-1) 2, 1]])))
#eval check "Riemannian evidence whose factors do not multiply to G is rejected"
  (appended (.metricEvidence (id "Skew") (.riemannian [[1, 0], [0, 1]] [2, 1] [[1, 0], [0, 1]])))
#eval check "evidence that names a non-metric is rejected"
  (appended (.metricEvidence (id "Plane") (.nondegenerate [[1, 0], [0, 1]])))
#eval check "a forged asymmetric, wrong-size, unbounded or foreign metric is rejected"
  (appended (.metric (id "MetricForm") (id "Plane") [[2, 1], [0, 1]]) &&
    appended (.metric (id "MetricForm") (id "Plane") [[2]]) &&
    appended (.metric (id "MetricForm") (id "Plane") [[(2 ^ 512 : Nat), 0], [0, 1]]) &&
    appended (.metric (id "MetricForm") (id "CInfReal") [[2, 1], [1, 1]]) &&
    appended (.metric (id "Cotangent") (id "Plane") [[2, 1], [1, 1]]))
/-- Append one forged entry to the declarations of the program with the
16-dimensional object `Big`. -/
private def appendedBig (declaration : Declaration) : Bool :=
  match resolvedOf (with' [bigSpace]) with
  | some env => !Core.validDeclarations { env with indexed := env.indexed ++ [⟨id "Forged", declaration⟩] }
  | none => false
#eval check "a forged metric beyond the matrix bound, with every entry within the entry bound, is rejected"
  (!appendedBig (.metric (id "MetricForm") (id "Big") (distinctMatrix 100)) &&
    appendedBig (.metric (id "MetricForm") (id "Big") (distinctMatrix (10 ^ 62))))

/-! ## The compiled audit checks each distinct evidence declaration once

`validEnvironment` compiles to `validEnvironmentOnce`. Equal evidence
declarations share one check, and a declaration that differs has its own. -/

/-- `validEnvironment`, written out so that it compiles as it reads. -/
private def reference (env : Environment) : Bool :=
  decide (env.length ≤ 4096) && decide (env.map Entry.id).Nodup && env.all (validEntry env (classRanks env))

/-- The declarations of the program with these entries appended. -/
private def extended (entries : List (String × Declaration)) : Option Environment :=
  resolved.map fun env => env.indexed ++ entries.map fun (name, declaration) => (⟨id name, declaration⟩ : Entry)

private def skewInverse : Declaration := .metricEvidence (id "Skew") (.nondegenerate [[1, -1], [-1, 2]])
private def skewForged : Declaration := .metricEvidence (id "Skew") (.nondegenerate [[1, 0], [0, 1]])

#eval check "the compiled audit and the reference agree on repeated and forged evidence"
  ([[], [("A", skewInverse)], [("A", skewInverse), ("B", skewInverse)], [("A", skewForged)],
      [("A", skewInverse), ("B", skewForged)], [("A", skewForged), ("B", skewInverse)],
      [("A", skewInverse), ("B", skewInverse), ("C", skewForged)], [("A", skewInverse), ("A", skewInverse)]].all
    fun entries => (extended entries).map validEnvironmentOnce == (extended entries).map reference &&
      (extended entries).map validEnvironment == (extended entries).map reference &&
      (extended entries).isSome)
#eval check "equal evidence declarations are accepted, and a forged one after them is rejected"
  ((extended [("A", skewInverse), ("B", skewInverse)]).map validEnvironment == some true &&
    (extended [("A", skewInverse), ("B", skewInverse), ("C", skewForged)]).map validEnvironment == some false &&
    (extended [("A", skewForged), ("B", skewInverse)]).map validEnvironment == some false)
#eval check "a forged metric form family is rejected"
  (tamperIndexed (forged "MetricForm" (.family ⟨[.object (id "CInfAffine")], [], .metricForm⟩)))

/-! ## Metric declarations leave the metric-free program unchanged

The generated code of a program that uses `differential` is byte-identical
with and without the metric, evidence, `flat` and `sharp` declarations. -/

private def differentialMain : Core.Function := {
  id := 0, definition := id "main", parameters := [], returnType := .pure .int
  body := guarded (sameCovector dg (dplane p 2 1)) 1 (.integer 42) }

private def generated (ds : List Source.Declaration) : Option String := do
  let env ← resolvedOf (program ds)
  let .ok checked := Core.Typing.checkModule ⟨env, [differentialMain], some 0⟩ true | none
  (Core.Codegen.generate checked).toOption

#eval check "metric declarations do not change the generated code of a differential"
  (generated metricFree == generated declarations && (generated metricFree).isSome)
#eval check "metric declarations do not change the differential's value"
  (match resolvedOf (program metricFree), resolved with
  | some free, some withMetrics =>
    Core.Semantics.eval ⟨free, [differentialMain], some 0⟩ 64 (fun _ => none) dg ==
      Core.Semantics.eval ⟨withMetrics, [differentialMain], some 0⟩ 64 (fun _ => none) dg
  | _, _ => false)

/-! ## Protocols 7 and 8 do not admit the metric forms; protocol 9 does -/

open Lean in
private def decodes (j : Json) (algebraic : Bool) : Bool :=
  (Wire.declarationBody j (numerical := true) (algebraic := algebraic)).isOk
open Lean in
private def spanJson : Json :=
  Json.mkObj [("start", (0 : Nat)), ("end", (0 : Nat)), ("line", (1 : Nat)), ("column", (1 : Nat))]
open Lean in
private def pathJson (name : String) : Json :=
  Json.mkObj [("path", Json.arr #[Json.str name]), ("span", spanJson)]
open Lean in
private def common (kind : String) : List (String × Json) :=
  [("kind", Json.str kind), ("name", Json.str "X"), ("public", Json.bool true), ("span", spanJson)]
open Lean in
private def primitiveJson (fields : List (String × Json)) : Json := Json.mkObj (common "primitive" ++
  [("binding", Json.mkObj fields)])
open Lean in
private def natural (value : Nat) : Json := Json.mkObj [("op", "natural"), ("value", Json.str (toString value))]
open Lean in
private def gramJson : Json := Json.mkObj [("kind", "gram"),
  ("rows", Json.arr #[Json.arr #[natural 2, natural 1], Json.arr #[natural 1, natural 1]])]
open Lean in
private def metricJson (gram : Json) (extra : List (String × Json) := []) : Json := Json.mkObj (common "metric" ++
  [("family", pathJson "MetricForm"), ("indices", Json.arr #[pathJson "Plane"]), ("gram", gram)] ++ extra)
open Lean in
private def evidenceJson (kind : String) (extra : List (String × Json) := []) : Json :=
  Json.mkObj (common "evidence" ++ [("metric", pathJson "Skew"), ("evidence", Json.str kind)] ++ extra)
open Lean in
private def flatJson (extra : List (String × Json) := []) : Json := primitiveJson ([("op", Json.str "flat"),
  ("tangent", pathJson "Tangent"), ("cotangent", pathJson "Cotangent"), ("metric", pathJson "Skew")] ++ extra)
open Lean in
private def sharpJson (extra : List (String × Json) := []) : Json := primitiveJson ([("op", Json.str "sharp"),
  ("cotangent", pathJson "Cotangent"), ("tangent", pathJson "Tangent"), ("metric", pathJson "Skew"),
  ("evidence", pathJson "SkewInvertible")] ++ extra)
open Lean in
private def forms : List Json := [
  metricJson gramJson, metricJson (Json.mkObj [("kind", "euclidean")]), evidenceJson "nondegenerate",
  evidenceJson "riemannian", flatJson, sharpJson,
  Json.mkObj (common "family" ++ [("parameters", Json.arr #[]), ("constraints", Json.arr #[]),
    ("representation", Json.str "metric_form")])]

#eval check "protocol 9 decodes each metric form" (forms.all (decodes · true))
#eval check "protocols 7 and 8 reject each metric form" (forms.all (!decodes · false))
open Lean in
private def matrixJson : Json := Json.arr #[Json.arr #[Json.str "1", Json.str "0"], Json.arr #[Json.str "0", Json.str "1"]]
open Lean in
#eval check "the wire carries no certificate or matrix"
  (!decodes (evidenceJson "nondegenerate" [("inverse", matrixJson)]) true &&
    !decodes (evidenceJson "riemannian" [("lower", matrixJson), ("pivots", Json.arr #[]),
      ("lower_inverse", matrixJson)]) true &&
    !decodes (metricJson gramJson [("inverse", matrixJson)]) true &&
    !decodes (metricJson (Json.mkObj [("kind", "euclidean"), ("rows", Json.arr #[])])) true &&
    !decodes (flatJson [("gram", matrixJson)]) true &&
    !decodes (sharpJson [("inverse", matrixJson)]) true &&
    !decodes (sharpJson [("object", pathJson "Plane")]) true)
open Lean in
#eval check "flat and sharp records name their metric and evidence"
  (!decodes (primitiveJson [("op", Json.str "flat"), ("tangent", pathJson "Tangent"),
      ("cotangent", pathJson "Cotangent")]) true &&
    !decodes (primitiveJson [("op", Json.str "sharp"), ("cotangent", pathJson "Cotangent"),
      ("tangent", pathJson "Tangent"), ("evidence", pathJson "SkewInvertible")]) true &&
    !decodes (primitiveJson [("op", Json.str "sharp"), ("cotangent", pathJson "Cotangent"),
      ("tangent", pathJson "Tangent"), ("metric", pathJson "Skew")]) true)
open Lean in
#eval check "metric and evidence records carry their Gram matrix and metric"
  (!decodes (Json.mkObj (common "metric" ++ [("family", pathJson "MetricForm"),
      ("indices", Json.arr #[pathJson "Plane"])])) true &&
    !decodes (Json.mkObj (common "evidence" ++ [("evidence", Json.str "nondegenerate")])) true &&
    !decodes (Json.mkObj (common "evidence" ++ [("metric", pathJson "Skew")])) true)
#eval check "evidence is nondegenerate or riemannian"
  (["positive", "lorentzian", "nondegenerate_", ""].all fun kind => !decodes (evidenceJson kind) true)
open Lean in
#eval check "a Gram matrix is euclidean or explicit rows"
  (!decodes (metricJson (Json.mkObj [("kind", "identity")])) true &&
    !decodes (metricJson (Json.mkObj [("kind", "gram"), ("rows", Json.arr #[Json.str "1"])])) true)
open Lean in
#eval check "the allow-list has no gradient or metric operation besides flat and sharp"
  (["gradient", "metric_gradient", "flat_", "sharp_", "metric", "musical", "metric_flat"].all fun op =>
    !decodes (primitiveJson [("op", Json.str op), ("metric", pathJson "Skew")]) true)

end VastitasKernel.Indexed.MetricFormRegression
