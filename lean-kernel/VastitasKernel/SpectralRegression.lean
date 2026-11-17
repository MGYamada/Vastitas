import VastitasKernel.IndexedSourceChecker
import VastitasKernel.IndexedDeclarationProtocol
import VastitasKernel.IndexedCodegen
import VastitasKernel.IndexedReverse
import VastitasKernel.IndexedSemantics
import VastitasKernel.RegressionSupport

set_option autoImplicit false

/-! The spectral bindings (Stage 5, #806) through the actual common source
checker, the independent declaration and Core audits, the role table of a
rejected call, the Core semantics and its erasure, code generation and the
protocol decoder. These are executable regressions, not proofs.

On the plane `Plane = Affine(2)[x, y]`: `H = rows((x, y), (y, −x))` on
`V = basis(e1, e2)`, declared `symmetric`, its spectrum `S = eigen(H, t)` with
`χ = t² − x² − y²` and `adj(tI − H) = tI + H`, and the branch `B` on
`D(x² + y²)` with witness `t/2`. On the point `Pt`, the four constant
endomorphisms `0`, `N = [[0, 1], [0, 0]]`, `2I` and `J = [[2, 1], [0, 2]]` of
`W2 = basis(f1, f2)` and their spectra. The invariants `tr1`, `tr2` and `c0`
are smooth maps `Plane → Line`, and `ref2 = pullback(s -> 2x² + 2y²)` is the
declared reference.

`spectralFixture` checks, in one Core module that returns 42:

- the module action (C3): `0`/`N` and `2I`/`J` have the same trace powers
  and characteristic coefficients, but `annihilates(t)`, `annihilates(t − 2)`
  and `action_entry(t − 2, f1, f2)` tell them apart, and `(t − 2)²`
  annihilates both (Cayley–Hamilton);
- the invariants as smooth maps (C4): `tr2` equals `ref2`, `d tr1 = 0` (a
  covector, not the failure value) and `d c0 = −½ d tr2`;
- the roadmap gradient (C5): `d tr2 = (4x, 4y)` at `(1, 2)`, `(3, 4)` and the
  origin, and the Euclidean `sharp` of it is the vector `(4x, 4y)`;
- the branch points (C9): `((3, 4), ±5)` and `((1, 0), ±1)` are on `B`,
  `((3, 4), 4)` is not, nor is the origin with `t = 0`, though `χ(0, 0) = 0`;
- the branch derivative (C10): `dλ = ±(3/5, 4/5)` at `(3, 4)`, `±(1, 0)` at
  `(1, 0)`, a unit covector under the Euclidean metric, and the failure
  value off the branch;
- the eigenprojectors (C11): `(1/5)[[4, 2], [2, 1]]` and
  `(1/5)[[1, −2], [−2, 4]]` at `(3, 4)`, `[[1, 0], [0, 0]]` at `((1, 0), 1)`,
  and `(0, 0)` off the branch.

The native fixture script compiles it, and its compiled reverse Core, whose
differentials of `tr2` and `c0` pull back along the invariants' maps
(`ReverseRule.morphism`). -/
namespace VastitasKernel.Indexed.SpectralRegression

open AlgebraRuntime

private def pkg : Namespace.PackageId := ⟨"/spectral/Vastitas.toml", "spectral", "0.1.0"⟩
private def id (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩
private def path (name : String) : Source.Path := ⟨[name], {}⟩
private def decl (name : String) (body : Source.Body) : Source.Declaration := ⟨name, body, true, {}⟩
private def c (name : String) : Source.PolyExpr := .coordinate name
private def n (value : Nat) : Source.PolyExpr := .natural value
private def neg (e : Source.PolyExpr) : Source.PolyExpr := .neg e
private def sq (e : Source.PolyExpr) : Source.PolyExpr := .pow e 2
private def space (name : String) (coordinates : List String) : Source.Declaration :=
  decl name (.smoothAffine (path "SmoothR") coordinates.length coordinates)
private def objectFamily (name : String) (representation : FamilyRepresentation) (arity : Nat := 1)
    (constraints : List Constraint := [.canonical 0]) : Source.Declaration :=
  decl name (.family ⟨(List.range arity).map fun _ => .object (path "CInfAffine"), constraints, representation⟩)
private def ref (field name : String) : String × Source.WireArgument := (field, .path (path name))
private def primitive (name : String) (binding : Source.Primitive) : Source.Declaration :=
  decl name (.primitive binding)
private def morphism (name x y : String) (definition : Source.MorphismDefinition) : Source.Declaration :=
  decl name (.morphism (path "Smooth") [path x, path y] definition)

private def freeModule (name object : String) (basis : List String) : Source.Declaration :=
  decl name (.freeModule (path "FreeModule") [path object] basis)
private def endomorphism (name object module : String) (rows : List (List Source.PolyExpr)) (symmetric : Bool) :
    Source.Declaration :=
  decl name (.endomorphism (path "Endomorphism") [path object] (path module) rows symmetric)
private def spectrum (name object endo : String) : Source.Declaration :=
  decl name (.spectrum (path "Spectrum") [path object] (path endo) "t")

private def annihilates (name spec : String) (element : Source.PolyExpr) : Source.Declaration :=
  primitive name ⟨"annihilates", [ref "map_family" "Smooth", ref "spectrum" spec, ("element", .polynomial element)]⟩
private def actionEntry (name spec : String) (element : Source.PolyExpr) (row column : String) :
    Source.Declaration :=
  primitive name ⟨"action_entry", [ref "map_family" "Smooth", ref "spectrum" spec,
    ("element", .polynomial element), ("row", .coordinate row), ("column", .coordinate column)]⟩
private def onBranch (name : String) (maps := "Smooth") (line := "Line") (branch := "B") : Source.Declaration :=
  primitive name ⟨"on_branch", [ref "map_family" maps, ref "line" line, ref "branch" branch]⟩
private def branchDifferential (name : String) (cotangent := "Cotangent") (line := "Line") (branch := "B") :
    Source.Declaration :=
  primitive name ⟨"branch_differential", [ref "map_family" "Smooth", ref "cotangent" cotangent, ref "line" line,
    ref "branch" branch]⟩
private def branchProjector (name row column : String) : Source.Declaration :=
  primitive name ⟨"branch_projector", [ref "map_family" "Smooth", ref "line" "Line", ref "branch" "B",
    ("row", .coordinate row), ("column", .coordinate column)]⟩

private def tMinus2 : Source.PolyExpr := .sum [c "t", neg (n 2)]

/-- The smooth profile with the spectral and metric families, and the objects. -/
private def base : List Source.Declaration := [
  decl "CInfReal" .marker,
  decl "SmoothR" (.implementation (path "CInfReal") .smoothAffine []),
  decl "CInfAffine" (.classification [] [path "SmoothR"]),
  objectFamily "Smooth" .smooth 2 [.canonical 0, .canonical 1],
  objectFamily "Tangent" (.fiber .tangent),
  objectFamily "Cotangent" (.fiber .cotangent),
  objectFamily "MetricForm" .metricForm,
  objectFamily "FreeModule" .freeModule,
  objectFamily "Endomorphism" .endomorphism,
  objectFamily "Spectrum" .spectrum,
  objectFamily "Branch" .branch,
  space "Pt" [],
  space "Line" ["s"],
  space "Plane" ["x", "y"],
  decl "Euclid" (.metric (path "MetricForm") [path "Plane"] .euclidean),
  decl "EuclidInvertible" (.evidence (path "Euclid") .nondegenerate)]

/-- The spectral declarations: the Stage 5 field on the plane and the four
constant endomorphisms on the point. -/
private def spectral : List Source.Declaration := [
  freeModule "V" "Plane" ["e1", "e2"],
  endomorphism "H" "Plane" "V" [[c "x", c "y"], [c "y", neg (c "x")]] true,
  spectrum "S" "Plane" "H",
  decl "B" (.branch (path "Branch") [path "Plane"] (path "S") (.sum [sq (c "x"), sq (c "y")])
    (.product [.fraction 1 2, c "t"]) 1),
  freeModule "W2" "Pt" ["f1", "f2"],
  endomorphism "Z" "Pt" "W2" [[n 0, n 0], [n 0, n 0]] true,
  endomorphism "N" "Pt" "W2" [[n 0, n 1], [n 0, n 0]] false,
  endomorphism "I2" "Pt" "W2" [[n 2, n 0], [n 0, n 2]] true,
  endomorphism "J" "Pt" "W2" [[n 2, n 1], [n 0, n 2]] false,
  spectrum "SZ" "Pt" "Z", spectrum "SN" "Pt" "N", spectrum "SI" "Pt" "I2", spectrum "SJ" "Pt" "J"]

/-- The invariants and the reference map. -/
private def invariants : List Source.Declaration := [
  morphism "tr1" "Plane" "Line" (.tracePower (path "H") 1),
  morphism "tr2" "Plane" "Line" (.tracePower (path "H") 2),
  morphism "c0" "Plane" "Line" (.charCoefficient (path "S") 0),
  morphism "ref2" "Plane" "Line"
    (.pullback [("s", .sum [.product [n 2, sq (c "x")], .product [n 2, sq (c "y")]])]),
  morphism "trZ" "Pt" "Line" (.tracePower (path "Z") 2), morphism "trN" "Pt" "Line" (.tracePower (path "N") 2),
  morphism "trI" "Pt" "Line" (.tracePower (path "I2") 2), morphism "trJ" "Pt" "Line" (.tracePower (path "J") 2),
  morphism "cZ" "Pt" "Line" (.charCoefficient (path "SZ") 0),
  morphism "cN" "Pt" "Line" (.charCoefficient (path "SN") 0),
  morphism "cI" "Pt" "Line" (.charCoefficient (path "SI") 1),
  morphism "cJ" "Pt" "Line" (.charCoefficient (path "SJ") 1)]

/-- The smooth, fiber and metric primitives that the checks use. -/
private def smoothPrimitives : List Source.Declaration := [
  primitive "plane_at" ⟨"smooth_int_point", [ref "family" "Smooth", ref "object" "Plane", ref "point" "Pt"]⟩,
  primitive "line_at" ⟨"smooth_int_point", [ref "family" "Smooth", ref "object" "Line", ref "point" "Pt"]⟩,
  primitive "pt_at" ⟨"smooth_int_point", [ref "family" "Smooth", ref "object" "Pt", ref "point" "Pt"]⟩,
  primitive "same_smooth" ⟨"smooth_equal", [ref "family" "Smooth"]⟩,
  primitive "vplane" ⟨"fiber_vector", [ref "family" "Tangent", ref "map_family" "Smooth", ref "object" "Plane"]⟩,
  primitive "dplane" ⟨"fiber_vector", [ref "family" "Cotangent", ref "map_family" "Smooth", ref "object" "Plane"]⟩,
  primitive "same_vector" ⟨"fiber_equal", [ref "family" "Tangent"]⟩,
  primitive "same_covector" ⟨"fiber_equal", [ref "family" "Cotangent"]⟩,
  primitive "dx" ⟨"fiber_component", [ref "family" "Cotangent", ref "object" "Plane", ("coordinate", .coordinate "x")]⟩,
  primitive "dy" ⟨"fiber_component", [ref "family" "Cotangent", ref "object" "Plane", ("coordinate", .coordinate "y")]⟩,
  primitive "pairing" ⟨"fiber_pairing", [ref "cotangent" "Cotangent", ref "tangent" "Tangent"]⟩,
  primitive "differential" ⟨"differential", [ref "map_family" "Smooth", ref "cotangent" "Cotangent",
    ref "line" "Line"]⟩,
  primitive "sharp_euclid" ⟨"sharp", [ref "cotangent" "Cotangent", ref "tangent" "Tangent", ref "metric" "Euclid",
    ref "evidence" "EuclidInvertible"]⟩,
  morphism "toPlane" "Line" "Plane" (.pullback [("x", c "s"), ("y", sq (c "s"))]),
  morphism "idLine" "Line" "Line" .identity]

/-- One binding of every spectral observation, most of them several times. -/
private def observations : List Source.Declaration := [
  annihilates "annZ" "SZ" (c "t"), annihilates "annN" "SN" (c "t"),
  annihilates "annI" "SI" tMinus2, annihilates "annJ" "SJ" tMinus2,
  annihilates "annJ2" "SJ" (sq tMinus2), annihilates "annN2" "SN" (sq (c "t")),
  actionEntry "actZ" "SZ" (c "t") "f1" "f2", actionEntry "actN" "SN" (c "t") "f1" "f2",
  actionEntry "actI" "SI" tMinus2 "f1" "f2", actionEntry "actJ" "SJ" tMinus2 "f1" "f2",
  -- An element that involves the coordinates: (t − x)(H(p)) = H(p) − p₀ I.
  actionEntry "actH" "S" (.sum [c "t", neg (c "x")]) "e2" "e2",
  onBranch "on", branchDifferential "dl",
  branchProjector "p11" "e1" "e1", branchProjector "p12" "e1" "e2", branchProjector "p21" "e2" "e1",
  branchProjector "p22" "e2" "e2"]

private def declarations : List Source.Declaration := base ++ spectral ++ invariants ++ smoothPrimitives ++ observations

private def program (ds := declarations) : Source.Program := {
  file := "spectral", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := {path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {}}
    declarations := ds }], none⟩] }

private def check := RegressionSupport.check "spectral regression failed"

private def with' (extra : List Source.Declaration) : Source.Program := program (declarations ++ extra)

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

private def endoRef (name : String) : EndoRef := (Source.endoRef? env.indexed (id name)).getD default
private def spectrumRef (name : String) : SpectrumRef := (Source.spectrumRef? env.indexed (id name)).getD default
private def branchRef (name : String) : BranchRef := (Source.branchRef? env.indexed (id name)).getD default

private def q (numerator : Int) (denominator : Nat := 1) : Rat := mkRat numerator denominator
private def x : Poly := Poly.var 2 0
private def y : Poly := Poly.var 2 1
private def lineMap : Application := ⟨id "Smooth", [.object (.global (id "Plane")), .object (.global (id "Line"))]⟩
/-- `x² + y²` on the plane. -/
private def gap : Poly := Poly.add (Poly.mul x x) (Poly.mul y y)

#eval check "the common source checker accepts the spectral declarations, invariants and observations"
  (code program == "accepted")
#eval check "declaration order independent" (code (program declarations.reverse) == "accepted")
#eval check "the profile without observations or invariants is accepted on its own"
  (code (program (base ++ spectral ++ smoothPrimitives)) == "accepted")

/-! ## The bindings embed their declarations -/

#eval check "the embedded declarations are the kernel's: H, χ = t² − x² − y², g = x² + y², W = t/2"
  ((endoRef "H").rows == [[x, y], [y, Poly.neg x]] && (endoRef "H").symmetric && (endoRef "H").module == id "V" &&
    (spectrumRef "S").endomorphism == endoRef "H" &&
    (spectrumRef "S").characteristic ==
      Poly.sub (Poly.mul (Poly.var 3 2) (Poly.var 3 2)) (Poly.add (Poly.mul (Poly.var 3 0) (Poly.var 3 0))
        (Poly.mul (Poly.var 3 1) (Poly.var 3 1))) &&
    (branchRef "B").spectrum == spectrumRef "S" && (branchRef "B").localize == gap &&
    (branchRef "B").witness == Poly.scale (1 / 2) (Poly.var 3 2) && (branchRef "B").exponent == 1)
#eval check "an invariant is a smooth map with its exact image and its provenance"
  (binding "tr2" == some (.spectralInvariant lineMap ⟨2, [], [Poly.scale 2 gap]⟩ (.tracePower (endoRef "H") 2)) &&
    binding "c0" == some (.spectralInvariant lineMap ⟨2, [], [Poly.neg gap]⟩ (.charCoefficient (spectrumRef "S") 0)) &&
    binding "tr1" == some (.spectralInvariant lineMap ⟨2, [], [[]]⟩ (.tracePower (endoRef "H") 1)))
#eval check "each observation embeds its spectrum or branch, its element and its basis indices"
  (binding "annI" == some (.annihilates (id "Smooth") (spectrumRef "SI") (Poly.sub (Poly.var 1 0) (Poly.const 1 2))) &&
    binding "actJ" == some (.actionEntry (id "Smooth") (spectrumRef "SJ")
      (Poly.sub (Poly.var 1 0) (Poly.const 1 2)) 0 1) &&
    binding "on" == some (.onBranch (id "Smooth") (id "Line") (branchRef "B")) &&
    binding "dl" == some (.branchDifferential (id "Smooth") (id "Cotangent") (id "Line") (branchRef "B")) &&
    binding "p21" == some (.branchProjector (id "Smooth") (id "Line") (branchRef "B") 1 0))
#eval check "every binding is valid and none allocates"
  (env.primitives.all fun entry => validPrimitiveBinding env.indexed entry.binding && !entry.binding.allocates)
#eval check "the operand counts: no operand for an invariant, a point, and a point and a value"
  ((["tr2", "c0", "annI", "actJ", "on", "dl", "p12"].map fun name => (binding name).map (·.arity env.indexed)) ==
    [some 0, some 0, some 1, some 1, some 2, some 2, some 2])
#eval check "an invariant pulls back along its map, an observation is opaque to a reverse pass"
  ((binding "tr2").all (fun b => b.contract.reverse == .morphism ⟨2, [], [Poly.scale 2 gap]⟩) &&
    ["annI", "actJ", "on", "dl", "p12"].all fun name =>
      (binding name).all fun b => b.contract.reverse == .none)

/-! ## An executable Core module -/

private def obj (name : String) : Index := .object (.global (id name))
private def smoothType (a b : String) : Core.Result := ⟨.indexed ⟨id "Smooth", [obj a, obj b]⟩, none⟩
private def tangentType : Core.Result := ⟨.indexed ⟨id "Tangent", [obj "Plane"]⟩, none⟩
private def cotangentType : Core.Result := ⟨.indexed ⟨id "Cotangent", [obj "Plane"]⟩, none⟩
private def bool : Core.Result := ⟨.pure .bool, none⟩
private def pairType : Core.Result := ⟨.pure (.pair .int), none⟩
private def prim (name : String) (arguments : List Core.Term) (result : Core.Result) : Core.Term :=
  .primitive (id name) arguments result
private def planeAt (a b : Int) : Core.Term := prim "plane_at" [.integer a, .integer b] (smoothType "Pt" "Plane")
private def lineAt (t : Int) : Core.Term := prim "line_at" [.integer t] (smoothType "Pt" "Line")
private def ptAt : Core.Term := prim "pt_at" [] (smoothType "Pt" "Pt")
private def smoothMap (name : String) (a := "Plane") : Core.Term := prim name [] (smoothType a "Line")
private def vplane (point : Core.Term) (a b : Int) : Core.Term :=
  prim "vplane" [point, .integer a, .integer b] tangentType
private def dplane (point : Core.Term) (a b : Int) : Core.Term :=
  prim "dplane" [point, .integer a, .integer b] cotangentType
private def differential (function point : Core.Term) : Core.Term :=
  prim "differential" [function, point] cotangentType
private def sharp (covector : Core.Term) : Core.Term := prim "sharp_euclid" [covector] tangentType
private def sameSmooth (left right : Core.Term) : Core.Term := prim "same_smooth" [left, right] bool
private def sameVector (left right : Core.Term) : Core.Term := prim "same_vector" [left, right] bool
private def sameCovector (left right : Core.Term) : Core.Term := prim "same_covector" [left, right] bool
private def observe (name : String) (point : Core.Term) (result : Core.Result) : Core.Term := prim name [point] result
private def onB (point value : Core.Term) : Core.Term := prim "on" [point, value] bool
private def dl (point value : Core.Term) : Core.Term := prim "dl" [point, value] cotangentType
private def projector (entry : String) (point value : Core.Term) : Core.Term := prim entry [point, value] pairType
private def numerator (value : Core.Term) : Core.Term := .project .int true value
private def denominator (value : Core.Term) : Core.Term := .project .int false value
private def equals (left : Core.Term) (right : Int) : Core.Term := .binary .eq left (.integer right) bool
/-- A pair equals the reduced fraction `a / b`. -/
private def isFraction (value : Core.Term) (a b : Int) : Core.Term :=
  .binary .and (equals (numerator value) a) (equals (denominator value) b) bool
private def guarded (condition : Core.Term) (code : Int) (rest : Core.Term) : Core.Term :=
  .branch condition rest (.integer code) ⟨.pure .int, none⟩
private def notE (value : Core.Term) : Core.Term := .unary .not value bool

private def p12 : Core.Term := planeAt 1 2
private def p34 : Core.Term := planeAt 3 4
private def p10 : Core.Term := planeAt 1 0
private def origin : Core.Term := planeAt 0 0

private def spectralMain : Core.Function := {
  id := 0, definition := id "main", parameters := [], returnType := .pure .int
  body :=
    -- C3: 0 and N, 2I and J have the same invariants but different actions.
    guarded (sameSmooth (smoothMap "trZ" "Pt") (smoothMap "trN" "Pt")) 1 <|
    guarded (sameSmooth (smoothMap "cZ" "Pt") (smoothMap "cN" "Pt")) 2 <|
    guarded (sameSmooth (smoothMap "trI" "Pt") (smoothMap "trJ" "Pt")) 3 <|
    guarded (sameSmooth (smoothMap "cI" "Pt") (smoothMap "cJ" "Pt")) 4 <|
    guarded (observe "annZ" ptAt bool) 5 <|
    guarded (notE (observe "annN" ptAt bool)) 6 <|
    guarded (observe "annI" ptAt bool) 7 <|
    guarded (notE (observe "annJ" ptAt bool)) 8 <|
    guarded (observe "annJ2" ptAt bool) 9 <|
    guarded (observe "annN2" ptAt bool) 10 <|
    guarded (isFraction (observe "actZ" ptAt pairType) 0 1) 11 <|
    guarded (isFraction (observe "actN" ptAt pairType) 1 1) 12 <|
    guarded (isFraction (observe "actI" ptAt pairType) 0 1) 13 <|
    guarded (isFraction (observe "actJ" ptAt pairType) 1 1) 14 <|
    -- (t − x)(H(3, 4)) = H(3, 4) − 3I has the entry −6 at (e2, e2).
    guarded (isFraction (observe "actH" p34 pairType) (-6) 1) 15 <|
    -- C4: tr2 is the declared reference; d tr1 = 0; d c0 = −½ d tr2.
    guarded (sameSmooth (smoothMap "tr2") (smoothMap "ref2")) 16 <|
    guarded (sameCovector (differential (smoothMap "tr1") p34) (dplane p34 0 0)) 17 <|
    guarded (sameCovector (differential (smoothMap "c0") p12) (dplane p12 (-2) (-4))) 18 <|
    -- C5: d tr2 = (4x, 4y), and its Euclidean sharp is the vector (4x, 4y).
    guarded (sameCovector (differential (smoothMap "tr2") p12) (dplane p12 4 8)) 19 <|
    guarded (sameCovector (differential (smoothMap "tr2") p34) (dplane p34 12 16)) 20 <|
    guarded (sameCovector (differential (smoothMap "tr2") origin) (dplane origin 0 0)) 21 <|
    guarded (sameVector (sharp (differential (smoothMap "tr2") p12)) (vplane p12 4 8)) 22 <|
    guarded (sameVector (sharp (differential (smoothMap "tr2") p34)) (vplane p34 12 16)) 23 <|
    -- C9: the branch points.
    guarded (onB p34 (lineAt 5)) 24 <|
    guarded (onB p34 (lineAt (-5))) 25 <|
    guarded (onB p10 (lineAt 1)) 26 <|
    guarded (onB p10 (lineAt (-1))) 27 <|
    guarded (notE (onB p34 (lineAt 4))) 28 <|
    guarded (notE (onB origin (lineAt 0))) 29 <|
    -- C10: dλ = ±(3/5, 4/5) at (3, 4) and ±(1, 0) at (1, 0); a unit covector.
    guarded (isFraction (prim "dx" [dl p34 (lineAt 5)] pairType) 3 5) 30 <|
    guarded (isFraction (prim "dy" [dl p34 (lineAt 5)] pairType) 4 5) 31 <|
    guarded (isFraction (prim "dx" [dl p34 (lineAt (-5))] pairType) (-3) 5) 32 <|
    guarded (isFraction (prim "dy" [dl p34 (lineAt (-5))] pairType) (-4) 5) 33 <|
    guarded (sameCovector (dl p10 (lineAt 1)) (dplane p10 1 0)) 34 <|
    guarded (sameCovector (dl p10 (lineAt (-1))) (dplane p10 (-1) 0)) 35 <|
    guarded (isFraction (prim "pairing" [dl p34 (lineAt 5), sharp (dl p34 (lineAt 5))] pairType) 1 1) 36 <|
    -- Off the branch the differential is the failure value, which equals nothing.
    guarded (notE (sameCovector (dl p34 (lineAt 4)) (dl p34 (lineAt 4)))) 37 <|
    guarded (isFraction (prim "dx" [dl origin (lineAt 0)] pairType) 0 0) 38 <|
    -- C11: the eigenprojectors, and (0, 0) off the branch.
    guarded (isFraction (projector "p11" p34 (lineAt 5)) 4 5) 39 <|
    guarded (isFraction (projector "p12" p34 (lineAt 5)) 2 5) 40 <|
    guarded (isFraction (projector "p21" p34 (lineAt 5)) 2 5) 41 <|
    guarded (isFraction (projector "p22" p34 (lineAt 5)) 1 5) 42 <|
    guarded (isFraction (projector "p11" p34 (lineAt (-5))) 1 5) 43 <|
    guarded (isFraction (projector "p12" p34 (lineAt (-5))) (-2) 5) 44 <|
    guarded (isFraction (projector "p22" p34 (lineAt (-5))) 4 5) 45 <|
    guarded (isFraction (projector "p11" p10 (lineAt 1)) 1 1) 46 <|
    guarded (isFraction (projector "p22" p10 (lineAt 1)) 0 1) 47 <|
    guarded (isFraction (projector "p12" p34 (lineAt 4)) 0 0) 48 <|
    guarded (isFraction (projector "p11" origin (lineAt 0)) 0 0) 49 <|
    .integer 42 }

/-- The spectral bindings of this regression as one audited Core module. -/
def spectralFixture : Core.Module := ⟨env, [spectralMain], some 0⟩

private def evaluate (term : Core.Term) : Option Core.Semantics.Value :=
  Core.Semantics.eval spectralFixture 64 (fun _ => none) term

#eval check "the spectral Core module is accepted" (Core.Typing.checkModule spectralFixture true).isOk
#eval check "the spectral Core module evaluates to 42" (evaluate spectralMain.body == some (.integer 42))
#eval check "the branch differential at ((3, 4), 5) is the covector (3/5, 4/5) at (3, 4)"
  (evaluate (dl p34 (lineAt 5)) == some (.indexed (.fiber .cotangent (some ⟨[3, 4], [q 3 5, q 4 5]⟩))))
#eval check "off the branch the differential is the failure value"
  (evaluate (dl p34 (lineAt 4)) == some (.indexed (.fiber .cotangent none)) &&
    evaluate (dl origin (lineAt 0)) == some (.indexed (.fiber .cotangent none)))
#eval check "the module action reads exact entries"
  (evaluate (observe "actJ" ptAt pairType) == some (.pairInt 1 1) &&
    evaluate (observe "annJ" ptAt bool) == some (.boolean false))

/-! ## Erasure: the runtime evaluator agrees on the erased values -/

private def agrees (name : String) (values : List Core.Semantics.Value) : Bool :=
  match binding name with
  | some b => match Core.Semantics.evalPrimitive env.indexed b values with
    | some value => match values.mapM Core.Semantics.erasePrimitiveValue, Core.Semantics.erasePrimitiveValue value with
      | some inputs, some output => Core.Semantics.evalRuntimePrimitive b inputs == some output
      | _, _ => false
    | none => false
  | none => false

private def pointValue (values : List Int) : Core.Semantics.Value :=
  .indexed (.smooth (SmoothRuntime.intPoint values))

#eval check "every spectral entry erases to its runtime evaluator"
  (agrees "tr2" [] && agrees "c0" [] && agrees "annJ" [pointValue []] && agrees "actH" [pointValue [3, 4]] &&
    agrees "on" [pointValue [3, 4], pointValue [5]] && agrees "dl" [pointValue [3, 4], pointValue [5]] &&
    agrees "dl" [pointValue [3, 4], pointValue [4]] && agrees "p12" [pointValue [3, 4], pointValue [-5]] &&
    agrees "p12" [pointValue [0, 0], pointValue [0]])
#eval check "the evaluators take exactly their operands"
  (["annI", "on", "dl", "p12"].all fun name => (binding name).all fun b =>
    (Core.Semantics.evalPrimitive env.indexed b []).isNone &&
      (Core.Semantics.evalPrimitive env.indexed b [.integer 1, .integer 2]).isNone &&
      (Core.Semantics.evalRuntimePrimitive b []).isNone)

/-! ## Static operands in Core -/

private def rejected (body : Core.Term) : Bool :=
  !(Core.Typing.checkModule ⟨env, [{ spectralMain with body := guarded body 1 (.integer 42) }], some 0⟩ true).isOk

#eval check "a point of another object is rejected"
  (rejected (observe "annI" p34 bool) && rejected (onB ptAt (lineAt 5)) &&
    rejected (isFraction (observe "actH" ptAt pairType) 0 1))
#eval check "a value that is not in the declared line is rejected"
  (rejected (onB p34 p34) && rejected (sameCovector (dl p34 p12) (dl p34 p12)))
#eval check "a point from a positive-dimensional object is rejected"
  (rejected (onB (prim "toPlane" [] (smoothType "Line" "Plane")) (prim "idLine" [] (smoothType "Line" "Line"))) &&
    rejected (observe "annN" (prim "idLine" [] (smoothType "Line" "Line")) bool))
#eval check "a result type over another object is rejected"
  (rejected (sameVector (prim "dl" [p34, lineAt 5] tangentType) (vplane p34 0 0)))

/-! ## The role table names the expected object -/

private def explain (name : String) (operands : List ValueType) (result : ValueType) :
    Option Source.Diagnostics.PrimitiveFailure :=
  (binding name).bind fun b => Source.Diagnostics.explainPrimitive env.indexed b [] 0 operands result

private def explained (name : String) (operands : List ValueType) (result : ValueType) : String :=
  match explain name operands result with
  | some failure => Source.Diagnostics.explainFailure env none {} name "" failure
  | none => ""

private def smoothValue (a b : String) : ValueType := .indexed ⟨id "Smooth", [obj a, obj b]⟩

#eval check "annihilates names the spectrum's object"
  (explain "annI" [smoothValue "Pt" "Plane"] .boolean ==
      some (.role (.object "point" "target" (.global (id "Pt")) (.global (id "Plane")) "the spectrum's object")) &&
    explained "annI" [smoothValue "Pt" "Plane"] .boolean ==
      "annI requires a point with target Pt (the spectrum's object), but the supplied point has target Plane")
#eval check "on_branch names the branch's object and the declared line"
  (explained "on" [smoothValue "Pt" "Line", smoothValue "Pt" "Line"] .boolean ==
      "on requires a point with target Plane (the branch's object), but the supplied point has target Line" &&
    explained "on" [smoothValue "Pt" "Plane", smoothValue "Pt" "Plane"] .boolean ==
      "on requires a value with target Line (the primitive's declared line), but the supplied value has target Plane")

/-! ## Source rejections -/

#eval check "a spectral binding with a family of the wrong representation fails the audit, naming it"
  (rejectsWith (with' [branchDifferential "bad" (cotangent := "Tangent")]) "E_TYPE"
      "the family `spectral::Tangent` of the `branch_differential` primitive `spectral::bad` must have the representation `cotangent`" &&
    rejectsWith (with' [onBranch "bad" (maps := "Cotangent")]) "E_TYPE"
      "the family `spectral::Cotangent` of the `on_branch` primitive `spectral::bad` must have the representation `smooth`" &&
    rejectsWith (with' [branchDifferential "bad" (cotangent := "Line")]) "E_TYPE"
      "the family `spectral::Line` of the `branch_differential` primitive `spectral::bad` must have the representation `cotangent`")
#eval check "a line that is not 1-dimensional fails the audit, naming it"
  (rejectsWith (with' [onBranch "bad" (line := "Plane")]) "E_TYPE"
      "the line `spectral::Plane` of the `on_branch` primitive `spectral::bad` must be a smooth object of dimension 1" &&
    rejectsWith (with' [branchDifferential "bad" (line := "Cotangent")]) "E_TYPE"
      "the line `spectral::Cotangent` of the `branch_differential` primitive `spectral::bad` must be a smooth object")
#eval check "the positional families of branch_differential are not reordered"
  (rejectsWith (with' [branchDifferential "bad" (cotangent := "Line") (line := "Cotangent")]) "E_TYPE"
    "must have the representation `cotangent`")

/-! ## Tampered Core: the independent audit rechecks every embedded declaration -/

private def tamper (extra : PrimitiveBinding) : Bool :=
  !Core.validDeclarations { env with primitives := env.primitives ++ [⟨id "bad", extra⟩] }

private def S : SpectrumRef := spectrumRef "S"
private def B : BranchRef := branchRef "B"
private def H : EndoRef := endoRef "H"
private def tr2Map : Map := ⟨2, [], [Poly.scale 2 gap]⟩
private def element : Poly := Poly.sub (Poly.var 3 2) (Poly.const 3 2)
private def diagonal : PolyMatrix := [[x, []], [[], y]]

#eval check "accepted Core is valid" (Core.validDeclarations env)
#eval check "a fresh copy of a correct binding is accepted, so the forgeries below fail on their data"
  (!tamper (.spectralInvariant lineMap tr2Map (.tracePower H 2)) && !tamper (.annihilates (id "Smooth") S element) &&
    !tamper (.onBranch (id "Smooth") (id "Line") B) &&
    !tamper (.branchProjector (id "Smooth") (id "Line") B 1 1))
#eval check "a forged invariant map, power, index or source is rejected"
  (tamper (.spectralInvariant lineMap ⟨2, [], [gap]⟩ (.tracePower H 2)) &&
    tamper (.spectralInvariant lineMap tr2Map (.tracePower H 1)) &&
    tamper (.spectralInvariant lineMap tr2Map (.tracePower H 0)) &&
    tamper (.spectralInvariant lineMap ⟨2, [], [Poly.neg gap]⟩ (.charCoefficient S 1)) &&
    tamper (.spectralInvariant lineMap ⟨2, [], [[]]⟩ (.charCoefficient S 3)) &&
    tamper (.spectralInvariant ⟨id "Smooth", [obj "Line", obj "Line"]⟩ ⟨1, [], [[]]⟩ (.tracePower H 1)) &&
    tamper (.spectralInvariant lineMap ⟨2, [], [Poly.scale 2 gap, []]⟩ (.tracePower H 2)))
#eval check "a tampered embedded endomorphism is rejected"
  (tamper (.spectralInvariant lineMap ⟨2, [], [Poly.add (Poly.mul x x) (Poly.mul y y)]⟩
      (.tracePower { H with rows := diagonal } 2)) &&
    tamper (.annihilates (id "Smooth") { S with endomorphism := { H with symmetric := false } } element) &&
    tamper (.annihilates (id "Smooth") { S with endomorphism := { H with rows := diagonal } } element) &&
    tamper (.annihilates (id "Smooth") { S with endomorphism := { H with module := id "W2" } } element) &&
    tamper (.annihilates (id "Smooth") { S with endomorphism := { H with object := id "Pt" } } element))
#eval check "a tampered embedded χ or adjugate is rejected"
  (tamper (.annihilates (id "Smooth") { S with characteristic := Poly.var 3 2 } element) &&
    tamper (.actionEntry (id "Smooth") { S with adjugate := [] } element 0 0) &&
    tamper (.onBranch (id "Smooth") (id "Line") { B with spectrum := { S with characteristic := [] } }))
#eval check "a tampered embedded g, W or exponent is rejected"
  (tamper (.onBranch (id "Smooth") (id "Line") { B with localize := Poly.one 2 }) &&
    tamper (.branchDifferential (id "Smooth") (id "Cotangent") (id "Line") { B with witness := Poly.var 3 2 }) &&
    tamper (.branchProjector (id "Smooth") (id "Line") { B with exponent := 2 } 0 0))
#eval check "a stale reference is rejected: another spectrum's data, or another declaration's name"
  (tamper (.annihilates (id "Smooth") { spectrumRef "SJ" with spectrum := id "SI" } element) &&
    tamper (.annihilates (id "Smooth") { S with spectrum := id "SI" } element) &&
    tamper (.onBranch (id "Smooth") (id "Line") { B with spectrum := spectrumRef "SJ" }) &&
    tamper (.onBranch (id "Smooth") (id "Line") { B with branch := id "S" }) &&
    tamper (.annihilates (id "Smooth") { S with endomorphism := endoRef "J" } element))
#eval check "an element of another arity, or an entry out of range, is rejected"
  (tamper (.annihilates (id "Smooth") S (Poly.var 2 0)) && tamper (.actionEntry (id "Smooth") S element 2 0) &&
    tamper (.branchProjector (id "Smooth") (id "Line") B 0 2) && !tamper (.actionEntry (id "Smooth") S element 1 1))
#eval check "forged families or a forged line are rejected"
  (tamper (.annihilates (id "Cotangent") S element) &&
    tamper (.onBranch (id "Smooth") (id "Plane") B) &&
    tamper (.branchDifferential (id "Smooth") (id "Tangent") (id "Line") B) &&
    tamper (.branchDifferential (id "Smooth") (id "Cotangent") (id "Pt") B))

/-! ## Generated code declares each polynomial and matrix once -/

private def generatedCode (function : Core.Function) : Option String := do
  let .ok checked := Core.Typing.checkModule ⟨env, [function], some 0⟩ true | none
  (Core.Codegen.generate checked).toOption
private def generatedChecks (checks : List Core.Term) : Option String :=
  generatedCode { spectralMain with body := checks.foldr (fun condition rest => guarded condition 1 rest) (.integer 42) }
private def occurrences (part : String) (source : Option String) : Option Nat :=
  source.map fun text => (text.splitOn part).length - 1

private def polyType : String := "def poly_0 : VastitasKernel.AlgebraRuntime.Poly :=\n"
private def rowsType : String := "def rows_0 : List (List VastitasKernel.AlgebraRuntime.Poly) :=\n"
private def oneBranch : Option String := generatedChecks [onB p34 (lineAt 5)]
private def fourBranches : Option String := generatedChecks (List.replicate 4 (onB p34 (lineAt 5)))

#eval check "one call and four calls of on_branch declare g and χ once"
  ([oneBranch, fourBranches].map (occurrences polyType) == [some 1, some 1] &&
    [oneBranch, fourBranches].map (occurrences "def poly_1 ") == [some 1, some 1] &&
    [oneBranch, fourBranches].map (occurrences "(VastitasKernel.SpectralRuntime.onBranch poly_0 poly_1 ") ==
      [some 1, some 4] &&
    occurrences "poly_2" oneBranch == some 0)
#eval check "the module action declares the rows of the endomorphism once"
  (occurrences rowsType (generatedChecks [observe "annI" ptAt bool, isFraction (observe "actI" ptAt pairType) 0 1]) ==
      some 1 &&
    occurrences "rows_1" (generatedChecks [observe "annI" ptAt bool, isFraction (observe "actI" ptAt pairType) 0 1]) ==
      some 0)
#eval check "a module with spectral calls imports the spectral runtime, and only then"
  (occurrences "import VastitasKernel.SpectralRuntime\n" (generatedCode spectralMain) == some 1 &&
    occurrences "import VastitasKernel.SpectralRuntime\n"
      (generatedChecks [sameSmooth (smoothMap "tr2") (smoothMap "ref2")]) == some 0)
#eval check "an invariant lowers as a declared smooth map"
  (occurrences "(VastitasKernel.SmoothRuntime.Program.primitive map_" (generatedChecks
    [sameSmooth (smoothMap "tr2") (smoothMap "ref2")]) == some 2)
#eval check "the observations lower to the spectral runtime"
  (let source := generatedCode spectralMain
  ["VastitasKernel.SpectralRuntime.annihilates rows_", "VastitasKernel.SpectralRuntime.actionEntry rows_",
    "VastitasKernel.SpectralRuntime.onBranch poly_", "VastitasKernel.SpectralRuntime.branchDifferential poly_",
    "VastitasKernel.SpectralRuntime.projectorEntry poly_"].all fun call => (occurrences call source).any (· > 0))
#eval check "a lowering with the wrong operand count is the arity error"
  (["tr2", "annI", "on", "dl", "p12"].all fun name =>
    (binding name).all fun b => !(b.contract.render (.share []) ["a", "b", "c"]).toBool)

/-! ## Compiled reverse Core pulls back along the invariants' maps -/

private def compiledReverse : Option Core.Module :=
  match Core.Typing.checkModule spectralFixture true with
  | .ok checked => match Core.Reverse.compile checked with
    | .ok compiled => some compiled.core.module
    | .error _ => none
  | .error _ => none

#eval check "the reverse compilation of the spectral module compiles every differential and evaluates to 42"
  (match compiledReverse with
    | some module =>
      module.functions.length > spectralFixture.functions.length &&
        match module.main.bind fun main => module.functions.find? (·.id == main) with
        | some main => Core.Semantics.eval module 64 (fun _ => none) main.body == some (.integer 42)
        | none => false
    | none => false)
private def jacobianMap? : PrimitiveBinding → Option Map
  | .cotangentJacobian _ _ map => some map
  | _ => none

#eval check "the compiled backward steps pull back along the maps of tr2 and c0"
  (match compiledReverse with
    | some module =>
      let maps := module.declarations.primitives.filterMap (jacobianMap? ·.binding)
      maps.contains ⟨2, [], [Poly.scale 2 gap]⟩ && maps.contains ⟨2, [], [Poly.neg gap]⟩
    | none => false)

/-! ## The wire decodes the observations -/

open Lean in
private def decodes (j : Json) : Bool := (Wire.declarationBody j).isOk
open Lean in
private def spanJson : Json :=
  Json.mkObj [("start", (0 : Nat)), ("end", (0 : Nat)), ("line", (1 : Nat)), ("column", (1 : Nat))]
open Lean in
private def pathJson (name : String) : Json := Json.mkObj [("path", Json.arr #[Json.str name]), ("span", spanJson)]
open Lean in
private def form (op : String) (fields : List (String × Json)) : Json := Json.mkObj
  [("kind", Json.str "primitive"), ("name", Json.str "X"), ("public", Json.bool true), ("span", spanJson),
    ("binding", Json.mkObj (("op", Json.str op) :: fields))]
open Lean in
private def coordinateJson (name : String) : Json := Json.mkObj [("op", Json.str "coordinate"), ("name", Json.str name)]

open Lean in
private def forms : List Json := [
  form "annihilates" [("map_family", pathJson "Smooth"), ("spectrum", pathJson "S"), ("element", coordinateJson "t")],
  form "action_entry" [("map_family", pathJson "Smooth"), ("spectrum", pathJson "S"), ("element", coordinateJson "t"),
    ("row", Json.str "e1"), ("column", Json.str "e2")],
  form "on_branch" [("map_family", pathJson "Smooth"), ("line", pathJson "Line"), ("branch", pathJson "B")],
  form "branch_differential" [("map_family", pathJson "Smooth"), ("cotangent", pathJson "Cotangent"),
    ("line", pathJson "Line"), ("branch", pathJson "B")],
  form "branch_projector" [("map_family", pathJson "Smooth"), ("line", pathJson "Line"), ("branch", pathJson "B"),
    ("row", Json.str "e1"), ("column", Json.str "e2")]]

#eval check "the decoder decodes each spectral observation" (forms.all decodes)
open Lean in
#eval check "the wire carries no embedded declaration: a certificate, rows or a quotient is an unknown field"
  (!decodes (form "on_branch" [("map_family", pathJson "Smooth"), ("line", pathJson "Line"),
      ("branch", pathJson "B"), ("characteristic", Json.arr #[])]) &&
    !decodes (form "annihilates" [("map_family", pathJson "Smooth"), ("spectrum", pathJson "S"),
      ("element", coordinateJson "t"), ("rows", Json.arr #[])]))

end VastitasKernel.Indexed.SpectralRegression
