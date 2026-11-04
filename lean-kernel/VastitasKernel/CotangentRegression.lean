import VastitasKernel.IndexedSourceChecker
import VastitasKernel.IndexedDeclarationProtocol
import VastitasKernel.IndexedCodegen
import VastitasKernel.IndexedSemantics

set_option autoImplicit false

/-! Covectors, vectors, tapes and the reverse pass (Stage 3) through the actual
common source checker, the independent declaration and Core audits, the Core
semantics and the protocol decoder. These are executable regressions, not
proofs. -/
namespace VastitasKernel.Indexed.CotangentRegression

open AlgebraRuntime

private def pkg : Namespace.PackageId := ⟨"/cotangent/Vastitas.toml", "cotangent", "0.1.0"⟩
private def id (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩
private def path (name : String) : Source.Path := ⟨[name], {}⟩
private def decl (name : String) (body : Source.Body) : Source.Declaration := ⟨name, body, true, {}⟩
private def c (name : String) : Source.PolyExpr := .coordinate name
private def n (value : Nat) : Source.PolyExpr := .natural value
private def space (name : String) (dimension : Nat) (coordinates : List String) : Source.Declaration :=
  decl name (.smoothAffine (path "SmoothR") dimension coordinates)
private def morphism (name x y : String) (definition : Source.MorphismDefinition) : Source.Declaration :=
  decl name (.morphism (path "Smooth") [path x, path y] definition)
private def primitive (name : String) (binding : Source.Primitive) : Source.Declaration :=
  decl name (.primitive binding)

private def family (representation : FamilyRepresentation) (arity : Nat)
    (constraints : List Constraint) (domain := "CInfAffine") : Source.Declaration :=
  decl (match representation with
    | .fiber .cotangent => "Cotangent" | .fiber .tangent => "Tangent" | .tape => "Tape" | _ => "Smooth")
    (.family ⟨(List.range arity).map fun _ => .object (path domain), constraints, representation⟩)

private def declarations : List Source.Declaration := [
  decl "CInfReal" .marker,
  decl "SmoothR" (.implementation (path "CInfReal") .smoothAffine []),
  decl "CInfAffine" (.classification [] [path "SmoothR"]),
  family .smooth 2 [.canonical 0, .canonical 1],
  family (.fiber .cotangent) 1 [.canonical 0],
  family (.fiber .tangent) 1 [.canonical 0],
  family .tape 2 [.canonical 0, .canonical 1],
  space "Pt" 0 [],
  space "Line" 1 ["t"],
  space "Plane" 2 ["x", "y"],
  morphism "f" "Line" "Plane" (.pullback [("x", c "t"), ("y", .pow (c "t") 2)]),
  morphism "g" "Plane" "Line" (.pullback [("t", .sum [.pow (c "x") 2, c "y"])]),
  morphism "gf" "Line" "Line" (.pullback [("t", .product [n 2, .pow (c "t") 2])]),
  morphism "sq" "Line" "Line" (.pullback [("t", .pow (c "t") 2)]),
  morphism "idP" "Plane" "Plane" .identity,
  primitive "compose" (.smoothCompose (path "Smooth")),
  primitive "composite" (.smoothComposite (path "Smooth")),
  primitive "line_at" (.smoothIntPoint (path "Smooth") (path "Line") (path "Pt")),
  primitive "plane_at" (.smoothIntPoint (path "Smooth") (path "Plane") (path "Pt")),
  primitive "pullback" (.cotangentPullback (path "Smooth") (path "Cotangent") .saved),
  primitive "pullback_recomputed" (.cotangentPullback (path "Smooth") (path "Cotangent") .recomputed),
  primitive "differential" (.differential (path "Smooth") (path "Cotangent") (path "Line")),
  primitive "linearize" (.linearize (path "Smooth") (path "Tape")),
  primitive "backward" (.cotangentBackward (path "Tape") (path "Cotangent")),
  primitive "lies_over" (.fiberAt (path "Cotangent") (path "Smooth")),
  primitive "same_covector" (.fiberEqual (path "Cotangent")),
  primitive "tangent_over" (.fiberAt (path "Tangent") (path "Smooth")),
  primitive "pairing" (.fiberPairing (path "Cotangent") (path "Tangent")),
  primitive "dline" (.fiberVector (path "Cotangent") (path "Smooth") (path "Line")),
  primitive "dplane" (.fiberVector (path "Cotangent") (path "Smooth") (path "Plane")),
  primitive "vplane" (.fiberVector (path "Tangent") (path "Smooth") (path "Plane")),
  primitive "vline" (.fiberVector (path "Tangent") (path "Smooth") (path "Line")),
  primitive "dt" (.fiberComponent (path "Cotangent") (path "Line") "t"),
  primitive "dx" (.fiberComponent (path "Cotangent") (path "Plane") "x"),
  primitive "dy" (.fiberComponent (path "Cotangent") (path "Plane") "y") ]

private def program (ds := declarations) : Source.Program := {
  file := "cotangent", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := {path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {}}
    declarations := ds }], none⟩] }

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"cotangent regression failed: {label}")

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

private def resolved : Option Core.Declarations :=
  match Source.checkDeclarations program with
  | .ok checked => some checked.resolved.declarations
  | .error _ => none

private def binding (name : String) : Option PrimitiveBinding := resolved.bind (·.primitive? (id name))

#eval check "the common source checker accepts fibers, tapes and the reverse pass" (code program == "accepted")
#eval check "declaration order independent" (code (program declarations.reverse) == "accepted")
#eval check "fiber families have their variance"
  ((resolved.map fun env => (fiberVariance? env.indexed (id "Cotangent"), fiberVariance? env.indexed (id "Tangent")))
    == some (some .cotangent, some .tangent))
#eval check "a tape family is not a fiber family"
  ((resolved.map fun env => (isTapeFamily env.indexed (id "Tape"), fiberVariance? env.indexed (id "Tape")))
    == some (true, none))
#eval check "fiber_component resolves the coordinate name to its index"
  (binding "dy" == some (.fiberComponent (id "Cotangent") (id "Plane") 1) &&
    binding "dx" == some (.fiberComponent (id "Cotangent") (id "Plane") 0))
#eval check "the pullback modes are kept"
  (binding "pullback_recomputed" == some (.cotangentPullback (id "Smooth") (id "Cotangent") .recomputed))
#eval check "fiber_vector takes the point and one integer per coordinate"
  ((resolved.map fun env => (binding "dplane").map (·.arity env.indexed)) == some (some 3))
#eval check "only the components of fiber_vector take an integer hint"
  ((binding "dplane").map (fun b => (b.argumentHint 0, b.argumentHint 1, b.argumentHint 2))
    == some (none, some (.pure .int), some (.pure .int)))

/-! ## An executable Core module

The module checks the roadmap identity and its failure cases. It is also
compiled by the native fixture script. -/

private def obj (name : String) : Index := .object (.global (id name))
private def smoothType (x y : String) : Core.Result := ⟨.indexed ⟨id "Smooth", [obj x, obj y]⟩, none⟩
private def cotangentType (x : String) : Core.Result := ⟨.indexed ⟨id "Cotangent", [obj x]⟩, none⟩
private def tangentType (x : String) : Core.Result := ⟨.indexed ⟨id "Tangent", [obj x]⟩, none⟩
private def tapeType (x y : String) : Core.Result := ⟨.indexed ⟨id "Tape", [obj x, obj y]⟩, none⟩
private def bool : Core.Result := ⟨.pure .bool, none⟩
private def pairType : Core.Result := ⟨.pure (.pair .int), none⟩
private def prim (name : String) (arguments : List Core.Term) (result : Core.Result) : Core.Term :=
  .primitive (id name) arguments result
private def constant (name x y : String) : Core.Term := prim name [] (smoothType x y)
private def compose (after before : Core.Term) (x y : String) : Core.Term :=
  prim "compose" [after, before] (smoothType x y)
private def lineAt (value : Int) : Core.Term := prim "line_at" [.integer value] (smoothType "Pt" "Line")
private def planeAt (x y : Int) : Core.Term := prim "plane_at" [.integer x, .integer y] (smoothType "Pt" "Plane")
private def dline (point : Core.Term) (component : Int) : Core.Term :=
  prim "dline" [point, .integer component] (cotangentType "Line")
private def dplane (point : Core.Term) (x y : Int) : Core.Term :=
  prim "dplane" [point, .integer x, .integer y] (cotangentType "Plane")
private def vplane (point : Core.Term) (x y : Int) : Core.Term :=
  prim "vplane" [point, .integer x, .integer y] (tangentType "Plane")
private def pullback (map point seed : Core.Term) (x : String) (mode := "pullback") : Core.Term :=
  prim mode [map, point, seed] (cotangentType x)
private def sameCovector (left right : Core.Term) : Core.Term := prim "same_covector" [left, right] bool
private def liesOver (value point : Core.Term) : Core.Term := prim "lies_over" [value, point] bool
private def component (name : String) (value : Core.Term) : Core.Term := prim name [value] pairType
private def numerator (value : Core.Term) : Core.Term := .project .int true value
private def denominator (value : Core.Term) : Core.Term := .project .int false value
private def equals (left : Core.Term) (right : Int) : Core.Term :=
  .binary .eq left (.integer right) bool
private def guarded (condition : Core.Term) (code : Int) (rest : Core.Term) : Core.Term :=
  .branch condition rest (.integer code) ⟨.pure .int, none⟩
private def notE (value : Core.Term) : Core.Term := .unary .not value bool

private def gAfterF : Core.Term := compose (constant "g" "Plane" "Line") (constant "f" "Line" "Plane") "Line" "Line"
private def three : Core.Term := lineAt 3
/-- dt at g(f(3)) = 18. -/
private def seed : Core.Term := dline (lineAt 18) 1
/-- Along g at f(3) = (3, 9), then along f at 3. -/
private def stepwise : Core.Term :=
  pullback (constant "f" "Line" "Plane") three
    (pullback (constant "g" "Plane" "Line") (compose (constant "f" "Line" "Plane") three "Pt" "Plane") seed "Plane")
    "Line"
private def failed : Core.Term := pullback gAfterF three (dline (lineAt 17) 1) "Line"
private def dg : Core.Term := prim "differential" [constant "g" "Plane" "Line", planeAt 1 2] (cotangentType "Plane")

private def cotangentMain : Core.Function := {
  id := 0, definition := id "main", parameters := [], returnType := .pure .int
  body :=
    guarded (equals (numerator (component "dt" stepwise)) 12) 1 <|
    guarded (equals (denominator (component "dt" stepwise)) 1) 2 <|
    guarded (sameCovector stepwise (pullback gAfterF three seed "Line")) 3 <|
    guarded (sameCovector stepwise
      (pullback (prim "composite" [gAfterF] (smoothType "Line" "Line")) three seed "Line")) 4 <|
    guarded (sameCovector stepwise (pullback (constant "gf" "Line" "Line") three seed "Line")) 5 <|
    guarded (liesOver stepwise three) 6 <|
    guarded (notE (liesOver failed three)) 7 <|
    guarded (notE (sameCovector failed failed)) 8 <|
    guarded (equals (denominator (component "dt" failed)) 0) 9 <|
    guarded (sameCovector stepwise (pullback gAfterF three seed "Line" "pullback_recomputed")) 10 <|
    guarded (sameCovector stepwise (prim "backward"
      [prim "linearize" [gAfterF, three] (tapeType "Line" "Line"), seed] (cotangentType "Line"))) 11 <|
    guarded (notE (liesOver (prim "backward" [prim "linearize" [constant "sq" "Line" "Line", three]
      (tapeType "Line" "Line"), dline (lineAt 16) 1] (cotangentType "Line")) three)) 12 <|
    guarded (sameCovector (pullback (constant "idP" "Plane" "Plane") (planeAt 1 2) (dplane (planeAt 1 2) 5 7) "Plane")
      (dplane (planeAt 1 2) 5 7)) 13 <|
    guarded (equals (numerator (component "dx" dg)) 2) 14 <|
    guarded (equals (numerator (component "dy" dg)) 1) 15 <|
    guarded (equals (numerator (prim "pairing" [dg, vplane (planeAt 1 2) 3 4] pairType)) 10) 16 <|
    guarded (equals (denominator (prim "pairing" [dg, vplane (planeAt 0 0) 3 4] pairType)) 0) 17 <|
    guarded (prim "tangent_over" [vplane (planeAt 1 2) 3 4, planeAt 1 2] bool) 18 <|
    .integer 42 }

/-- The reverse pass of this regression as one audited Core module. -/
def cotangentFixture : Core.Module := ⟨resolved.getD default, [cotangentMain], some 0⟩

#eval check "the cotangent Core module is accepted" (Core.Typing.checkModule cotangentFixture true).isOk
#eval check "the cotangent Core module evaluates to 42"
  (Core.Semantics.eval cotangentFixture 64 (fun _ => none) cotangentMain.body ==
    some (Core.Semantics.Value.integer 42))
#eval check "the stepwise pullback is the covector 12 dt at 3"
  (Core.Semantics.eval cotangentFixture 64 (fun _ => none) stepwise ==
    some (.indexed (.fiber .cotangent (some ⟨[3], [12]⟩))))
#eval check "a seed at 17 fails"
  (Core.Semantics.eval cotangentFixture 64 (fun _ => none) failed == some (.indexed (.fiber .cotangent none)))
#eval check "a wrong intermediate point propagates the failure"
  (Core.Semantics.eval cotangentFixture 64 (fun _ => none)
    (pullback (constant "sq" "Line" "Line") (lineAt 1)
      (pullback (constant "f" "Line" "Plane") three
        (pullback (constant "g" "Plane" "Line") (compose (constant "f" "Line" "Plane") (lineAt 2) "Pt" "Plane")
          (dline (lineAt 8) 1) "Plane") "Line") "Line") ==
    some (.indexed (.fiber .cotangent none)))
#eval check "the cotangent Core module imports the smooth runtime" (match Core.Typing.checkModule cotangentFixture true with
  | .ok checked => match Core.Codegen.generate checked with
    | .ok source => (source.splitOn "import VastitasKernel.SmoothRuntime\n").length == 2 &&
        (source.splitOn "VastitasKernel.SmoothRuntime.PullbackMode.recomputed").length > 1 &&
        (source.splitOn "VastitasKernel.SmoothRuntime.linearize").length > 1
    | .error _ => false
  | .error _ => false)

/-! ## Static rejections in Core -/

private def rejected (body : Core.Term) : Bool :=
  !(Core.Typing.checkModule ⟨resolved.getD default, [{ cotangentMain with body := guarded body 1 (.integer 42) }],
    some 0⟩ true).isOk

#eval check "a covector over the wrong object is rejected"
  (rejected (liesOver (pullback (constant "g" "Plane" "Line") (planeAt 3 9) (dplane (planeAt 3 9) 1 0) "Plane")
    (planeAt 3 9)))
#eval check "a tangent seed is rejected"
  (rejected (liesOver (pullback gAfterF three (prim "vline" [lineAt 18, .integer 1] (tangentType "Line")) "Line")
    three))
#eval check "a tangent where a cotangent is compared is rejected"
  (rejected (sameCovector (vplane (planeAt 1 2) 1 0) (vplane (planeAt 1 2) 1 0)))
#eval check "lies_over at a point from a non-zero-dimensional object is rejected"
  (rejected (liesOver (pullback (constant "sq" "Line" "Line") (compose (constant "sq" "Line" "Line") three "Pt" "Line")
    (dline (lineAt 9) 1) "Line") (compose (constant "sq" "Line" "Line") (constant "sq" "Line" "Line") "Line" "Line")))
#eval check "a non-zero-dimensional point of a pullback is rejected"
  (rejected (liesOver (pullback (constant "sq" "Line" "Line") (constant "sq" "Line" "Line") (dline three 1) "Line")
    three))
#eval check "a differential of a map to the plane is rejected"
  (rejected (liesOver (prim "differential" [constant "f" "Line" "Plane", three] (cotangentType "Line")) three))
#eval check "a backward pass of a tape with a seed over its source is rejected"
  (rejected (liesOver (prim "backward" [prim "linearize" [constant "f" "Line" "Plane", three]
    (tapeType "Line" "Plane"), dline (lineAt 3) 1] (cotangentType "Line")) three))
#eval check "a pullback that claims a result over the target is rejected"
  (rejected (liesOver (prim "pullback" [constant "f" "Line" "Plane", three, dplane (planeAt 3 9) 1 0]
    (cotangentType "Plane")) (planeAt 3 9)))
#eval check "a fiber with too many components is rejected"
  (rejected (liesOver (prim "dline" [lineAt 3, .integer 1, .integer 2] (cotangentType "Line")) three))
#eval check "a fiber with too few components is rejected"
  (rejected (liesOver (prim "dplane" [planeAt 3 9, .integer 1] (cotangentType "Plane")) (planeAt 3 9)))
#eval check "a fiber_vector result over another object is rejected"
  (rejected (liesOver (prim "dline" [lineAt 3, .integer 1] (cotangentType "Plane")) (planeAt 3 9)))
#eval check "a forged tape from a smooth map is rejected"
  (rejected (notE (liesOver (prim "backward" [prim "sq" [] (tapeType "Line" "Line"), dline (lineAt 9) 1]
    (cotangentType "Line")) three)))
#eval check "a forged tape from a pullback is rejected"
  (rejected (notE (liesOver (prim "backward" [prim "pullback" [constant "sq" "Line" "Line", three, dline (lineAt 9) 1]
    (tapeType "Line" "Line"), dline (lineAt 9) 1] (cotangentType "Line")) three)))
#eval check "a tape ascribed to a smooth type is rejected"
  (rejected (prim "same_covector" [dline three 1, prim "backward" [.ascribe (.indexed ⟨id "Tape",
    [obj "Line", obj "Line"]⟩) (constant "sq" "Line" "Line"), dline (lineAt 9) 1] (cotangentType "Line")] bool))

/-! ## Source rejections with specific codes -/

#eval check "fiber families need exactly one canonical constraint"
  (code (replacing "Cotangent" (family (.fiber .cotangent) 1 [])) == "E_TYPE" &&
    code (replacing "Cotangent" (family (.fiber .cotangent) 2 [.canonical 0, .canonical 1])) == "E_TYPE" &&
    code (replacing "Tangent" (family (.fiber .tangent) 1 [.canonical 0, .canonical 0])) == "E_TYPE")
#eval check "tape families need exactly the canonical constraints"
  (code (replacing "Tape" (family .tape 2 [.canonical 0])) == "E_TYPE" &&
    code (replacing "Tape" (family .tape 1 [.canonical 0])) == "E_TYPE")

/-- The Stage 2 profile, to check that fibers and tapes range over smooth objects only. -/
private def presented : List Source.Declaration := [
  decl "QQ" .marker,
  decl "AffineQQ" (.implementation (path "QQ") (.presentedAffine .rational) []),
  decl "AffineScheme" (.classification [] [path "AffineQQ"]),
  decl "SpecQQ" (.affine (path "AffineQQ") [] [] none []),
  decl "QLine" (.affine (path "AffineQQ") ["t"] [] (some (path "SpecQQ")) []) ]

#eval check "presented objects coexist" (code (with' presented) == "accepted")
#eval check "fiber and tape families range over smooth objects only"
  (code (with' (presented ++ [decl "BadFiber" (.family ⟨[.object (path "AffineScheme")], [.canonical 0],
      .fiber .cotangent⟩)])) == "E_TYPE" &&
    code (with' (presented ++ [decl "BadTape" (.family ⟨[.object (path "AffineScheme"), .object (path "AffineScheme")],
      [.canonical 0, .canonical 1], .tape⟩)])) == "E_TYPE")
#eval check "a cotangent pullback needs a cotangent family"
  (code (with' [primitive "bad" (.cotangentPullback (path "Smooth") (path "Tangent") .saved)]) == "E_SMOOTH" &&
    mentions (with' [primitive "bad" (.cotangentPullback (path "Smooth") (path "Tangent") .saved)])
      "`Tangent` is a tangent family")
#eval check "a pairing names a cotangent and a tangent family"
  (code (with' [primitive "bad" (.fiberPairing (path "Tangent") (path "Cotangent"))]) == "E_SMOOTH")
#eval check "a backward pass and a differential need a cotangent family"
  (code (with' [primitive "bad" (.cotangentBackward (path "Tape") (path "Tangent"))]) == "E_SMOOTH" &&
    code (with' [primitive "bad" (.differential (path "Smooth") (path "Tangent") (path "Line"))]) == "E_SMOOTH")
#eval check "a differential needs a 1-dimensional line"
  (code (with' [primitive "bad" (.differential (path "Smooth") (path "Cotangent") (path "Plane"))]) == "E_SMOOTH" &&
    mentions (with' [primitive "bad" (.differential (path "Smooth") (path "Cotangent") (path "Plane"))])
      "must be 1-dimensional, but it has dimension 2" &&
    code (with' [primitive "bad" (.differential (path "Smooth") (path "Cotangent") (path "Pt"))]) == "E_SMOOTH")
#eval check "a fiber component names a coordinate of its object"
  (code (with' [primitive "bad" (.fiberComponent (path "Cotangent") (path "Plane") "t")]) == "E_AFFINE_COORDINATE")
#eval check "fiber contracts need smooth objects"
  (code (with' (presented ++ [primitive "bad" (.fiberVector (path "Cotangent") (path "Smooth") (path "QLine"))]))
      == "E_SMOOTH" &&
    code (with' (presented ++ [primitive "bad" (.fiberComponent (path "Cotangent") (path "QLine") "t")])) == "E_SMOOTH")
#eval check "families of the wrong kind fail the declaration audit"
  (code (with' [primitive "bad" (.cotangentPullback (path "Tape") (path "Cotangent") .saved)]) == "E_TYPE" &&
    code (with' [primitive "bad" (.linearize (path "Smooth") (path "Cotangent"))]) == "E_TYPE" &&
    code (with' [primitive "bad" (.cotangentBackward (path "Smooth") (path "Cotangent"))]) == "E_TYPE" &&
    code (with' [primitive "bad" (.fiberVector (path "Smooth") (path "Smooth") (path "Line"))]) == "E_TYPE" &&
    code (with' [primitive "bad" (.fiberAt (path "Tape") (path "Smooth"))]) == "E_TYPE" &&
    code (with' [primitive "bad" (.fiberEqual (path "Smooth"))]) == "E_TYPE")

/-! ## Tampered Core: the independent audit rechecks every binding -/

private def tamper (extra : PrimitiveBinding) : Bool :=
  match resolved with
  | some env => !Core.validDeclarations { env with primitives := env.primitives ++ [⟨id "bad", extra⟩] }
  | none => false
#eval check "accepted Core is valid" (resolved.map Core.validDeclarations == some true)
#eval check "forged cotangent pullback with mismatched families"
  (tamper (.cotangentPullback (id "Smooth") (id "Tangent") .saved) &&
    tamper (.cotangentPullback (id "Tape") (id "Cotangent") .recomputed) &&
    tamper (.cotangentPullback (id "Cotangent") (id "Cotangent") .saved))
#eval check "forged differential with a 2-dimensional line" (tamper (.differential (id "Smooth") (id "Cotangent") (id "Plane")))
#eval check "forged linearize into a fiber family" (tamper (.linearize (id "Smooth") (id "Cotangent")))
#eval check "forged backward from a smooth family" (tamper (.cotangentBackward (id "Smooth") (id "Cotangent")))
#eval check "forged fiber component out of range" (tamper (.fiberComponent (id "Cotangent") (id "Plane") 2))
#eval check "forged pairing of two cotangent families" (tamper (.fiberPairing (id "Cotangent") (id "Cotangent")))
#eval check "forged fiber vector over a non-smooth object" (tamper (.fiberVector (id "Cotangent") (id "Smooth") (id "CInfReal")))
#eval check "forged smooth constant on a tape application" (tamper
  (.smoothConstant ⟨id "Tape", [obj "Line", obj "Line"]⟩ (SmoothRuntime.identity 1)))
private def tamperIndexed (edit : Environment → Environment) : Bool :=
  match resolved with
  | some env => !Core.validDeclarations { env with indexed := edit env.indexed }
  | none => false
private def forgedFamily (name : String) (contract : Family) (env : Environment) : Environment :=
  env.map fun entry => if entry.id == id name then ⟨entry.id, .family contract⟩ else entry
#eval check "forged fiber family with two constraints" (tamperIndexed (forgedFamily "Cotangent"
  ⟨[.object (id "CInfAffine")], [.canonical 0, .canonical 0], .fiber .cotangent⟩))
#eval check "forged tape family with one parameter" (tamperIndexed (forgedFamily "Tape"
  ⟨[.object (id "CInfAffine")], [.canonical 0], .tape⟩))

/-! ## Protocols 7 and 8 do not admit the fiber forms; protocol 9 does -/

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
private def familyJson (representation : String) : Json := Json.mkObj (common "family" ++
  [("parameters", Json.arr #[]), ("constraints", Json.arr #[]), ("representation", Json.str representation)])
open Lean in
private def primitives : List Json := [
  primitiveJson [("op", "fiber_vector"), ("family", pathJson "Cotangent"), ("map_family", pathJson "Smooth"),
    ("object", pathJson "Line")],
  primitiveJson [("op", "fiber_at"), ("family", pathJson "Cotangent"), ("map_family", pathJson "Smooth")],
  primitiveJson [("op", "fiber_equal"), ("family", pathJson "Cotangent")],
  primitiveJson [("op", "fiber_component"), ("family", pathJson "Cotangent"), ("object", pathJson "Line"),
    ("coordinate", "t")],
  primitiveJson [("op", "fiber_pairing"), ("cotangent", pathJson "Cotangent"), ("tangent", pathJson "Tangent")],
  primitiveJson [("op", "cotangent_pullback"), ("map_family", pathJson "Smooth"), ("cotangent", pathJson "Cotangent"),
    ("mode", "saved")],
  primitiveJson [("op", "cotangent_pullback"), ("map_family", pathJson "Smooth"), ("cotangent", pathJson "Cotangent"),
    ("mode", "recomputed")],
  primitiveJson [("op", "differential"), ("map_family", pathJson "Smooth"), ("cotangent", pathJson "Cotangent"),
    ("line", pathJson "Line")],
  primitiveJson [("op", "linearize"), ("map_family", pathJson "Smooth"), ("tape", pathJson "Tape")],
  primitiveJson [("op", "cotangent_backward"), ("tape", pathJson "Tape"), ("cotangent", pathJson "Cotangent")] ]

#eval check "protocol 9 decodes each fiber and tape primitive" (primitives.all (decodes · true))
#eval check "protocols 7 and 8 reject each fiber and tape primitive" (primitives.all (!decodes · false))
#eval check "protocol 9 decodes the fiber and tape families"
  (["cotangent", "tangent", "tape"].all fun r => decodes (familyJson r) true)
#eval check "protocols 7 and 8 reject the fiber and tape families"
  (["cotangent", "tangent", "tape"].all fun r => !decodes (familyJson r) false)
open Lean in
#eval check "a pullback mode is saved or recomputed"
  (!decodes (primitiveJson [("op", "cotangent_pullback"), ("map_family", pathJson "Smooth"),
    ("cotangent", pathJson "Cotangent"), ("mode", "cached")]) true)
open Lean in
#eval check "the primitive allow-list rejects unlisted spellings and tape constructors"
  (["fiber_", "fiber_gradient", "cotangent_", "tape", "tape_literal", "backward", "gradient"].all fun op =>
    !decodes (primitiveJson [("op", Json.str op), ("family", pathJson "Cotangent")]) true)
open Lean in
#eval check "fiber primitives reject extra fields"
  (!decodes (primitiveJson [("op", "fiber_equal"), ("family", pathJson "Cotangent"), ("tape", Json.arr #[])]) true)

end VastitasKernel.Indexed.CotangentRegression
