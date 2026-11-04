import VastitasKernel.IndexedSourceChecker
import VastitasKernel.IndexedDeclarationProtocol
import VastitasKernel.IndexedCodegen
import VastitasKernel.IndexedSemantics

set_option autoImplicit false

/-! Smooth objects and smooth maps (Stage 3) through the actual common source
checker, the independent declaration audit and the protocol decoder. These
are executable regressions, not proofs. -/
namespace VastitasKernel.Indexed.SmoothObjectRegression

open AlgebraRuntime

private def pkg : Namespace.PackageId := ⟨"/smooth/Vastitas.toml", "smooth", "0.1.0"⟩
private def id (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩
private def path (name : String) : Source.Path := ⟨[name], {}⟩
private def decl (name : String) (body : Source.Body) : Source.Declaration := ⟨name, body, true, {}⟩
private def c (name : String) : Source.PolyExpr := .coordinate name
private def n (value : Nat) : Source.PolyExpr := .natural value
private def space (name : String) (dimension : Nat) (coordinates : List String)
    (implementation := "SmoothR") : Source.Declaration :=
  decl name (.smoothAffine (path implementation) dimension coordinates)
private def morphism (name x y : String) (definition : Source.MorphismDefinition) : Source.Declaration :=
  decl name (.morphism (path "Smooth") [path x, path y] definition)

private def smoothFamily (constraints : List Constraint := [.canonical 0, .canonical 1])
    (domain := "CInfAffine") : Source.Family :=
  ⟨[.object (path domain), .object (path domain)], constraints, .smooth⟩

private def declarations : List Source.Declaration := [
  decl "CInfReal" .marker,
  decl "SmoothR" (.implementation (path "CInfReal") .smoothAffine []),
  decl "CInfAffine" (.classification [] [path "SmoothR"]),
  decl "Smooth" (.family (smoothFamily)),
  space "Pt" 0 [],
  space "Line" 1 ["t"],
  space "Plane" 2 ["x", "y"],
  -- Target coordinate ↦ polynomial in the source coordinates.
  morphism "f" "Line" "Plane" (.pullback [("x", c "t"), ("y", .pow (c "t") 2)]),
  morphism "g" "Plane" "Line" (.pullback [("t", .sum [.pow (c "x") 2, c "y"])]),
  morphism "gf" "Line" "Line" (.pullback [("t", .product [n 2, .pow (c "t") 2])]),
  morphism "idP" "Plane" "Plane" .identity,
  morphism "eighteen" "Pt" "Line" (.pullback [("t", n 18)]),
  decl "compose" (.primitive (.smoothCompose (path "Smooth"))),
  decl "same" (.primitive (.smoothEqual (path "Smooth"))),
  decl "composite" (.primitive (.smoothComposite (path "Smooth"))),
  decl "line_at" (.primitive (.smoothIntPoint (path "Smooth") (path "Line") (path "Pt"))) ]

/-- The Stage 2 profile, to check that the two kinds of object stay apart. -/
private def presented : List Source.Declaration := [
  decl "QQ" .marker,
  decl "AffineQQ" (.implementation (path "QQ") (.presentedAffine .rational) []),
  decl "AffineScheme" (.classification [] [path "AffineQQ"]),
  decl "Over" (.family ⟨[.object (path "AffineScheme"), .object (path "AffineScheme"),
    .object (path "AffineScheme")], [.structural 0 2, .structural 1 2], .relative⟩),
  decl "SpecQQ" (.affine (path "AffineQQ") [] [] none []),
  decl "QLine" (.affine (path "AffineQQ") ["t"] [] (some (path "SpecQQ")) []) ]

private def program (ds := declarations) : Source.Program := {
  file := "smooth objects", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := {path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {}}
    declarations := ds }], none⟩] }

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"smooth object regression failed: {label}")

private def with' (extra : List Source.Declaration) : Source.Program := program (declarations ++ extra)

private def code (p : Source.Program) : String :=
  match Source.checkDeclarations p with
  | .ok _ => "accepted"
  | .error e => e.code

private def message (p : Source.Program) : String :=
  match Source.checkDeclarations p with
  | .ok _ => ""
  | .error e => e.message

private def resolved : Option Core.Declarations :=
  match Source.checkDeclarations program with
  | .ok checked => some checked.resolved.declarations
  | .error _ => none

private def binding (name : String) : Option PrimitiveBinding := resolved.bind (·.primitive? (id name))

private def mapOf (name : String) : Option Map :=
  match binding name with
  | some (.smoothConstant _ map) => some map
  | _ => none

#eval check "the common source checker accepts smooth objects and maps" (code program == "accepted")
#eval check "declaration order independent" (code (program declarations.reverse) == "accepted")
#eval check "smooth and presented objects coexist" (code (with' presented) == "accepted")
#eval check "a smooth object keeps its coordinates"
  ((resolved.bind fun env => smoothCoordinates? env.indexed (id "Plane")) == some ["x", "y"])
#eval check "a smooth object is not a presented object"
  ((resolved.bind fun env => affineData? env.indexed (id "Plane")).isNone)
#eval check "a smooth object has no base chain"
  ((resolved.bind fun env => chainOf env.indexed (id "Plane")).isNone)
#eval check "f is t ↦ (t, t²) in target-coordinate order"
  (mapOf "f" == some ⟨1, [], [Poly.var 1 0, Poly.pow 1 (Poly.var 1 0) 2]⟩)
#eval check "g is (x, y) ↦ x² + y"
  (mapOf "g" == some ⟨2, [], [Poly.add (Poly.pow 2 (Poly.var 2 0) 2) (Poly.var 2 1)]⟩)
#eval check "identity is the runtime identity" (mapOf "idP" == some (SmoothRuntime.identity 2))
#eval check "compose builds a node, and it denotes gf"
  (match mapOf "g", mapOf "f", mapOf "gf" with
   | some g, some f, some gf =>
     SmoothRuntime.same (.compose (.primitive g) (.primitive f)) (.primitive gf) &&
       SmoothRuntime.composite (.compose (.primitive g) (.primitive f)) == .primitive gf
   | _, _, _ => false)
#eval check "pullback images are stored in target-coordinate order"
  (code (program (declarations.map fun d => if d.name == "f" then
    morphism "f" "Line" "Plane" (.pullback [("y", .pow (c "t") 2), ("x", c "t")]) else d)) == "accepted")

-- An executable Core module over the checked declarations, also compiled by
-- the native fixture script.
private def smoothType (x y : String) : Core.Result :=
  ⟨.indexed ⟨id "Smooth", [.object (.global (id x)), .object (.global (id y))]⟩, none⟩
private def constant (name x y : String) : Core.Term := .primitive (id name) [] (smoothType x y)
private def composeTerm (after before : Core.Term) (x y : String) : Core.Term :=
  .primitive (id "compose") [after, before] (smoothType x y)
private def sameTerm (left right : Core.Term) : Core.Term := .primitive (id "same") [left, right] ⟨.pure .bool, none⟩
private def guarded (condition : Core.Term) (code : Int) (rest : Core.Term) : Core.Term :=
  .branch condition rest (.integer code) ⟨.pure .int, none⟩
private def gAfterF : Core.Term := composeTerm (constant "g" "Plane" "Line") (constant "f" "Line" "Plane") "Line" "Line"
private def smoothMain : Core.Function := {
  id := 0, definition := id "main", parameters := [], returnType := .pure .int
  body :=
    guarded (sameTerm gAfterF (constant "gf" "Line" "Line")) 1 <|
    guarded (sameTerm (.primitive (id "composite") [gAfterF] (smoothType "Line" "Line"))
      (constant "gf" "Line" "Line")) 2 <|
    guarded (sameTerm (composeTerm (constant "gf" "Line" "Line")
        (.primitive (id "line_at") [.integer 3] (smoothType "Pt" "Line")) "Pt" "Line")
      (constant "eighteen" "Pt" "Line")) 3 <|
    guarded (sameTerm (composeTerm (constant "idP" "Plane" "Plane") (constant "f" "Line" "Plane") "Line" "Plane")
      (constant "f" "Line" "Plane")) 4 <|
    .integer 42 }

/-- The smooth programs of this regression as one audited Core module. -/
def smoothFixture : Core.Module := ⟨resolved.getD default, [smoothMain], some 0⟩

#eval check "the smooth Core module is accepted" (Core.Typing.checkModule smoothFixture true).isOk
#eval check "the smooth Core module evaluates to 42"
  (Core.Semantics.eval smoothFixture 64 (fun _ => none) smoothMain.body == some (Core.Semantics.Value.integer 42))
#eval check "the smooth Core module imports the smooth runtime" (match Core.Typing.checkModule smoothFixture true with
  | .ok checked => match Core.Codegen.generate checked with
    | .ok source => (source.splitOn "import VastitasKernel.SmoothRuntime\n").length == 2
    | .error _ => false
  | .error _ => false)
private def wrongMiddle : Core.Term :=
  guarded (sameTerm (composeTerm (constant "f" "Line" "Plane") (constant "f" "Line" "Plane") "Line" "Plane")
    (constant "f" "Line" "Plane")) 1 (.integer 42)
#eval check "a wrong middle object is rejected by the Core audit"
  (!(Core.Typing.checkModule ⟨resolved.getD default, [{ smoothMain with body := wrongMiddle }], some 0⟩
    true).isOk)

-- Source rejections with specific codes.
#eval check "spec under a smooth implementation"
  (code (with' [decl "Bad" (.affine (path "SmoothR") ["t"] [] none [])]) == "E_SMOOTH")
#eval check "a principal open under a smooth implementation"
  (code (with' (presented ++ [decl "Bad" (.affineLocalization (path "SmoothR") (path "QLine") (c "t") "u")]))
    == "E_SMOOTH")
#eval check "Affine(n) under a presented implementation"
  (code (with' (presented ++ [space "Bad" 1 ["t"] "AffineQQ"])) == "E_SMOOTH")
#eval check "Affine(n) under a descriptor implementation"
  (code (with' [decl "Grid" (.implementation (path "CInfReal") .affineDescriptor []),
    space "Bad" 1 ["t"] "Grid"]) == "E_SMOOTH")
#eval check "the presented message names the implementation"
  (((message (with' (presented ++ [space "Bad" 1 ["t"] "AffineQQ"]))).splitOn "AffineQQ").length > 1)
#eval check "dimension differs from the number of coordinates"
  (code (with' [space "Bad" 2 ["t"]]) == "E_SMOOTH")
#eval check "duplicate coordinates" (code (with' [space "Bad" 2 ["t", "t"]]) == "E_SMOOTH")
#eval check "dimension above the generator limit"
  (code (with' [space "Bad" 17 ((List.range 17).map (s!"x{·}"))]) == "E_LIMIT")
#eval check "a 16-dimensional object is accepted"
  (code (with' [space "Big" 16 ((List.range 16).map (s!"x{·}"))]) == "accepted")
#eval check "a smooth implementation has no globals"
  (code (with' [decl "G" (.global (path "SmoothR"))]) == "E_SMOOTH")
#eval check "a smooth_int_point needs a 0-dimensional point object"
  (code (with' [decl "bad" (.primitive (.smoothIntPoint (path "Smooth") (path "Plane") (path "Line")))])
    == "E_SMOOTH")
#eval check "a smooth_int_point needs smooth objects"
  (code (with' (presented ++ [decl "bad" (.primitive (.smoothIntPoint (path "Smooth") (path "Line")
    (path "SpecQQ")))])) == "E_SMOOTH")
#eval check "a foreign coordinate in an image"
  (code (with' [morphism "bad" "Line" "Plane" (.pullback [("x", c "s"), ("y", c "t")])]) == "E_AFFINE_COORDINATE")
#eval check "target coordinates in an image (swapped variance)"
  (code (with' [morphism "bad" "Line" "Plane" (.pullback [("x", c "x"), ("y", c "t")])]) == "E_AFFINE_COORDINATE")
#eval check "a missing target coordinate"
  (code (with' [morphism "bad" "Line" "Plane" (.pullback [("x", c "t")])]) == "E_AFFINE_COORDINATE")
#eval check "a source coordinate named as a target coordinate"
  (code (with' [morphism "bad" "Line" "Plane" (.pullback [("t", c "t"), ("y", c "t")])]) == "E_AFFINE_COORDINATE")
#eval check "a degree above the limit" (code (with' [morphism "bad" "Line" "Line"
  (.pullback [("t", .pow (c "t") 17)])]) == "E_LIMIT")
#eval check "identity needs the same object"
  (code (with' [morphism "bad" "Line" "Plane" .identity]) == "E_SMOOTH")
#eval check "a smooth map has no structure map"
  (code (with' [morphism "bad" "Line" "Line" .structureMap]) == "E_SMOOTH")
#eval check "a smooth map between presented objects"
  (code (with' (presented ++ [morphism "bad" "QLine" "QLine" .identity])) == "E_SMOOTH")
#eval check "a relative map between smooth objects"
  (code (with' (presented ++ [decl "bad" (.morphism (path "Over") [path "Line", path "Line", path "Pt"]
    (.pullback [("t", c "t")]))])) == "E_AFFINE_BASE")
#eval check "smooth families need exactly the canonical constraints"
  (code (program (declarations.map fun d => if d.name == "Smooth" then decl "Smooth"
    (.family (smoothFamily [.canonical 0])) else d)) == "E_TYPE")
#eval check "smooth families range over smooth objects only"
  (code (with' (presented ++ [decl "BadSmooth" (.family (smoothFamily [.canonical 0, .canonical 1]
    "AffineScheme"))])) == "E_TYPE")
#eval check "a relative family cannot range over smooth objects"
  (code (with' [decl "BadOver" (.family ⟨[.object (path "CInfAffine"), .object (path "CInfAffine"),
    .object (path "CInfAffine")], [.structural 0 2, .structural 1 2], .relative⟩)]) == "E_TYPE")
#eval check "a smooth representation needs no capabilities"
  (code (with' [decl "Caps" (.implementation (path "CInfReal") .smoothAffine [.dimension])]) == "E_TYPE")
#eval check "a smooth representation needs a real coefficient marker"
  (code (with' [decl "Complex" (.implementation (path "CInfReal") (.scalarBase .scheme .complex) [])])
    == "E_TYPE")

-- Tampered Core: the independent audit rechecks every map.
private def tamper (name : String) (edit : Map → Map) : Bool :=
  match resolved with
  | some env => !Core.validDeclarations { env with primitives := env.primitives.map fun entry =>
      match entry.binding with
      | .smoothConstant application map =>
        if entry.id == id name then ⟨entry.id, .smoothConstant application (edit map)⟩ else entry
      | _ => entry }
  | none => false
#eval check "accepted Core is valid" (resolved.map Core.validDeclarations == some true)
#eval check "forged arity" (tamper "f" fun m => {m with arity := 2})
#eval check "forged image count" (tamper "f" fun m => {m with images := [Poly.var 1 0]})
#eval check "forged nonzero basis" (tamper "f" fun m => {m with basis := [Poly.var 1 0]})
#eval check "forged non-canonical image"
  (tamper "f" fun m => {m with images := [[⟨[1], 1⟩, ⟨[1], 1⟩], Poly.var 1 0]})
#eval check "forged zero coefficient" (tamper "f" fun m => {m with images := [[⟨[1], 0⟩], Poly.var 1 0]})
#eval check "forged image in the wrong arity" (tamper "f" fun m => {m with images := [Poly.var 2 0, Poly.var 1 0]})
private def tamperIndexed (edit : Environment → Environment) : Bool :=
  match resolved with
  | some env => !Core.validDeclarations { env with indexed := edit env.indexed }
  | none => false
#eval check "forged duplicate coordinates" (tamperIndexed fun env => env.map fun entry =>
  if entry.id == id "Plane" then ⟨entry.id, .smoothAffine (id "SmoothR") ["x", "x"]⟩ else entry)
#eval check "forged smooth global" (tamperIndexed fun env => env ++ [⟨id "G", .global (id "SmoothR")⟩])
#eval check "forged smooth_int_point to a 1-dimensional point" (match resolved with
  | some env => !Core.validDeclarations { env with primitives := env.primitives ++
      [⟨id "bad", .smoothIntPoint (id "Smooth") (id "Plane") (id "Line")⟩] }
  | none => false)
#eval check "forged smooth constant on a relative application" (match resolved with
  | some env => !Core.validDeclarations { env with primitives := env.primitives ++
      [⟨id "bad", .smoothConstant ⟨id "Smooth", [.object (.global (id "Line"))]⟩ ⟨1, [], []⟩⟩] }
  | none => false)

-- Protocols 7 and 8 do not admit the smooth forms; protocol 9 does.
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
  [("kind", Json.str kind), ("name", Json.str "X"), ("public", Json.bool true),
   ("span", spanJson)]
open Lean in
private def smoothObject : Json := Json.mkObj (common "smooth_affine" ++
  [("implementation", pathJson "SmoothR"), ("dimension", Json.str "1"), ("coordinates", Json.arr #[Json.str "t"])])
open Lean in
private def smoothImplementation : Json := Json.mkObj (common "implementation" ++
  [("marker", pathJson "CInfReal"), ("representation", Json.str "smooth_affine"), ("capabilities", Json.arr #[])])
open Lean in
private def primitiveJson (op : String) : Json := Json.mkObj (common "primitive" ++
  [("binding", Json.mkObj [("op", Json.str op), ("family", pathJson "Smooth")])])
open Lean in
private def familyJson (representation : String) (constraint : Json) : Json := Json.mkObj (common "family" ++
  [("parameters", Json.arr #[]), ("constraints", Json.arr #[constraint]),
   ("representation", Json.str representation)])
open Lean in
private def canonicalJson : Json := Json.mkObj [("kind", Json.str "canonical"), ("object", (0 : Nat))]
open Lean in
private def sameObjectJson : Json :=
  Json.mkObj [("kind", Json.str "same_object"), ("left", (0 : Nat)), ("right", (1 : Nat))]

#eval check "protocol 9 decodes a smooth object" (decodes smoothObject true)
#eval check "protocols 7 and 8 reject a smooth object" (!decodes smoothObject false)
#eval check "protocol 9 decodes a smooth implementation" (decodes smoothImplementation true)
#eval check "protocols 7 and 8 reject a smooth implementation" (!decodes smoothImplementation false)
#eval check "protocol 9 decodes a smooth family" (decodes (familyJson "smooth" canonicalJson) true)
#eval check "protocols 7 and 8 reject a smooth family" (!decodes (familyJson "smooth" sameObjectJson) false)
#eval check "protocols 7 and 8 reject a canonical constraint" (!decodes (familyJson "token" canonicalJson) false)
#eval check "protocol 9 decodes each smooth primitive"
  (["smooth_compose", "smooth_equal", "smooth_composite"].all fun op => decodes (primitiveJson op) true)
#eval check "protocols 7 and 8 reject each smooth primitive"
  (["smooth_compose", "smooth_equal", "smooth_composite"].all fun op => !decodes (primitiveJson op) false)
#eval check "the primitive allow-list rejects unlisted spellings"
  (["smooth_gradient", "relative_gradient", "relative_", "smooth_"].all fun op => !decodes (primitiveJson op) true)
open Lean in
#eval check "a smooth object rejects extra fields"
  (!decodes (smoothObject.setObjVal! "map" (Json.arr #[])) true)
open Lean in
#eval check "a smooth dimension is a decimal string"
  (!decodes (smoothObject.setObjVal! "dimension" (Json.str "-1")) true &&
    !decodes (smoothObject.setObjVal! "dimension" (1 : Nat)) true)

end VastitasKernel.Indexed.SmoothObjectRegression
