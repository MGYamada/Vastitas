import VastitasKernel.IndexedSourceChecker
import VastitasKernel.RegressionSupport

/-! Declared morphisms over a base through the actual common source checker.
These are executable regressions, not proofs. -/
namespace VastitasKernel.Indexed.AffineMorphismRegression

open AlgebraRuntime

private def pkg : Namespace.PackageId := ⟨"/morphisms/Vastitas.toml", "morphisms", "0.1.0"⟩
private def id (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩
private def path (name : String) : Source.Path := ⟨[name], {}⟩
private def decl (name : String) (body : Source.Body) : Source.Declaration := ⟨name, body, true, {}⟩
private def c (name : String) : Source.PolyExpr := .coordinate name
private def n (value : Nat) : Source.PolyExpr := .natural value
private def sq (name : String) : Source.PolyExpr := .pow (c name) 2
private def affine (name : String) (generators : List String) (relations : List Source.PolyExpr)
    (base : Option String := none) (bindings : List (String × Source.PolyExpr) := []) :
    Source.Declaration :=
  decl name (.affine (path "AffineQQ") generators relations (base.map path) bindings)
private def morphism (name x y s : String) (definition : Source.MorphismDefinition) : Source.Declaration :=
  decl name (.morphism (path "Over") [path x, path y, path s] definition)
/-- `relative_coefficient` of `Over` from `D` to `Line` in wire order; the algebra pass reads the
coordinate and the monomial back by field name. -/
private def coefficientOf (coordinate : String) (monomial : Source.PolyExpr) : Source.Body :=
  .primitive ⟨"relative_coefficient", [("family", .path (path "Over")), ("source", .path (path "D")),
    ("target", .path (path "Line")), ("coordinate", .coordinate coordinate),
    ("monomial", .polynomial monomial)]⟩
private def viewOf (source target : String) : Source.Body :=
  .primitive ⟨"relative_view", [("family", .path (path "Over")), ("source", .path (path source)),
    ("target", .path (path target))]⟩

private def over (constraints : List Constraint := [.structural 0 2, .structural 1 2]) : Source.Family :=
  ⟨[.object (path "AffineScheme"), .object (path "AffineScheme"), .object (path "AffineScheme")],
    constraints, .relative⟩

private def declarations : List Source.Declaration := [
  decl "QQ" .marker,
  decl "AffineQQ" (.implementation (path "QQ") (.presentedAffine .rational) []),
  decl "AffineScheme" (.classification [] [path "AffineQQ"]),
  decl "Over" (.family (over)),
  affine "SpecQQ" [] [],
  affine "Line" ["t"] [] "SpecQQ",
  affine "D" ["e"] [sq "e"] "SpecQQ",
  affine "S" ["t"] [] "SpecQQ",
  affine "X" ["t", "x"] [.sum [sq "x", .neg (c "t")]] "S" [("t", c "t")],
  affine "Y" ["u"] [] "S" [("t", sq "u")],
  affine "DS" ["e"] [sq "e"] "S" [("t", n 0)],
  morphism "p" "D" "Line" "SpecQQ" (.pullback [("t", c "e")]),
  morphism "toX" "DS" "X" "S" (.pullback [("t", n 0), ("x", c "e")]),
  morphism "root" "X" "Y" "S" (.pullback [("u", c "x")]),
  morphism "toS" "X" "S" "S" .structureMap,
  morphism "same" "X" "X" "S" .identity,
  decl "compose" (.primitive ⟨"relative_compose", [("family", .path (path "Over"))]⟩),
  decl "eps" (coefficientOf "t" (c "e")),
  decl "view" (viewOf "S" "SpecQQ") ]

private def program (ds := declarations) : Source.Program := {
  file := "affine morphisms", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := {path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {}}
    declarations := ds }], none⟩] }

private def check := RegressionSupport.check "affine morphism regression failed"

private def with' (extra : List Source.Declaration) : Source.Program := program (declarations ++ extra)

private def code (p : Source.Program) : String :=
  match Source.checkDeclarations p with
  | .ok _ => "accepted"
  | .error e => e.code

private def resolved : Option Core.Declarations :=
  match Source.checkDeclarations program with
  | .ok checked => some checked.resolved.declarations
  | .error _ => none

private def binding (name : String) : Option PrimitiveBinding := resolved.bind (·.primitive? (id name))

private def mapOf (name : String) : Option Map :=
  match binding name with
  | some (.relativeConstant _ map) => some map
  | _ => none

#eval check "the common source checker accepts declared morphisms" (code (program) == "accepted")
#eval check "declaration order independent" (code (program declarations.reverse) == "accepted")
#eval check "a D-valued point keeps e" ((mapOf "p").map (·.images) == some [Poly.var 1 0])
#eval check "a point of X over S" ((mapOf "toX").map (·.images) == some [[], Poly.var 1 0])
#eval check "a structure map is the stored chain image" ((mapOf "toS").map (·.images) == some [Poly.var 2 0])
#eval check "identity normal forms" ((mapOf "same").map (·.images) == some [Poly.var 2 0, Poly.var 2 1])
#eval check "coefficient selector elaborated to a target index and monomial"
  (binding "eps" == some (.relativeCoefficient (id "Over") (id "D") (id "Line") 0 [1]))

-- Source rejections with specific codes.
#eval check "a map that violates the target relations"
  (code (with' [morphism "bad" "D" "X" "SpecQQ" (.pullback [("t", n 1), ("x", c "e")])]) == "E_AFFINE_RELATION")
#eval check "swapped variance names source coordinates"
  (code (with' [morphism "bad" "D" "Line" "SpecQQ" (.pullback [("e", c "t")])]) == "E_AFFINE_COORDINATE")
#eval check "an image in the target's coordinates"
  (code (with' [morphism "bad" "D" "Line" "SpecQQ" (.pullback [("t", c "t")])]) == "E_AFFINE_COORDINATE")
#eval check "a map that does not commute with the structure maps"
  (code (with' [morphism "bad" "X" "Y" "S" (.pullback [("u", c "t")])]) == "E_AFFINE_BASE")
#eval check "identity needs the same object"
  (code (with' [morphism "bad" "D" "Line" "SpecQQ" .identity]) == "E_AFFINE_BASE")
#eval check "a structure map needs the target on the chain"
  (code (with' [morphism "bad" "D" "S" "SpecQQ" .structureMap]) == "E_AFFINE_BASE")
#eval check "absent structure map to the named base"
  (code (with' [morphism "bad" "D" "Line" "S" (.pullback [("t", c "e")])]) != "accepted")
#eval check "unknown coefficient coordinate"
  (code (with' [decl "bad" (coefficientOf "u" (c "e"))]) == "E_AFFINE_COORDINATE")
#eval check "coefficient selector must be a monomial"
  (code (with' [decl "bad" (coefficientOf "t" (.sum [c "e", n 1]))]) == "E_AFFINE_COORDINATE")
#eval check "a zero coefficient selector"
  (code (with' [decl "bad" (coefficientOf "t" (n 0))]) == "E_AFFINE_COORDINATE")
#eval check "a coefficient selector that cancels to zero"
  (code (with' [decl "bad" (coefficientOf "t" (.sum [c "e", .neg (c "e")]))]) == "E_AFFINE_COORDINATE")
#eval check "the constant coefficient selector is one"
  (code (with' [decl "constant" (coefficientOf "t" (n 1))]) == "accepted")

-- The result type of `relative_int_point` is fixed by the declaration, so the
-- declaration is checked against it (#737).
private def intPoint (name object base : String) : Source.Declaration :=
  decl name (.primitive ⟨"relative_int_point", [("family", .path (path "Over")), ("object", .path (path object)),
    ("base", .path (path base))]⟩)
private def diagnostic (p : Source.Program) : Option (String × String) :=
  match Source.checkDeclarations p with
  | .ok _ => none
  | .error e => some (e.code, e.message)
#eval check "a rational point of the line over its base" (code (with' [intPoint "at" "Line" "SpecQQ"]) == "accepted")
#eval check "a point object off the base chain of the object"
  (diagnostic (with' [affine "Pt2" [] [] "SpecQQ", intPoint "at2" "Line" "Pt2"]) == some ("E_TYPE",
    "the result type `Over<Pt2, Line, Pt2>` of the `relative_int_point` primitive `morphisms::at2` is not a " ++
      "valid type: `morphisms::Pt2` is not on the base chain of `morphisms::Line`"))

-- Substitution is budgeted: small sources whose expansions are huge fail with E_LIMIT.
private def coordinates : List String := (List.range 16).map (s!"x{·}")
#eval check "substituting a 16-term image into t^16 exceeds the budget"
  (code (with' [affine "Free" coordinates [] "SpecQQ", affine "T16" ["t"] [.pow (c "t") 16] "SpecQQ",
    morphism "bad" "Free" "T16" "SpecQQ" (.pullback [("t", .sum (coordinates.map c))])]) == "E_LIMIT")
private def level (k : Nat) : Source.Declaration :=
  affine s!"S{k + 1}" [s!"a{k + 1}"] [] s!"S{k}" [(s!"a{k}", .pow (.sum [c s!"a{k + 1}", n 1]) 16)]
#eval check "composing structure maps along a base chain exceeds the budget"
  (code (with' ([affine "S0" ["a0"] []] ++ (List.range 3).map level ++
    [morphism "bad" "S3" "S0" "S0" .structureMap])) == "E_LIMIT")
#eval check "a shorter chain composes within the budget"
  (code (with' ([affine "S0" ["a0"] []] ++ (List.range 2).map level ++
    [morphism "fine" "S2" "S0" "S0" .structureMap])) == "accepted")
#eval check "a view needs the target base on the chain"
  (code (with' [decl "bad" (viewOf "SpecQQ" "S")]) != "accepted")
#eval check "relative families need exactly the structural constraints"
  (code (program (declarations.map fun d => if d.name == "Over" then decl "Over" (.family (over [.structural 0 2]))
    else d)) != "accepted")
#eval check "relative families range over presented objects only"
  (code (with' [decl "Grid" (.implementation (path "QQ") .affineDescriptor []),
    decl "Grids" (.classification [] [path "Grid"]),
    decl "BadOver" (.family ⟨[.object (path "Grids"), .object (path "Grids"), .object (path "Grids")],
      [.structural 0 2, .structural 1 2], .relative⟩)]) != "accepted")

-- Tampered Core: the independent audit rechecks every map.
private def tamper (name : String) (edit : Map → Map) : Bool :=
  match resolved with
  | some env => !Core.validDeclarations { env with primitives := env.primitives.map fun entry =>
      match entry.binding with
      | .relativeConstant application map =>
        if entry.id == id name then ⟨entry.id, .relativeConstant application (edit map)⟩ else entry
      | _ => entry }
  | none => false
#eval check "accepted Core is valid" (resolved.map Core.validDeclarations == some true)
#eval check "forged image violating relations" (tamper "toX" fun m => {m with images := [Poly.one 1, Poly.var 1 0]})
#eval check "forged non-normal image" (tamper "p" fun m => {m with images := [Poly.pow 1 (Poly.var 1 0) 2]})
#eval check "forged basis" (tamper "p" fun m => {m with basis := []})
#eval check "forged arity" (tamper "p" fun m => {m with arity := 2})
#eval check "forged image count" (tamper "toS" fun m => {m with images := []})
#eval check "forged triangle" (tamper "root" fun m => {m with images := [Poly.var 2 0]})

-- Runtime composition keeps the written order.
private def line (images : List Poly) : Map := ⟨1, [], images⟩
#eval check "compose(sq, shift) is (t + 1)^2"
  ((Map.compose (line [Poly.pow 1 (Poly.var 1 0) 2]) (line [Poly.add (Poly.var 1 0) (Poly.one 1)])).images ==
    [Poly.pow 1 (Poly.add (Poly.var 1 0) (Poly.one 1)) 2])

end VastitasKernel.Indexed.AffineMorphismRegression
