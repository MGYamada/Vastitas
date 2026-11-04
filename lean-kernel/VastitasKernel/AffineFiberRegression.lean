import VastitasKernel.IndexedSourceChecker

/-! Fiber products, Cartesian evidence and base isomorphisms through the actual
common source checker. These are executable regressions, not proofs. -/
namespace VastitasKernel.Indexed.AffineFiberRegression

open AlgebraRuntime

private def pkg : Namespace.PackageId := ⟨"/fibers/Vastitas.toml", "fibers", "0.1.0"⟩
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
private def fiber (name left right : String)
    (via : Option (List (String × Source.PolyExpr) × List (String × Source.PolyExpr)) := none) :
    Source.Declaration :=
  decl name (.affineFiber (path "AffineQQ") (path left) (path right) via)
private def morphism (name x y s : String) (definition : Source.MorphismDefinition) : Source.Declaration :=
  decl name (.morphism (path "Over") [path x, path y, path s] definition)
private def cartesian (name first second fiber inverse : String) : Source.Declaration :=
  decl name (.cartesian (path first) (path second) (path fiber) (path inverse))

private def declarations : List Source.Declaration := [
  decl "QQ" .marker,
  decl "AffineQQ" (.implementation (path "QQ") (.presentedAffine .rational) []),
  decl "AffineScheme" (.classification [] [path "AffineQQ"]),
  decl "Over" (.family ⟨[.object (path "AffineScheme"), .object (path "AffineScheme"),
    .object (path "AffineScheme")], [.structural 0 2, .structural 1 2], .relative⟩),
  affine "SpecQQ" [] [],
  affine "S" ["t"] [] "SpecQQ",
  affine "X" ["t", "x"] [.sum [sq "x", .neg (c "t")]] "S" [("t", c "t")],
  affine "Origin" [] [] "S" [("t", n 0)],
  affine "DS" ["e"] [sq "e"] "S" [("t", n 0)],
  fiber "Fiber" "X" "Origin",
  morphism "toX" "DS" "X" "S" (.pullback [("t", n 0), ("x", c "e")]),
  morphism "toOrigin" "DS" "Origin" "S" (.pullback []),
  morphism "prX" "Fiber" "X" "S" .first,
  morphism "prO" "Fiber" "Origin" "S" .second,
  morphism "back" "Fiber" "DS" "S" (.pullback [("e", c "X::x")]),
  cartesian "fiberIsDual" "toX" "toOrigin" "Fiber" "back",
  decl "lift" (.primitive (.relativePair (path "Over") (path "Fiber"))),
  -- A separately declared copy of S, comparable only through a chosen isomorphism.
  affine "S2" ["t"] [] "SpecQQ",
  affine "Origin2" [] [] "S2" [("t", n 0)],
  fiber "Fiber2" "X" "Origin2" (some ([("t", c "t")], [("t", c "t")])),
  morphism "toS2" "S" "S2" "SpecQQ" (.pullback [("t", c "t")]),
  morphism "fromS2" "S2" "S" "SpecQQ" (.pullback [("t", c "t")]),
  decl "sameBase" (.iso (path "toS2") (path "fromS2")) ]

private def program (ds := declarations) : Source.Program := {
  file := "affine fibers", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := {path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {}}
    declarations := ds }], none⟩] }

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"affine fiber regression failed: {label}")

private def with' (extra : List Source.Declaration) : Source.Program := program (declarations ++ extra)
private def replacing (name : String) (d : Source.Declaration) : Source.Program :=
  program (declarations.map fun e => if e.name == name then d else e)

private def code (p : Source.Program) : String :=
  match Source.checkDeclarations p with
  | .ok _ => "accepted"
  | .error e => e.code

private def resolved : Option Core.Declarations :=
  match Source.checkDeclarations program with
  | .ok checked => some checked.resolved.declarations
  | .error _ => none

private def data (name : String) : Option AlgebraDeclarations.AffineData :=
  resolved.bind fun env => affineData? env.indexed (id name)

private def mapOf (name : String) : Option Map :=
  match resolved.bind (·.primitive? (id name)) with
  | some (.relativeConstant _ map) => some map
  | _ => none

#eval check "the common source checker accepts fibers and evidence" (code (program) == "accepted")
#eval check "declaration order independent" (code (program declarations.reverse) == "accepted")
#eval check "qualified fiber coordinates" ((data "Fiber").map (·.generators) == some ["X::t", "X::x"])
#eval check "the fiber of x^2 = t over the origin has basis [x^2, t]"
  ((data "Fiber").map (·.basis) == some [Poly.pow 2 (Poly.var 2 1) 2, Poly.var 2 0])
#eval check "the fiber lies over S" ((data "Fiber").bind (·.base) == some (id "S"))
#eval check "projections pick the factor coordinates"
  ((mapOf "prX").map (·.images) == some [[], Poly.var 2 1] && (mapOf "prO").map (·.images) == some [])
#eval check "a fiber over a separately declared base through a chosen isomorphism"
  ((data "Fiber2").map (·.basis) == some [Poly.pow 2 (Poly.var 2 1) 2, Poly.var 2 0])
#eval check "the pair contract names a plain fiber"
  ((resolved.bind (·.primitive? (id "lift"))) == some (.relativePair (id "Over") (id "Fiber")))
#eval check "pair concatenates factor images in the written order"
  (match mapOf "toX", mapOf "toOrigin" with
    | some f, some g => (Map.pair f g).images == f.images
    | _, _ => false)

#eval check "a self-product qualifies coordinates by occurrence"
  (match Source.checkDeclarations (with' [fiber "XX" "X" "X"]) with
    | .ok checked => (affineData? checked.resolved.declarations.indexed (id "XX")).map (·.generators) ==
        some ["first::t", "first::x", "second::t", "second::x"]
    | .error _ => false)
#eval check "a nested fiber nests its qualifiers"
  (match Source.checkDeclarations (with' [fiber "Nested" "Fiber" "Origin",
      decl "nx" (.primitive (.relativeCoefficient (path "Over") (path "DS") (path "Nested") "Fiber::X::x" (c "e")))]) with
    | .ok checked => (affineData? checked.resolved.declarations.indexed (id "Nested")).map (·.generators) ==
        some ["Fiber::X::t", "Fiber::X::x"]
    | .error _ => false)

-- Rejections with specific codes.
#eval check "different bases need a chosen isomorphism"
  (code (with' [fiber "Bad" "X" "Origin2"]) == "E_AFFINE_BASE")
#eval check "a base map that is not an isomorphism"
  (code (with' [fiber "Bad" "X" "Origin2" (some ([("t", sq "t")], [("t", c "t")]))]) == "E_AFFINE_RELATION")
#eval check "a base isomorphism must name every coordinate"
  (code (with' [fiber "Bad" "X" "Origin2" (some ([], [("t", c "t")]))]) == "E_AFFINE_BASE")
#eval check "a forged inverse in a Cartesian square"
  (code (replacing "back" (morphism "back" "Fiber" "DS" "S" (.pullback [("e", n 0)]))) == "E_AFFINE_RELATION")
#eval check "a square over a different base"
  (code (with' [affine "DS2" ["e"] [sq "e"] "S2" [("t", n 0)],
    morphism "toOrigin2" "DS2" "Origin2" "S2" (.pullback []),
    morphism "toX2" "DS2" "Origin2" "S2" (.pullback []),
    cartesian "bad" "toX2" "toOrigin2" "Fiber" "back"]) == "E_AFFINE_BASE")
#eval check "a square whose arrows miss the factors"
  (code (with' [cartesian "bad" "toOrigin" "toX" "Fiber" "back"]) == "E_AFFINE_BASE")
#eval check "a projection from a non-fiber" (code (with' [morphism "bad" "X" "S" "S" .first]) == "E_AFFINE_BASE")
#eval check "a projection to the wrong factor"
  (code (with' [morphism "bad" "Fiber" "Origin" "S" .first]) == "E_AFFINE_BASE")
#eval check "pair is not admitted for products through an isomorphism"
  (code (with' [decl "bad" (.primitive (.relativePair (path "Over") (path "Fiber2")))]) != "accepted")
#eval check "isomorphisms must compose to the identity"
  (code (with' [morphism "sq2" "S" "S2" "SpecQQ" (.pullback [("t", sq "t")]),
    decl "bad" (.iso (path "sq2") (path "fromS2"))]) == "E_AFFINE_RELATION")
#eval check "a fiber factor must be a presented object"
  (code (with' [fiber "Bad" "X" "Missing"]) != "accepted")

-- Tampered Core: the audit re-derives every fiber presentation.
private def tamper (name : String) (edit : AlgebraDeclarations.AffineData → AlgebraDeclarations.AffineData) :
    Bool :=
  match resolved with
  | some env => !Core.validDeclarations { env with indexed := env.indexed.map fun entry =>
      match entry.declaration with
      | .affine implementation d => if entry.id == id name then ⟨entry.id, .affine implementation (edit d)⟩ else entry
      | _ => entry }
  | none => false
#eval check "accepted Core is valid" (resolved.map Core.validDeclarations == some true)
#eval check "forged fiber relations" (tamper "Fiber" fun d => match d.construction with
  | .fiber l r v _ => {d with construction := .fiber l r v [], basis := [], cofactors := []}
  | _ => d)
#eval check "forged fiber coordinates" (tamper "Fiber" fun d => {d with generators := ["t", "x"]})
#eval check "forged fiber base" (tamper "Fiber" fun d => {d with base := some (id "SpecQQ")})
#eval check "dropped base isomorphism" (tamper "Fiber2" fun d => match d.construction with
  | .fiber l r _ rel => {d with construction := .fiber l r none rel}
  | _ => d)
#eval check "forged evidence maps" (match resolved with
  | some env => !Core.validDeclarations { env with primitives := env.primitives.map fun entry =>
      match entry.binding with
      | .relativeCartesian q1 q2 (application, map) fiber =>
        ⟨entry.id, .relativeCartesian q1 q2 (application, {map with images := [[]]}) fiber⟩
      | _ => entry }
  | none => false)

end VastitasKernel.Indexed.AffineFiberRegression
