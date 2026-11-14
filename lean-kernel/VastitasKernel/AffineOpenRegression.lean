import VastitasKernel.IndexedSourceChecker
import VastitasKernel.RegressionSupport

/-! Principal opens and the structure-sheaf action of declared morphisms
through the actual common source checker. These are executable regressions,
not proofs. -/
namespace VastitasKernel.Indexed.AffineOpenRegression

open AlgebraRuntime

private def pkg : Namespace.PackageId := ⟨"/opens/Vastitas.toml", "opens", "0.1.0"⟩
private def id (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩
private def path (name : String) : Source.Path := ⟨[name], {}⟩
private def decl (name : String) (body : Source.Body) : Source.Declaration := ⟨name, body, true, {}⟩
private def c (name : String) : Source.PolyExpr := .coordinate name
private def n (value : Nat) : Source.PolyExpr := .natural value
private def affine (name : String) (generators : List String) (relations : List Source.PolyExpr)
    (base : Option String := none) (bindings : List (String × Source.PolyExpr) := []) :
    Source.Declaration :=
  decl name (.affine (path "AffineQQ") generators relations (base.map path) bindings)
private def localize (name object : String) (element : Source.PolyExpr) (inverse : String) :
    Source.Declaration :=
  decl name (.affineLocalization (path "AffineQQ") (path object) element inverse)
private def morphism (name x y s : String) (definition : Source.MorphismDefinition) : Source.Declaration :=
  decl name (.morphism (path "Over") [path x, path y, path s] definition)

private def declarations : List Source.Declaration := [
  decl "QQ" .marker,
  decl "AffineQQ" (.implementation (path "QQ") (.presentedAffine .rational) []),
  decl "AffineScheme" (.classification [] [path "AffineQQ"]),
  decl "Over" (.family ⟨[.object (path "AffineScheme"), .object (path "AffineScheme"),
    .object (path "AffineScheme")], [.structural 0 2, .structural 1 2], .relative⟩),
  affine "SpecQQ" [] [],
  affine "Line" ["t"] [] "SpecQQ",
  localize "Dt" "Line" (c "t") "u",
  localize "Dt2" "Line" (.pow (c "t") 2) "v",
  morphism "sq" "Line" "Line" "SpecQQ" (.pullback [("t", .pow (c "t") 2)]),
  morphism "onOpens" "Dt2" "Dt" "SpecQQ" (.restrict (path "sq")),
  morphism "inclusion" "Dt" "Line" "Line" .structureMap,
  -- #104's transition: D(x) ≅ D(y) by y = 1/x.
  affine "L1" ["x"] [] "SpecQQ",
  affine "L2" ["y"] [] "SpecQQ",
  localize "U1" "L1" (c "x") "xi",
  localize "U2" "L2" (c "y") "yi",
  morphism "glue" "U1" "U2" "SpecQQ" (.pullback [("y", c "xi"), ("yi", c "x")]),
  morphism "unglue" "U2" "U1" "SpecQQ" (.pullback [("x", c "yi"), ("xi", c "y")]),
  decl "transition" (.iso (path "glue") (path "unglue")),
  -- D(0) is the zero ring.
  localize "Empty" "Line" (n 0) "z",
  -- D(1) is the whole line, where the inverse reduces to 1.
  morphism "lineId" "Line" "Line" "SpecQQ" .identity,
  localize "One" "Line" (n 1) "w",
  morphism "oneId" "One" "One" "SpecQQ" (.restrict (path "lineId")),
  -- An open of an open, restricted along a restriction.
  localize "E1" "Dt" (.sum [c "t", n 1]) "a",
  localize "E2" "Dt2" (.sum [.pow (c "t") 2, n 1]) "b",
  morphism "deeper" "E2" "E1" "SpecQQ" (.restrict (path "onOpens")) ]

private def program (ds := declarations) : Source.Program := {
  file := "affine opens", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := {path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {}}
    declarations := ds }], none⟩] }

private def check := RegressionSupport.check "affine open regression failed"

private def with' (extra : List Source.Declaration) : Source.Program := program (declarations ++ extra)

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

#eval check "the common source checker accepts opens and restrictions" (code (program) == "accepted")
#eval check "declaration order independent" (code (program declarations.reverse) == "accepted")
#eval check "D(t) is QQ[t, u]/(t u - 1) over the line"
  ((data "Dt").map (·.generators) == some ["t", "u"] && (data "Dt").bind (·.base) == some (id "Line") &&
    (data "Dt").map (·.basis) == some [Poly.sub (Poly.mul (Poly.var 2 0) (Poly.var 2 1)) (Poly.one 2)])
#eval check "restrict acts on the structure sheaf: t ↦ t², u ↦ v"
  ((mapOf "onOpens").map (·.images) == some [Poly.pow 2 (Poly.var 2 0) 2, Poly.var 2 1])
#eval check "the open inclusion is the structure map" ((mapOf "inclusion").map (·.images) == some [Poly.var 2 0])
#eval check "D(0) is the zero ring" ((data "Empty").map (·.basis) == some [Poly.one 2])
#eval check "a restriction of a restriction: t ↦ t², u ↦ v, a ↦ b"
  ((mapOf "deeper").map (·.images) == some [Poly.pow 3 (Poly.var 3 0) 2, Poly.var 3 1, Poly.var 3 2])
#eval check "restricted images are normal forms in the source open: w ↦ 1"
  ((mapOf "oneId").map (·.images) == some [Poly.var 2 0, Poly.one 2])

-- Rejections with specific codes.
#eval check "restrict needs the preimage open"
  (code (with' [morphism "bad" "Dt" "Dt" "SpecQQ" (.restrict (path "sq"))]) == "E_AFFINE_BASE")
#eval check "restrict needs principal opens"
  (code (with' [morphism "bad" "Line" "Dt" "SpecQQ" (.restrict (path "sq"))]) == "E_AFFINE_BASE")
#eval check "restrict needs a declared morphism"
  (code (with' [morphism "bad" "Dt2" "Dt" "SpecQQ" (.restrict (path "transition"))]) != "accepted")
#eval check "a transition that is not an isomorphism"
  (code (with' [morphism "glue2" "U1" "U2" "SpecQQ" (.pullback [("y", c "xi"), ("yi", .pow (c "x") 2)])])
    == "E_AFFINE_RELATION")
#eval check "restrictions that form a cycle"
  (code (with' [morphism "loopA" "Dt2" "Dt" "SpecQQ" (.restrict (path "loopB")),
    morphism "loopB" "Dt2" "Dt" "SpecQQ" (.restrict (path "loopA"))]) == "E_TYPE")
private def coordinates : List String := (List.range 15).map (s!"x{·}")
#eval check "the restrict preimage substitution is budgeted"
  (code (with' [affine "Y15" coordinates [] "SpecQQ",
    morphism "spread" "Y15" "Line" "SpecQQ" (.pullback [("t", .sum (coordinates.map c))]),
    localize "U15" "Y15" (c "x0") "w15", localize "V16" "Line" (.pow (c "t") 16) "z16",
    morphism "bad" "U15" "V16" "SpecQQ" (.restrict (path "spread"))]) == "E_LIMIT")
#eval check "the localized element uses the object's coordinates"
  (code (with' [localize "Bad" "Line" (c "x") "w"]) == "E_AFFINE_COORDINATE")
#eval check "the inverse coordinate is fresh" (code (with' [localize "Bad" "Line" (c "t") "t"]) == "E_AFFINE_COORDINATE")
#eval check "a principal open of a missing object" (code (with' [localize "Bad" "Missing" (c "t") "w"]) != "accepted")

-- Tampered Core: the audit re-derives every principal open.
private def tamper (name : String) (edit : AlgebraDeclarations.AffineData → AlgebraDeclarations.AffineData) :
    Bool :=
  match resolved with
  | some env => !Core.validDeclarations { env with indexed := env.indexed.map fun entry =>
      match entry.declaration with
      | .affine implementation d => if entry.id == id name then ⟨entry.id, .affine implementation (edit d)⟩ else entry
      | _ => entry }
  | none => false
#eval check "accepted Core is valid" (resolved.map Core.validDeclarations == some true)
#eval check "forged localized element" (tamper "Dt" fun d => match d.construction with
  | .localization o _ i rel => {d with construction := .localization o (Poly.one 1) i rel}
  | _ => d)
#eval check "forged open relations" (tamper "Dt" fun d => match d.construction with
  | .localization o e i _ => {d with construction := .localization o e i [], basis := [], cofactors := []}
  | _ => d)
#eval check "forged open base" (tamper "Dt" fun d => {d with base := some (id "SpecQQ")})

end VastitasKernel.Indexed.AffineOpenRegression
