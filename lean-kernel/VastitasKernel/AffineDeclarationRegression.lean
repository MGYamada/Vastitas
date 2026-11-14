import VastitasKernel.IndexedSourceChecker
import VastitasKernel.RegressionSupport

/-! Presented affine declarations through the actual common source checker.
Objects are canonical declarations with exact bases and declared base chains;
the `structural` constraint compares object identity along those chains.
These are executable regressions, not proofs. -/
namespace VastitasKernel.Indexed.AffineDeclarationRegression

open AlgebraRuntime

private def pkg : Namespace.PackageId := ⟨"/affine/Vastitas.toml", "affine", "0.1.0"⟩
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

private def over : Source.Family :=
  ⟨[.object (path "AffineScheme"), .object (path "AffineScheme"), .object (path "AffineScheme")],
    [.structural 0 2, .structural 1 2], .token⟩

private def declarations : List Source.Declaration := [
  decl "QQ" .marker,
  decl "AffineQQ" (.implementation (path "QQ") (.presentedAffine .rational) []),
  decl "AffineScheme" (.classification [] [path "AffineQQ"]),
  decl "Over" (.family over),
  affine "SpecQQ" [] [],
  affine "Line" ["t"] [] "SpecQQ" [],
  affine "D" ["e"] [sq "e"] "SpecQQ",
  affine "S" ["t"] [] "SpecQQ",
  affine "X" ["t", "x"] [.sum [sq "x", .neg (c "t")]] "S" [("t", c "t")],
  affine "Origin" [] [] "S" [("t", n 0)],
  affine "DS" ["e"] [sq "e"] "S" [("t", n 0)] ]

private def program (ds := declarations) : Source.Program := {
  file := "affine declarations", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := {path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {}}
    declarations := ds }], none⟩] }

private def check := RegressionSupport.check "affine declaration regression failed"

private def change (name : String) (d : Source.Declaration) : Source.Program :=
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

private def overApp (x y s : String) : Application :=
  ⟨id "Over", [.object (.global (id x)), .object (.global (id y)), .object (.global (id s))]⟩

private def accepts (x y s : String) : Bool :=
  match resolved with
  | some env => validApplication env.indexed (overApp x y s)
  | none => false

#eval check "the common source checker accepts the profile" (code (program) == "accepted")
#eval check "declaration order independent" (code (program declarations.reverse) == "accepted")
#eval check "elaborated bases"
  ((data "X").map (·.basis) == some [Poly.sub (Poly.pow 2 (Poly.var 2 1) 2) (Poly.var 2 0)] &&
    (data "DS").map (·.basis) == some [Poly.pow 1 (Poly.var 1 0) 2] &&
    (data "SpecQQ").map (·.basis) == some [])
#eval check "ordered structure images"
  ((data "X").map (·.structureImages) == some [Poly.var 2 0] &&
    (data "Origin").map (·.structureImages) == some [[]] &&
    (data "Line").map (·.structureImages) == some [])
#eval check "base chains" (match resolved with
  | some env => chainOf env.indexed (id "X") == some [id "X", id "S", id "SpecQQ"] &&
      chainOf env.indexed (id "D") == some [id "D", id "SpecQQ"]
  | none => false)

-- `structural` follows declared chains, not markers or shapes.
#eval check "object over its own base" (accepts "X" "X" "S")
#eval check "point of X valued in DS over S" (accepts "DS" "X" "S")
#eval check "D-valued point of the line over SpecQQ" (accepts "D" "Line" "SpecQQ")
#eval check "a chain ancestor is a base" (accepts "X" "X" "SpecQQ")
#eval check "D is not over S" (!accepts "X" "D" "S")
#eval check "S is not over X" (!accepts "S" "X" "X")
#eval check "a same-shaped object is not on the chain" (!accepts "Line" "Line" "S")
#eval check "local brands never satisfy structural" (match resolved with
  | some env => !validApplication env.indexed ⟨id "Over",
      [.object (.local ⟨id "AffineScheme", id "QQ"⟩ 0), .object (.global (id "S")), .object (.global (id "S"))]⟩
  | none => false)

-- Source rejections.
#eval check "missing base binding" (code (change "X" (affine "X" ["t", "x"] [.sum [sq "x", .neg (c "t")]] "S")) ==
  "E_AFFINE_BASE")
#eval check "unknown base coordinate binding"
  (code (change "Origin" (affine "Origin" [] [] "S" [("t", n 0), ("u", n 0)])) == "E_AFFINE_BASE")
#eval check "a structure map must respect base relations"
  (code (change "DS" (affine "DS" ["e"] [] "D" [("e", c "e")])) == "E_AFFINE_BASE")
#eval check "binding into another object's coordinates"
  (code (change "Origin" (affine "Origin" [] [] "S" [("t", c "t")])) == "E_AFFINE_COORDINATE")
#eval check "unknown coordinate in a relation"
  (code (change "D" (affine "D" ["e"] [sq "x"] "SpecQQ")) == "E_AFFINE_COORDINATE")
#eval check "duplicate coordinate names"
  (code (change "Line" (affine "Line" ["t", "t"] [] "SpecQQ")) == "E_AFFINE_COORDINATE")
#eval check "degree 16 accepted, 17 rejected"
  (code (change "D" (affine "D" ["e"] [.pow (c "e") 16] "SpecQQ")) == "accepted" &&
    code (change "D" (affine "D" ["e"] [.pow (c "e") 17] "SpecQQ")) == "E_LIMIT" &&
    code (change "D" (affine "D" ["e"] [.product [.pow (c "e") 9, .pow (c "e") 8]] "SpecQQ")) == "E_LIMIT")
#eval check "64 digits accepted, 65 rejected"
  (code (change "D" (affine "D" ["e"] [.sum [c "e", .neg (n (10 ^ 63))]] "SpecQQ")) == "accepted" &&
    code (change "D" (affine "D" ["e"] [.sum [c "e", .neg (n (10 ^ 64))]] "SpecQQ")) == "E_LIMIT")
#eval check "zero denominator" (code (change "D" (affine "D" ["e"] [.fraction 1 0] "SpecQQ")) ==
  "E_AFFINE_COORDINATE")
#eval check "17 generators rejected"
  (code (change "Line" (affine "Line" ((List.range 17).map (s!"t{·}")) [] "SpecQQ")) == "E_LIMIT")
#eval check "a descriptor global is not a presented base"
  (code (program (declarations ++ [
    decl "Grid" (.implementation (path "QQ") .affineDescriptor []),
    decl "Fixed" (.global (path "Grid")),
    affine "Bad" ["u"] [] "Fixed" [] ])) == "E_AFFINE_BASE")
#eval check "cyclic bases" (code (program (declarations ++ [
    affine "A" ["a"] [] "B" [("b", c "a")], affine "B" ["b"] [] "A" [("a", c "b")] ])) ==
  "E_AFFINE_BASE")
private def tower : List Source.Declaration :=
  (List.range 17).map fun k => affine s!"T{k + 1}" [] [] (some (if k == 0 then "SpecQQ" else s!"T{k}")) []
#eval check "base chains of 16 accepted, 17 rejected"
  (code (program (declarations ++ tower.take 15)) == "accepted" &&
    code (program (declarations ++ tower)) == "E_LIMIT")

-- Presented objects stay outside descriptor contracts.
#eval check "a presented implementation cannot back a plain global"
  (code (program (declarations ++ [decl "Plain" (.global (path "AffineQQ"))])) != "accepted")
#eval check "presented implementations have no descriptor capabilities"
  (code (change "AffineQQ" (decl "AffineQQ" (.implementation (path "QQ") (.presentedAffine .rational) [.origin])))
    != "accepted")
#eval check "sealed point families reject presented objects" (code (program (declarations ++ [
    decl "BadPoint" (.family ⟨[.object (path "AffineScheme"), .object (path "AffineScheme")],
      [.sameBase 0 1], .point⟩) ])) != "accepted")
#eval check "a base with another coefficient marker" (code (program (declarations ++ [
    decl "RR" .marker,
    decl "AffineRR" (.implementation (path "RR") (.presentedAffine .rational) []),
    decl "Other" (.affine (path "AffineRR") ["r"] [] (some (path "SpecQQ")) []) ])) != "accepted")

-- Tampered Core is rejected by the independent declaration audit.
private def tamper (name : String) (edit : AlgebraDeclarations.AffineData → AlgebraDeclarations.AffineData) :
    Bool :=
  match resolved with
  | some env => !Core.validDeclarations { env with indexed := env.indexed.map fun entry =>
      match entry.declaration with
      | .affine implementation d => if entry.id == id name then ⟨entry.id, .affine implementation (edit d)⟩ else entry
      | _ => entry }
  | none => false
#eval check "accepted Core is valid" (resolved.map Core.validDeclarations == some true)
#eval check "forged empty basis" (tamper "X" fun d => {d with basis := [], cofactors := []})
#eval check "forged unit basis" (tamper "D" fun d => {d with basis := [Poly.one 1], cofactors := [[[]]]})
#eval check "forged structure image" (tamper "Origin" fun d => {d with structureImages := [Poly.one 0]})
#eval check "forged relation" (tamper "D" fun d => {d with construction := .presented []})
#eval check "forged base" (tamper "DS" fun d => {d with base := some (id "X")})
#eval check "dropped base" (tamper "X" fun d => {d with base := none})

end VastitasKernel.Indexed.AffineDeclarationRegression
