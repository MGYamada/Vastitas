import VastitasKernel.AlgebraBasis
import Lean.Data.Json

/-! Cross-check the kernel's exact Gröbner bases and normal forms against the
independent Python reference fixture `tests/fixtures/algebra-bases.json`
(`scripts/affine_algebra_reference.py`). Adversarial certificates and limit
boundaries follow. These are executable regressions, not proofs. -/
namespace VastitasAlgebraTest.BasisRegression

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.AlgebraBasis Lean

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"algebra basis regression failed: {label}")

private def rational (text : String) : Except String Rat :=
  match text.splitOn "/" with
  | [n] => match n.toInt? with
    | some value => pure value
    | none => throw s!"bad rational {text}"
  | [n, d] => match n.toInt?, d.toNat? with
    | some num, some den => if den == 0 then throw "zero denominator" else pure (mkRat num den)
    | _, _ => throw s!"bad rational {text}"
  | _ => throw s!"bad rational {text}"

private def term (json : Json) : Except String AlgebraRuntime.Term := do
  let #[exponents, coefficient] ← json.getArr? | throw "term must be a pair"
  let exponents ← (← exponents.getArr?).toList.mapM fun e => e.getNat?
  pure ⟨exponents, ← rational (← coefficient.getStr?)⟩

private def poly (json : Json) : Except String Poly := do
  (← json.getArr?).toList.mapM term

private def polys (json : Json) : Except String (List Poly) := do
  (← json.getArr?).toList.mapM poly

structure Case where
  name : String
  arity : Nat
  relations : List Poly
  basis : List Poly
  normalForms : List (Poly × Poly)

private def decodeCase (json : Json) : Except String Case := do
  let normalForms ← (← (← json.getObjVal? "normalForms").getArr?).toList.mapM fun pair => do
    let #[input, output] ← pair.getArr? | throw "normal form must be a pair"
    pure (← poly input, ← poly output)
  pure {
    name := ← (← json.getObjVal? "name").getStr?
    arity := ← (← json.getObjVal? "arity").getNat?
    relations := ← polys (← json.getObjVal? "relations")
    basis := ← polys (← json.getObjVal? "basis")
    normalForms }

private def fixture : Except String (List Case) := do
  let json ← Json.parse (include_str "../../tests/fixtures/algebra-bases.json")
  unless (← (← json.getObjVal? "order").getStr?) == "degLex" do throw "unexpected monomial order"
  (← (← json.getObjVal? "cases").getArr?).toList.mapM decodeCase

private def v (arity index : Nat) : Poly := Poly.var arity index

private def accepted (certificate : Certificate) : Bool := (run (verify certificate)).isOk

private def rejection (certificate : Certificate) : String :=
  match run (verify certificate) with
  | .ok _ => "accepted"
  | .error e => e.code

/-- No term of a normal form is divisible by a basis leading monomial. -/
private def fullyReduced (basis : List Poly) (p : Poly) : Bool :=
  p.all fun t => (leadingMonomials basis).all fun m => !m.divides t.monomial

#eval show IO Unit from do
  let cases ← IO.ofExcept fixture
  check "fixture has cases" (cases.length ≥ 10)
  for c in cases do
    check s!"{c.name}: fixture input is canonical" (c.relations.all (Poly.canonical c.arity))
    match run (certify c.arity c.relations) with
    | .error e => throw (IO.userError s!"{c.name}: kernel rejected the fixture: {e.message}")
    | .ok certificate =>
      check s!"{c.name}: same reduced basis as the reference" (certificate.basis == c.basis)
      check s!"{c.name}: stored certificate verifies again" (accepted certificate)
      for (input, output) in c.normalForms do
        check s!"{c.name}: same normal form as the reference" (normalForm c.basis input == output)
        check s!"{c.name}: normal form is fully reduced" (fullyReduced c.basis output)
        let division := AlgebraRuntime.divide c.basis input
        check s!"{c.name}: division identity is exact"
          (Poly.add (combination division.quotients c.basis) division.remainder == input)

-- The dual numbers keep ε and kill ε².
private def dual : List Poly := [Poly.pow 1 (v 1 0) 2]
#eval check "ε is nonzero in QQ[e]/(e²)" (normalForm dual (v 1 0) == v 1 0)
#eval check "ε² is zero in QQ[e]/(e²)" (normalForm dual (Poly.pow 1 (v 1 0) 2) == [])

-- Map order: (t+1)² differs from t²+1.
private def sq : Map := ⟨1, [], [Poly.pow 1 (v 1 0) 2]⟩
private def shift : Map := ⟨1, [], [Poly.add (v 1 0) (Poly.one 1)]⟩
#eval check "pullback composition keeps the written order"
  ((Map.compose sq shift).coefficient 0 [1] == (2, 1) &&
    (Map.compose shift sq).coefficient 0 [1] == (0, 1))
#eval check "identity normalizes coordinates that the basis kills"
  ((Map.identity 2 [Poly.pow 2 (v 2 1) 2, v 2 0]).images == [[], v 2 1])

-- Adversarial certificates for QQ[x]/(x²).
private def square : Poly := Poly.pow 1 (v 1 0) 2
#eval check "forged unit basis without a cofactor identity"
  (rejection ⟨1, [square], [Poly.one 1], [[[]]]⟩ == "E_AFFINE_RELATION")
#eval check "omitted relation"
  (rejection ⟨2, [Poly.pow 2 (v 2 0) 2, v 2 1], [Poly.pow 2 (v 2 0) 2], [[Poly.one 2, []]]⟩ ==
    "E_AFFINE_RELATION")
private def xy : List Poly :=
  [Poly.sub (Poly.pow 2 (v 2 0) 2) (v 2 1), Poly.sub (Poly.mul (v 2 0) (v 2 1)) (Poly.one 2)]
#eval check "generators that are not a Gröbner basis"
  (rejection ⟨2, xy, xy, [[Poly.one 2, []], [[], Poly.one 2]]⟩ == "E_AFFINE_RELATION")
#eval check "non-monic basis" (rejection ⟨1, [square], [Poly.scale 2 square], [[Poly.const 1 2]]⟩ ==
  "E_AFFINE_RELATION")
#eval check "unordered basis" (rejection ⟨2, [v 2 1, v 2 0], [v 2 1, v 2 0],
  [[Poly.one 2, []], [[], Poly.one 2]]⟩ == "E_AFFINE_RELATION")
#eval check "non-reduced basis"
  (rejection ⟨1, [Poly.pow 1 (v 1 0) 3, square], [Poly.pow 1 (v 1 0) 3, square],
    [[Poly.one 1, []], [[], Poly.one 1]]⟩ == "E_AFFINE_RELATION")
#eval check "non-canonical relation" (rejection ⟨1, [[⟨[0], 0⟩]], [], []⟩ == "E_AFFINE_RELATION")
#eval check "wrong arity" (rejection ⟨2, [square], [square], [[Poly.one 1]]⟩ == "E_AFFINE_RELATION")
#eval check "cofactor table size" (rejection ⟨1, [square], [square], []⟩ == "E_AFFINE_RELATION")

-- Limit boundaries.
private def certifies (arity : Nat) (relations : List Poly) : String :=
  match run (certify arity relations) with
  | .ok _ => "ok"
  | .error e => e.code
#eval check "16 generators accepted" (certifies Limits.algebraGenerators [] == "ok")
#eval check "17 generators rejected" (certifies (Limits.algebraGenerators + 1) [] == "E_LIMIT")
#eval check "32 relations accepted"
  (certifies 1 ((List.range Limits.algebraRelations).map fun _ => square) == "ok")
#eval check "33 relations rejected"
  (certifies 1 ((List.range (Limits.algebraRelations + 1)).map fun _ => square) == "E_LIMIT")
#eval check "exhausted work budget is a limit, not an acceptance"
  (match (certify 2 xy).run (Limits.algebraWork - 4) with
    | .error (.limit _) => true
    | _ => false)
#eval check "term limit"
  (certifies 3 [Poly.pow 3 (Poly.add (Poly.add (v 3 0) (v 3 1)) (Poly.add (v 3 2) (Poly.one 3))) 16] ==
    "E_LIMIT")

end VastitasAlgebraTest.BasisRegression
