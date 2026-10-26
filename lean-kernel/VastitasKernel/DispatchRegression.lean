import VastitasKernel.Dispatch

/-! Direct tests of the finite engine, independently of the source frontend and
monomorphizer. Synthetic hierarchies use the very same `checkWith` algorithm. -/
namespace VastitasKernel.Dispatch.Regression

private def expectError (label expected : String) (result : Except Error Checked) : IO Unit :=
  match result with
  | .error error => unless error.code == expected do
      throw (IO.userError s!"{label}: expected {expected}, got {error.code}: {error.message}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly accepted")

private def expectWinner (label : String) (key : Key) (id : Nat)
    (result : Except Error Checked) : IO Unit :=
  match result with
  | .error error => throw (IO.userError s!"{label}: {error.code}: {error.message}")
  | .ok checked => unless checked.winner key == some id do
      throw (IO.userError s!"{label}: wrong winner: {repr (checked.winner key)}")

private def method (id : Nat) (selectors : List Nat) (requirements : List String := []) : Method :=
  { id, selectors, requirements }

/-- 0 inherits both A=4 and B=5; 1 inherits only A and 2 only B.
All concrete types and both abstract parents inherit Top=6. -/
private def diamond : Hierarchy where
  nominalCount := 7
  concrete := [0, 1, 2, 3]
  subtype a b := a == b || b == 6 ||
    ((a == 0 || a == 1) && b == 4) || ((a == 0 || a == 2) && b == 5)
  facts _ := [.hasEq]

private def broadTriple : List Method :=
  [method 10 [4, 6, 6], method 11 [6, 4, 6], method 12 [6, 6, 4]]

private def pairRepairs : List Method :=
  [method 20 [4, 4, 6], method 21 [4, 6, 4], method 22 [6, 4, 4]]

#eval show IO Unit from do
  expectWinner "exact nominal" [0] 2 (check 1 [[0]] [method 1 [5], method 2 [0]])
  expectWinner "Number selector" [1] 2 (check 1 [[1]] [method 1 [5], method 2 [4]])
  expectWinner "capability product repair" [0] 3
    (check 1 [[0], [1]] [method 1 [4], method 2 [5] ["HasOrder"], method 3 [4] ["HasOrder"]])
  expectError "extensional containment is not specificity" "E_DISPATCH_AMBIGUOUS"
    (check 1 [[0]] [method 1 [4], method 2 [5] ["HasOrder"]])
  expectError "ambiguity outside D" "E_DISPATCH_AMBIGUOUS"
    (check 2 [[2, 2]] [method 1 [5, 5], method 2 [0, 5], method 3 [5, 0]])
  expectError "missing coverage" "E_DISPATCH_COVERAGE"
    (check 1 [[1]] [method 1 [0]])
  expectError "normalized requirements duplicate" "E_DISPATCH_DUPLICATE"
    (check 1 [[0]] [method 1 [5] ["HasOrder"], method 2 [5] ["HasEq", "HasOrder"]])
  expectError "repeated capability canonicalization" "E_DISPATCH_DUPLICATE"
    (check 1 [[0]] [method 1 [5] ["HasEq"], method 2 [5] ["HasEq", "HasEq"]])
  expectError "duplicate identities" "E_DISPATCH_DUPLICATE_ID"
    (check 1 [[0]] [method 1 [5], method 1 [0]])
  expectError "unsupported capability" "E_DISPATCH_CAPABILITY"
    (check 1 [[0]] [method 1 [5] ["HasMetric"]])
  expectError "unrealizable capability" "E_DISPATCH_UNREALIZABLE"
    (check 1 [] [method 1 [2] ["HasOrder"]])
  expectError "tuple capability intersection" "E_DISPATCH_UNREALIZABLE"
    (check 2 [] [method 1 [0, 2] ["HasOrder"]])
  expectWinner "zero argument empty requirement" [] 1 (check 0 [[]] [method 1 []])
  expectError "zero argument has no static facts" "E_DISPATCH_UNREALIZABLE"
    (check 0 [[]] [method 1 [] ["HasEq"]])
  expectError "nonconcrete domain" "E_DISPATCH_DOMAIN"
    (check 1 [[4]] [method 1 [5]])
  expectError "domain arity" "E_DISPATCH_DOMAIN"
    (check 1 [[0, 1]] [method 1 [5]])
  expectError "method arity" "E_DISPATCH_ARITY"
    (check 1 [[0]] [method 1 [0, 1]])
  expectError "selector outside hierarchy" "E_DISPATCH_SELECTOR"
    (check 1 [[0]] [method 1 [6]])
  expectError "key limit" "E_DISPATCH_LIMIT" (check 7 [] [])
  expectError "multiple inheritance ambiguity" "E_DISPATCH_AMBIGUOUS"
    (checkWith diamond 1 [[0]] [method 1 [4], method 2 [5]])
  expectWinner "multiple inheritance repair" [0] 3
    (checkWith diamond 1 [[0]] [method 1 [4], method 2 [5], method 3 [0]])
  expectError "pair repairs leave triple ambiguity" "E_DISPATCH_AMBIGUOUS"
    (checkWith diamond 3 [[0, 0, 0]] (broadTriple ++ pairRepairs))
  let repaired := broadTriple ++ pairRepairs ++ [method 30 [4, 4, 4]]
  expectWinner "triple repair" [0, 0, 0] 30 (checkWith diamond 3 [[0, 0, 0]] repaired)
  expectWinner "permuted triple repair" [0, 0, 0] 30
    (checkWith diamond 3 [[0, 0, 0]] repaired.reverse)
  let invalidHierarchy := { diamond with subtype := fun a b => a == b || a == 0 || b == 0 }
  expectError "nonpartial hierarchy" "E_DISPATCH_HIERARCHY"
    (checkWith invalidHierarchy 1 [] [])
  let invalidFacts := { diamond with facts := fun _ => [.hasOrder] }
  expectError "unsupported capability evidence" "E_DISPATCH_HIERARCHY"
    (checkWith invalidFacts 1 [] [])
  match check 1 [[0]] [method 1 [5], method 2 [0]] with
  | .error error => throw (IO.userError error.message)
  | .ok checked =>
      unless checked.applicablePairs.contains (1, [3]) do
        throw (IO.userError "ground body pairs must include keys outside D")
      unless checked.applicablePairs.contains (1, [0]) do
        throw (IO.userError "ground body pairs must include applicable losing methods")
  match check 6 [] [] with
  | .error error => throw (IO.userError s!"4096-key boundary: {error.message}")
  | .ok checked => unless checked.keys.length == 4096 do
      throw (IO.userError "4096-key boundary: incomplete universe")
  IO.println "dispatch: 28 finite-engine regression checks passed"

end VastitasKernel.Dispatch.Regression
