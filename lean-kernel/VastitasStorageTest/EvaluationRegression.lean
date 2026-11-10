import VastitasStorageTest.NumericalFixture
import VastitasKernel.NumericalCoverage

namespace VastitasKernel.Storage.EvaluationRegression
open NumericalFixture Numerical

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"vector evaluation regression: {label}")

private def prepare (scalar : Scalar) (implementation : String) (dimension : Nat) (transposed : Bool) : List Functions.Statement :=
  let layout : Layout := if transposed then ⟨0, 1, dimension, 2, true⟩ else ⟨0, dimension, 1, max 1 dimension, false⟩
  [.numerical (.space 0 (id implementation) dimension), .numerical (.basis 1 0),
    .numerical (.dualSpace 2 0), .numerical (.derivedBasis 3 1 2), .numerical (.involution 4 0),
    .numerical (.conjugateSpace 5 0 4), .numerical (.derivedBasis 6 1 5), .numerical (.metric 7 1 4 .identity),
    .action (.allocate 10 scalar (2 * dimension)), .action (.allocate 11 scalar 1),
    .action (.borrow 20 (.owner 10) layout .write), .action (.fill 20 (payload scalar)), .action (.release 20),
    .action (.borrow 21 (.owner 10) layout .read), .action (.borrow 22 (.owner 10) layout .read),
    .action (.borrow 23 (.owner 11) (NumericalFixture.layout 1 1) .write),
    .numerical (.vector 30 21 1), .numerical (.vector 31 21 3), .numerical (.vector 33 22 1)]

private def algebraic : Functions.Statement := .numerical (.evaluate 31 30 23 .dual .overwrite .nativeFast)
private def hermitian : List Functions.Statement := [.numerical (.conjugateVector 40 30 6 4),
  .numerical (.evaluate 40 33 23 (.hermitian 7) .overwrite .nativeFast), .action (.release 40)]
private def finish : List Functions.Statement := [.action (.release 23),
  .action (.borrow 24 (.owner 11) (NumericalFixture.layout 1 1) .read), .action (.release 24),
  .action (.release 21), .action (.release 22), .action (.drop 10), .action (.drop 11)]

#eval show IO Unit from do
  let .ok declarations := Indexed.Source.checkDeclarations source | throw (IO.userError "invalid declaration fixture")
  let env := declarations.resolved.declarations.indexed
  for (scalar, implementation) in [(Scalar.f64, "Real"), (.complexF64, "Complex")] do
    for dimension in [0, 1, 3] do
      for transposed in [false, true] do
        let body := prepare scalar implementation dimension transposed ++ [algebraic] ++ hermitian ++ finish
        let .ok accepted := Functions.check (program body) env | throw (IO.userError "valid vector evaluation rejected")
        check "actual evaluation receipts exclude probes" (accepted.context.evaluations.size == 2)
        let some first := accepted.context.evaluations[0]? | throw (IO.userError "missing evaluation")
        let tampered := accepted.context.code.set! first.location.start (.action (.release first.leftChild))
        check "evaluation coverage checks child borrows as well as GEMM"
          (NumericalCoverage.audit (program body).functions 0 accepted.context &&
            !NumericalCoverage.audit (program body).functions 0 {accepted.context with code := tampered})
        check "actual conjugation receipt excludes probes" (accepted.context.vectorConjugates.size == 1)
        check "two allocations, no copy or packing" (accepted.statements.countP (fun s => match s with
          | .action (.allocate ..) => true | _ => false) == 2 && accepted.statements.all (fun s => match s with
          | .action (.copy ..) => false | _ => true))
        for receipt in accepted.context.evaluations do
          let op := evaluationRequest receipt.checked.left receipt.checked.right receipt.leftChild receipt.rightChild
            receipt.output receipt.mode receipt.policy receipt.alpha receipt.beta
          check "scalar result initialized" (scalarOutputReady receipt.after receipt.output scalar)
          check "input loan snapshots restored" (decide (receipt.checked.left.Live receipt.after) &&
            decide (receipt.checked.right.Live receipt.after))
          check "evaluation adds no conjugation" (op.conjugateLeft == receipt.checked.left.conjugate &&
            op.conjugateRight == receipt.checked.right.conjugate)
          let forged := receipt.values.map fun (name, value) => (name, match value with
            | .vector view => if name == receipt.left then .vector {view with conjugate := !view.conjugate} else value
            | _ => value)
          check "forged interpretation rejected" (!(checkEvaluation env receipt.resources forged receipt.left receipt.right
            receipt.output receipt.leftChild receipt.rightChild receipt.operation receipt.mode receipt.policy).isOk)
          check "output/input alias rejected" (!(checkEvaluation env receipt.resources receipt.values receipt.left receipt.right
            receipt.checked.right.loan.name receipt.leftChild receipt.rightChild receipt.operation receipt.mode receipt.policy).isOk)
        let .ok native := Native.compile accepted.statements | throw (IO.userError "vector schedule lowering failed")
        let wrong := native.instructions.map fun instruction => match instruction with
          | .gemm l lv lc r rv rc o ov mode policy alpha beta => .gemm l lv (!lc) r rv rc o ov mode policy alpha beta
          | other => other
        check "forged emitted conjugation rejected" (!(Native.generate {native with instructions := wrong}).isOk)
  let preparation := prepare .complexF64 "Complex" 3 false
  let invalid : List (String × List Functions.Statement) := [
    ("two ordinary vectors cannot dual-evaluate", [.numerical (.evaluate 30 33 23 .dual .overwrite .nativeFast)]),
    ("conjugate space is not dual", [.numerical (.vector 39 21 6),
      .numerical (.evaluate 39 33 23 .dual .overwrite .nativeFast)]),
    ("Hermitian pairing cannot insert conjugation", [.numerical (.evaluate 30 33 23 (.hermitian 7) .overwrite .nativeFast)]),
    ("nonidentity Gram requires explicit realization", [.numerical (.metric 39 1 4 (.scaledIdentity 2)),
      .numerical (.conjugateVector 40 30 6 4), .numerical (.evaluate 40 33 23 (.hermitian 39) .overwrite .nativeFast)]),
    ("same-sized fresh dual is not related", [.numerical (.space 39 (id "Complex") 3),
      .numerical (.basis 40 39), .numerical (.vector 41 21 40), .numerical (.evaluate 41 33 23 .dual .overwrite .nativeFast)]),
    ("arbitrary dual-space basis is not corresponding", [.numerical (.basis 39 2), .numerical (.vector 40 21 39),
      .numerical (.evaluate 40 33 23 .dual .overwrite .nativeFast)]),
    ("wrong conjugate basis", [.numerical (.conjugateVector 40 30 3 4)]),
    ("wrong selected involution", [.numerical (.involution 39 0), .numerical (.conjugateVector 40 30 6 39)]),
    ("parent cannot be read while conjugate child lives", [.numerical (.conjugateVector 40 30 6 4),
      .numerical (.evaluate 40 30 23 (.hermitian 7) .overwrite .nativeFast)]),
    ("parent cannot be released before conjugate child", [.numerical (.conjugateVector 40 30 6 4), .action (.release 30)]),
    ("accumulate needs initialized read/write output", [.numerical (.evaluate 31 30 23 .dual .accumulate .nativeFast)]),
    ("old view cannot survive physical transpose", [.action (.transpose 21), algebraic])]
  for (label, tail) in invalid do
    check label (!((Functions.expand 4096 [] [] [] (preparation ++ tail)).run {environment := env}).isOk)
  let noInitialization := preparation.filter fun statement => match statement with | .action (.fill ..) => false | _ => true
  check "uninitialized vector read rejected" (!((Functions.expand 4096 [] [] [] (noInitialization ++ [algebraic])).run
    {environment := env}).isOk)
  for condition in [false, true] do
    let branch := [algebraic] ++ hermitian
    let .ok result := Functions.check (program (preparation ++ [.branch condition branch branch] ++ finish)) env
      | throw (IO.userError "balanced evaluation branches rejected")
    check "both branch evaluation receipts retained" (result.context.evaluations.size == 4 && result.context.vectorConjugates.size == 2)
    check "branch cannot leave conjugate loan outstanding" (!((Functions.expand 4096 [] [] []
      (preparation ++ [.branch condition branch [.numerical (.conjugateVector 40 30 6 4)]])).run {environment := env}).isOk)
  IO.println "Vector evaluation: dual/Hermitian roles, exact flags, scalar initialization, actual loans, branches and forged IR passed"

/-! `fill`, `store`, `expect` and `copy` that name a vector act on its loan. -/

/-- One body, with every cell statement naming either the vectors or their loans. -/
private def cells (scalar : Scalar) (implementation : String) (dimension : Nat) (transposed viaVector : Bool) :
    List Functions.Statement :=
  let layout : Layout := if transposed then ⟨0, 1, dimension, 2, true⟩ else ⟨0, dimension, 1, max 1 dimension, false⟩
  let name (vector loan : Symbol) := if viaVector then vector else loan
  let value := payload scalar
  [.numerical (.space 0 (id implementation) dimension), .numerical (.basis 1 0),
    .action (.allocate 10 scalar (2 * dimension)), .action (.allocate 11 scalar (2 * dimension)),
    .action (.borrow 20 (.owner 10) layout .write), .numerical (.vector 30 20 1),
    .action (.fill (name 30 20) value)] ++
  (if dimension == 0 then [] else [.action (.store (name 30 20) (dimension - 1) 0 value)]) ++
  [.action (.release 20),
    .action (.borrow 21 (.owner 10) layout .read), .numerical (.vector 31 21 1),
    .action (.borrow 22 (.owner 11) layout .write), .numerical (.vector 32 22 1)] ++
  (if dimension == 0 then [] else [.action (.expect (name 31 21) (dimension - 1) 0 value)]) ++
  [.action (.copy (name 31 21) (name 32 22)),
    .action (.release 22), .action (.release 21), .action (.drop 10), .action (.drop 11)]

/-- A caller lends uninitialized cells as a vector; only the callee writes them. -/
private def producer (scalar : Scalar) (implementation : String) (dimension : Nat) (access : Access)
    (initializes : Bool) (body : List Functions.Statement) : Functions.Program :=
  let layout := NumericalFixture.layout dimension 1
  ⟨[⟨0, [], [], [.numerical (.space 0 (id implementation) dimension), .numerical (.basis 1 0),
      .action (.allocate 10 scalar dimension), .action (.borrow 20 (.owner 10) layout .write),
      .numerical (.vector 30 20 1), .call 1 [0, 1, 30] [], .action (.release 20),
      .action (.borrow 21 (.owner 10) layout .read), .action (.release 21), .action (.drop 10)], none⟩,
    ⟨1, [.space 0 (id implementation) dimension, .basis 1 0, .vector 2 1 access initializes], [], body, none⟩], 0⟩

private def checkCode (program : Functions.Program) (env : Indexed.Environment) : Option String :=
  match Functions.check program env with | .ok _ => none | .error error => some error.code

private def expandCode (statements : List Functions.Statement) (env : Indexed.Environment) : Option String :=
  match (Functions.expand 4096 [] [] [] statements).run {environment := env} with
  | .ok _ => none
  | .error error => some error.code

#eval show IO Unit from do
  let .ok declarations := Indexed.Source.checkDeclarations source | throw (IO.userError "invalid declaration fixture")
  let env := declarations.resolved.declarations.indexed
  for (scalar, implementation) in [(Scalar.f64, "Real"), (.complexF64, "Complex")] do
    let value := payload scalar
    for dimension in [0, 1, 3] do
      for transposed in [false, true] do
        let .ok viaVector := Functions.check (program (cells scalar implementation dimension transposed true)) env
          | throw (IO.userError "cell statements through vectors rejected")
        let .ok viaLoan := Functions.check (program (cells scalar implementation dimension transposed false)) env
          | throw (IO.userError "cell statements through loans rejected")
        check "a vector operand emits the schedule of its loan"
          (decide (viaVector.statements = viaLoan.statements))
        check "a vector operand leaves the resource state of its loan"
          (viaVector.context.resources == viaLoan.context.resources)
        check "vector cell statements allocate and conjugate nothing" (viaVector.statements.countP (fun s => match s with
          | .action (.allocate ..) => true | _ => false) == 2 && viaVector.statements.all (fun s => match s with
          | .action (.gemm ..) | .action (.borrow _ (.loan _) ..) => false | _ => true))
      let stores := (List.range dimension).map fun row => Functions.Statement.action (.store 2 row 0 value)
      let .ok filled := Functions.check (producer scalar implementation dimension .write true [.action (.fill 2 value)]) env
        | throw (IO.userError "fill through an initializing vector parameter rejected")
      -- The callee writes through the child loan of its vector parameter.
      check "fill reaches the child loan of the parameter" (filled.statements.any fun statement => match statement with
        | .action (.fill loan _) => filled.statements.any (fun prior => match prior with
          | .action (.borrow child (.loan _) _ .write) => child == loan | _ => false)
        | _ => false)
      check "stores of every cell keep the promise"
        ((checkCode (producer scalar implementation dimension .write true stores) env).isNone)
      check "written cells are initialized for the caller without a promise"
        ((checkCode (producer scalar implementation dimension .write false [.action (.fill 2 value)]) env).isNone)
      check "an unwritten promise fails only where a cell exists"
        (checkCode (producer scalar implementation dimension .write true []) env ==
          if dimension == 0 then none else some "E_RESOURCE_INIT")
      check "a missing cell breaks the promise"
        (checkCode (producer scalar implementation dimension .write true (stores.drop 1)) env ==
          if dimension == 0 then none else some "E_RESOURCE_INIT")
      check "one arm cannot keep the promise"
        (checkCode (producer scalar implementation dimension .write true
          [.branch (.literal true) [.action (.fill 2 value)] []]) env ==
          if dimension == 0 then none else some "E_RESOURCE_INIT")
      check "both arms keep the promise"
        ((checkCode (producer scalar implementation dimension .write true
          [.branch (.literal true) [.action (.fill 2 value)] stores]) env).isNone)
      check "a write-only vector parameter cannot be read"
        (checkCode (producer scalar implementation dimension .write true
          [.action (.fill 2 value), .action (.copy 2 2)]) env == some "E_RESOURCE_ACCESS")
    -- A tampered schedule that writes through the suspended caller loan is refused.
    let .ok accepted := Functions.check (producer scalar implementation 3 .write true [.action (.fill 2 value)]) env
      | throw (IO.userError "vector producer rejected")
    let parent := accepted.statements.findSome? fun statement => match statement with
      | .action (.borrow _ (.loan parent) _ .write) => some parent | _ => none
    let some parent := parent | throw (IO.userError "missing parameter child loan")
    let forged := accepted.statements.map fun statement => match statement with
      | .action (.fill _ value) => Storage.Statement.action (.fill parent value) | other => other
    check "forged write through the suspended caller loan rejected"
      ((checkPlan accepted.statements).isOk && !(checkPlan forged).isOk)
  let value := payload .complexF64
  let preparation := prepare .complexF64 "Complex" 3 false
  let conjugated : Functions.Statement := .numerical (.conjugateVector 40 30 6 4)
  let rejected : List (String × List Functions.Statement × String) := [
    ("fill through a read vector", [.action (.fill 30 value)], "E_RESOURCE_ACCESS"),
    ("store through a read vector", [.action (.store 30 0 0 value)], "E_RESOURCE_ACCESS"),
    ("copy into a read vector", [.action (.copy 33 30)], "E_RESOURCE_ACCESS"),
    ("copy onto the same read vector still needs write access", [.action (.copy 30 30)], "E_RESOURCE_ACCESS"),
    ("fill through a conjugate vector", [conjugated, .action (.fill 40 value)], "E_RESOURCE_ACCESS"),
    ("store through a conjugate vector", [conjugated, .action (.store 40 0 0 value)], "E_RESOURCE_ACCESS"),
    ("copy into a conjugate vector", [conjugated, .action (.copy 33 40)], "E_RESOURCE_ACCESS"),
    ("stored cells are not read through a conjugate vector", [conjugated, .action (.expect 40 0 0 value)], "E_NUMERICAL_TYPE"),
    ("stored cells are not copied from a conjugate vector", [conjugated, .action (.copy 40 23)], "E_NUMERICAL_TYPE"),
    ("a suspended vector gives no access", [conjugated, .action (.expect 30 0 0 value)], "E_NUMERICAL_TYPE"),
    ("another vector of the suspended loan gives no access", [conjugated, .action (.expect 31 0 0 value)], "E_NUMERICAL_TYPE"),
    ("a vector keeps the layout of its statement", [.action (.transpose 21), .action (.expect 30 0 0 value)], "E_NUMERICAL_TYPE"),
    ("a vector ends with its loan", [.action (.release 21), .action (.expect 30 0 0 value)], "E_NUMERICAL_TYPE"),
    ("a cell outside the vector", [.action (.expect 30 3 0 value)], "E_RESOURCE_BOUNDS"),
    ("a vector has one column", [.action (.expect 30 0 1 value)], "E_RESOURCE_BOUNDS"),
    ("the payload has the element type of the vector", [.action (.expect 30 0 0 (payload .f64))], "E_RESOURCE_TYPE"),
    ("copy needs the shape of the vector", [.action (.copy 30 23)], "E_RESOURCE_TYPE"),
    ("transpose rejects a vector", [.action (.transpose 30)], "E_RESOURCE_LOAN"),
    ("drop rejects a vector", [.action (.drop 30)], "E_RESOURCE_MOVE"),
    ("move rejects a vector", [.action (.move 30 50)], "E_RESOURCE_MOVE"),
    ("borrow rejects a vector", [.action (.borrow 50 (.loan 30) (NumericalFixture.layout 1 1) .read)], "E_RESOURCE_LOAN"),
    ("a map is not a loan", [.numerical (.space 50 (id "Complex") 1), .numerical (.basis 51 50),
      .numerical (.map 52 23 51 51), .action (.fill 52 value)], "E_RESOURCE_LOAN"),
    ("a basis is not a loan", [.action (.fill 1 value)], "E_RESOURCE_LOAN")]
  for (label, tail, code) in rejected do
    check label (expandCode (preparation ++ tail) env == some code)
  let accepted : List (String × List Functions.Statement) := [
    ("expect reads the stored cell of a read vector", [.action (.expect 30 2 0 value)]),
    ("a covector presents the same stored cells", [.action (.expect 31 2 0 value)]),
    ("two conjugations read the stored cells", [.numerical (.conjugateSpace 50 5 4), .numerical (.derivedBasis 51 6 50),
      conjugated, .numerical (.conjugateVector 41 40 51 4), .action (.expect 41 0 0 value)])]
  for (label, tail) in accepted do
    check label ((expandCode (preparation ++ tail) env).isNone)
  IO.println "Vector cells: loan schedules, initialization promises, access, conjugation, suspension, stale views and forged schedules passed"

end VastitasKernel.Storage.EvaluationRegression
