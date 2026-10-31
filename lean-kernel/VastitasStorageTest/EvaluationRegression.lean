import VastitasStorageTest.NumericalFixture

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

end VastitasKernel.Storage.EvaluationRegression
