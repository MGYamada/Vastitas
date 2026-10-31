import VastitasStorageTest.NumericalFixture

namespace VastitasKernel.Storage.TransformRegression
open NumericalFixture Numerical

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"typed transform regression: {label}")

private def declarations : List Functions.Statement := [
  .numerical (.dualSpace 40 0), .numerical (.dualSpace 41 1), .numerical (.dualSpace 42 2),
  .numerical (.derivedBasis 43 3 40), .numerical (.derivedBasis 44 4 41), .numerical (.derivedBasis 45 5 42),
  .numerical (.involution 46 1),
  .numerical (.conjugateSpace 47 0 46), .numerical (.conjugateSpace 48 1 46), .numerical (.conjugateSpace 49 2 46),
  .numerical (.derivedBasis 50 3 47), .numerical (.derivedBasis 51 4 48), .numerical (.derivedBasis 52 5 49),
  .numerical (.metric 53 3 46 .identity), .numerical (.metric 54 4 46 .identity), .numerical (.metric 55 5 46 .identity)]

private def transforms (kind : Nat) : List Functions.Statement := match kind with
  | 0 => [.numerical (.transform 60 30 (.dual 45 44)), .numerical (.transform 61 31 (.dual 44 43)),
      .numerical (.map 62 24 45 43), .numerical (.gemm 61 60 62 .overwrite .nativeFast)]
  | 1 => [.numerical (.transform 60 30 (.conjugate 51 52 46)), .numerical (.transform 61 31 (.conjugate 50 51 46)),
      .numerical (.map 62 24 50 52), .numerical (.gemm 60 61 62 .overwrite .nativeFast)]
  | _ => [.numerical (.transform 60 30 (.adjoint 54 55)), .numerical (.transform 61 31 (.adjoint 53 54)),
      .numerical (.map 62 24 5 3), .numerical (.gemm 61 60 62 .overwrite .nativeFast)]

private def release : List Functions.Statement := [.action (.release 60), .action (.release 61)]

#eval show IO Unit from do
  let .ok accepted := Indexed.Source.checkDeclarations source
    | throw (IO.userError "transform profile declarations failed")
  let env := accepted.resolved.declarations.indexed
  for (scalar, implementation) in [(Scalar.f64, "Real"), (.complexF64, "Complex")] do
    for kind in [0, 1, 2] do
      let body := setup scalar implementation ++ declarations ++ transforms kind ++ release ++ cleanup
      let .ok checked := Functions.check (program body) env
        | throw (IO.userError s!"valid transform program rejected: {kind}")
      check "actual transform receipts exclude probes" (checked.context.transforms.size == 2)
      check "three original buffers, no packing/copy" (checked.statements.countP (fun s => match s with
        | .action (.allocate ..) => true | _ => false) == 3 && checked.statements.all (fun s => match s with
        | .action (.copy ..) => false | _ => true))
      let some product := checked.context.products[0]? | throw (IO.userError "missing transformed product")
      check "flags survive actual product" (product.checked.product.left.conjugate == (kind != 0) &&
        product.checked.product.right.conjugate == (kind != 0) &&
        product.checked.product.left.loan.layout.transposed == (kind != 1))
      for receipt in checked.context.transforms do
        check "original allocation retained" (receipt.checked.original.loan.allocation == receipt.checked.result.loan.allocation)
        check "parent suspended" (receipt.after.suspended receipt.checked.original.loan.name)
        check "parent cannot be released first" (!(checkAction receipt.after (.release receipt.checked.original.loan.name)).isOk)
        check "transformed read loan cannot acquire write authority"
          (!(checkAction receipt.after (.borrow 2000 (.loan receipt.checked.result.loan.name)
            receipt.checked.result.loan.layout .write)).isOk)
        check "parent interpretation cannot be reused while child lives"
          (!(checkTransform env receipt.after receipt.checked.output 999  receipt.parent 1000 receipt.operation).isOk)
        let forged := receipt.checked.output.map fun (name, value) => (name,
          if name == receipt.name then .map {receipt.checked.result with conjugate := !receipt.checked.result.conjugate} else value)
        check "forged conjugation rejected" (!decide (Valid env forged))
        let cyclic := receipt.checked.output.map fun (name, value) => (name,
          if name == receipt.name then .map {receipt.checked.result with origin := .reborrow name} else value)
        check "cyclic transform provenance rejected" (!decide (Valid env cyclic))
        let changed := receipt.checked.output.map fun (name, value) => (name,
          if name == receipt.name then .map {receipt.checked.result with loan :=
            {receipt.checked.result.loan with allocation := 999}} else value)
        check "forged allocation rejected" (!decide (Valid env changed))
      let forgedMetric := product.values.map fun (name, value) => (name, match value with
        | .metric form => .metric {form with gram := .scaledIdentity 2}
        | other => other)
      if kind == 2 then
        check "nonorthonormal metric cannot reuse an adjoint certificate" (!decide (Valid env forgedMetric))
      let .ok native := Native.compile checked.statements | throw (IO.userError "transform native lowering failed")
      let forgedCode := native.instructions.map fun instruction => match instruction with
        | .gemm l lv lc r rv rc o ov mode policy alpha beta => .gemm l lv (!lc) r rv rc o ov mode policy alpha beta
        | other => other
      check "forged native transform flag rejected" (!(Native.generate {native with instructions := forgedCode}).isOk)
  let preparation := setup .complexF64 "Complex" ++ declarations
  let invalid : List (String × List Functions.Statement) := [
    ("uninitialized write-only map cannot be transformed", preparation ++ [.numerical (.transform 60 32 (.dual 45 43))]),
    ("ordinary basis is not a dual basis", preparation ++ [.numerical (.transform 60 30 (.dual 5 4))]),
    ("conjugate is not dual", preparation ++ [.numerical (.transform 60 30 (.dual 52 51))]),
    ("wrong conjugate involution", preparation ++ [.numerical (.involution 70 1),
      .numerical (.transform 60 30 (.conjugate 51 52 70))]),
    ("wrong derived parent basis", setup .complexF64 "Complex" ++ declarations ++
      [.numerical (.derivedBasis 70 5 41)]),
    ("missing metric", preparation ++ [.numerical (.transform 60 30 (.adjoint 54 999))]),
    ("metric for wrong nominal object", preparation ++ [.numerical (.transform 60 30 (.adjoint 54 53))]),
    ("non-orthonormal direct adjoint", preparation ++ [.numerical (.metric 70 4 46 (.scaledIdentity 2)),
      .numerical (.transform 60 30 (.adjoint 70 55))]),
    ("degenerate form", preparation ++ [.numerical (.metric 70 4 46 (.scaledIdentity 0))]),
    ("wrong diagonal dimension", preparation ++ [.numerical (.metric 70 4 46 (.diagonal [1, 1]))]),
    ("zero diagonal entry", preparation ++ [.numerical (.metric 70 4 46 (.diagonal [1, 0, 1]))]),
    ("metric involution from another scalar", preparation ++ [.numerical (.space 70 (id "Real") 3),
      .numerical (.involution 71 70), .numerical (.metric 72 4 71 .identity)])]
  for (label, body) in invalid do
    -- Run the prefix itself: a missing final cleanup cannot explain rejection.
    check label (!((Functions.expand 4096 [] [] [] body).run {environment := env}).isOk)
  check "nonpositive nondegenerate metric is permitted as declared data"
    (((Functions.expand 4096 [] [] [] (preparation ++ [.numerical (.metric 70 4 46 (.diagonal [-1, 2, -3]))])).run
      {environment := env}).isOk)
  let nested := preparation ++ [.numerical (.transform 60 30 (.dual 45 44)),
    .numerical (.dualSpace 70 41), .numerical (.dualSpace 71 42),
    .numerical (.derivedBasis 72 44 70), .numerical (.derivedBasis 73 45 71),
    .numerical (.transform 61 60 (.dual 72 73))]
  check "nested transforms release inside out" ((Functions.check
    (program (nested ++ [.action (.release 61), .action (.release 60),
      .action (.fill 24 (.complexF64 0 0))] ++ cleanup)) env).isOk)
  check "nested outer release rejected" (!((Functions.expand 4096 [] [] []
    (nested ++ [.action (.release 60)])).run {environment := env}).isOk)
  let branchBody := transforms 1 ++ release
  for condition in [false, true] do
    let .ok branched := Functions.check
        (program (preparation ++ [.branch condition branchBody branchBody] ++ cleanup)) env
      | throw (IO.userError "balanced transformed branches rejected")
    check "both branches retain actual transform receipts" (branched.context.transforms.size == 4)
    check "unreturned transform in either branch is rejected" (!((Functions.expand 4096 [] [] []
      (preparation ++ [.branch condition branchBody (transforms 1 ++ [.action (.release 60)])])).run
        {environment := env}).isOk)
  IO.println "Typed transforms: dual/conjugate/adjoint provenance, metrics, exact flags, nested loans and forged IR passed"

end VastitasKernel.Storage.TransformRegression
