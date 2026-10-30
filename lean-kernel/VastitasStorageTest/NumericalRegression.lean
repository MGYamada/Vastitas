import VastitasStorageTest.NumericalFixture

namespace VastitasKernel.Storage.NumericalRegression
open Indexed

open NumericalFixture

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"numerical value regression failed: {label}")

#eval show IO Unit from do
  let .ok declarations := Indexed.Source.checkDeclarations source
    | throw (IO.userError "numerical declarations rejected by common checker")
  let env := declarations.resolved.declarations.indexed
  for (scalar, implementation) in [(Scalar.f64, "Real"), (.complexF64, "Complex")] do
    let body := setup scalar implementation ++ [multiply] ++ cleanup
    let .ok checked := Functions.check (program body) env
      | throw (IO.userError "valid typed product rejected")
    check "exactly one actual product; probes do not leak" (checked.context.products.size == 1)
    check "local mathematical values cannot escape the activation" checked.context.numerical.isEmpty
    let some receipt := checked.context.products[0]? | throw (IO.userError "lost product receipt")
    let product := receipt.checked.product
    check "same extent is not nominal equality" (product.right.source.space.dimension == product.left.target.space.dimension &&
      product.right.source.space.object != product.left.target.space.object)
    check "no implicit conjugation" (!(product.request .overwrite .nativeFast).conjugateLeft &&
      !(product.request .overwrite .nativeFast).conjugateRight)
    check "complex dimension is retained" (product.left.source.space.realDimension ==
      (if scalar == .f64 then 3 else 6))
    let .ok native := Native.compile checked.statements | throw (IO.userError "typed native lowering rejected")
    check "typed product reaches the existing native GEMM lowering" native.needsNumerical
    -- The actual source program is replayed; stale certificates are not reused.
    let twice : Functions.Program := ⟨[⟨0, [], [], [.call 1 [] [], .call 1 [] []]⟩,
      ⟨1, [], [], body⟩], 0⟩
    let .ok repeated := Functions.check twice env | throw (IO.userError "repeated activation rejected")
    let some first := repeated.context.products[0]? | throw (IO.userError "missing first activation")
    let some second := repeated.context.products[1]? | throw (IO.userError "missing second activation")
    check "fresh objects per actual call" (repeated.context.products.size == 2 &&
      first.checked.product.left.source.space.object != second.checked.product.left.source.space.object)
    let forged := receipt.values.map fun (name, value) => (name, match value with
      | .map view => .map {view with source := {view.source with brand := 99999}}
      | other => other)
    check "forged basis provenance rejected" (!(Numerical.checkProduct env receipt.resources forged
      receipt.left receipt.right receipt.output receipt.mode receipt.policy).isOk)
    let changed := {receipt.resources with loans := receipt.resources.loans.map fun loan =>
      if loan.name == product.left.loan.name then {loan with layout := {loan.layout with transposed := true}} else loan}
    check "forged live layout rejected" (!(Numerical.checkProduct env changed receipt.values
      receipt.left receipt.right receipt.output receipt.mode receipt.policy).isOk)
  let real := setup .f64 "Real"
  let square := setup .f64 "Real" 2
  let cases : List (String × List Functions.Statement) := [
    ("same extent, wrong output object", real.map (fun statement => match statement with
      | .numerical (.map 32 loan _ target) => .numerical (.map 32 loan target target)
      | other => other) ++ [multiply] ++ cleanup),
    ("same space, distinct basis", real ++ [.numerical (.basis 40 1),
      .numerical (.map 41 23 3 40), .numerical (.gemm 30 41 32 .overwrite .nativeFast)] ++ cleanup),
    ("wrong middle object with same dimension", square ++ [.numerical (.map 40 23 3 5),
      .numerical (.gemm 30 40 32 .overwrite .nativeFast)] ++ cleanup),
    ("real buffer cannot implement complex coefficients", setup .f64 "Complex" ++ [multiply] ++ cleanup),
    ("affine descriptor cannot construct linear space", setup .f64 "Affine" ++ [multiply] ++ cleanup),
    ("distinct nominal bases", real.map (fun statement => match statement with
      | .numerical (.space 2 _ dim) => .numerical (.space 2 (id "Other") dim)
      | other => other) ++ [multiply] ++ cleanup),
    ("stale square view after transpose", square ++ [.action (.transpose 22), multiply] ++ cleanup),
    ("returned loan view", real ++ [.action (.release 22), multiply] ++ cleanup),
    ("suspended parent view", real ++ [.action (.borrow 40 (.loan 22) (layout 2 3) .read), multiply] ++ cleanup),
    ("accumulate must read initialized output", real ++ [.numerical (.gemm 30 31 32 .accumulate .nativeFast)] ++ cleanup),
    ("false branch still checked", real ++ [.branch false [.numerical (.gemm 31 30 32 .overwrite .nativeFast)] []] ++ cleanup),
    ("branch-local basis cannot escape", real ++ [.branch true [.numerical (.basis 40 0)] [],
      .numerical (.map 41 23 40 4)] ++ cleanup),
    ("resource handle is not a map", real ++ [.numerical (.gemm 22 31 32 .overwrite .nativeFast)] ++ cleanup),
    ("space cannot shadow resource name", real ++ [.numerical (.space 10 (id "Real") 2)] ++ cleanup)]
  for (label, body) in cases do check label (!(Functions.check (program body) env).isOk)
  let unused : Functions.Program := ⟨[⟨0, [], [], []⟩,
    ⟨1, [], [], [.numerical (.space 0 (id "Affine") 2)]⟩], 0⟩
  check "unused numerical body checked" (!(Functions.check unused env).isOk)
  let escape : Functions.Program := ⟨[⟨0, [], [], [.call 1 [] [10]]⟩,
    ⟨1, [], [(0, ⟨.f64, 2, []⟩)], [.numerical (.space 0 (id "Real") 2)]⟩], 0⟩
  check "numerical object cannot escape as owner" (!(Functions.check escape env).isOk)
  let invalidEnv := env ++ [⟨id "Conflict", .implementation (id "R") (.scalarBase .scheme .complex) []⟩]
  check "unused conflicting declaration rejected" (!(Functions.check (program (real ++ [multiply] ++ cleanup)) invalidEnv).isOk)
  IO.println "numerical values: real/complex typed products, exact lowering, nominal objects/bases, activation freshness and stale/forged view rejection passed"

end VastitasKernel.Storage.NumericalRegression
