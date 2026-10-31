import VastitasStorageTest.NumericalFixture

namespace VastitasKernel.Storage.TensorRegression
open NumericalFixture Numerical

private def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"tensor packing: {label}")

private def setup (scalar : Scalar) (implementation : String) : List Functions.Statement := [
  .numerical (.space 0 (id implementation) 2), .numerical (.basis 4 0),
  .numerical (.space 1 (id implementation) 3), .numerical (.basis 5 1),
  .numerical (.space 2 (id implementation) 2), .numerical (.basis 6 2),
  .numerical (.space 3 (id implementation) 2), .numerical (.basis 7 3),
  .numerical (.dualSpace 8 1), .numerical (.derivedBasis 9 5 8),
  .numerical (.dualSpace 10 3), .numerical (.derivedBasis 11 7 10),
  .action (.allocate 20 scalar 12), .action (.allocate 21 scalar 6),
  .action (.allocate 22 scalar 12), .action (.allocate 23 scalar 8),
  .action (.borrow 30 (.owner 20) (layout 2 6) .write),
  .action (.fill 30 (payload scalar)), .action (.release 30),
  .action (.borrow 31 (.owner 21) (layout 3 2) .write),
  .action (.fill 31 (payload scalar)), .action (.release 31),
  .action (.borrow 32 (.owner 20) (layout 2 6) .read),
  .action (.borrow 33 (.owner 21) (layout 3 2) .read),
  .tensor (.view 40 32 [4, 9, 6] Tensor.unpacked),
  .tensor (.view 41 33 [5, 11] Tensor.matrix),
  .action (.borrow 34 (.owner 22) (layout 4 3) .write),
  .tensor (.view 42 34 [4, 9, 6] Tensor.packed)]

private def pack : Functions.Statement := .tensor (.pack 40 42)
private def regroup : List Functions.Statement := [
  .action (.release 34), .action (.borrow 36 (.owner 22) (layout 4 3) .read),
  .tensor (.view 43 36 [4, 9, 6] Tensor.packed),
  .action (.borrow 35 (.owner 23) (layout 4 2) .write),
  .tensor (.view 44 35 [4, 6, 11] Tensor.boundary)]
private def contract : Functions.Statement := .tensor (.contract3 43 41 44 .nativeFast)
private def cleanup : List Functions.Statement := [
  .action (.release 35), .action (.borrow 37 (.owner 23) (layout 4 2) .read), .action (.release 37),
  .action (.release 36), .action (.release 33), .action (.release 32),
  .action (.drop 23), .action (.drop 22), .action (.drop 21), .action (.drop 20)]

#eval show IO Unit from do
  let .ok declarations := Indexed.Source.checkDeclarations source | throw (IO.userError "tensor declaration fixture rejected")
  let env := declarations.resolved.declarations.indexed
  for (scalar, implementation) in [(Scalar.f64, "Real"), (.complexF64, "Complex")] do
    let body := setup scalar implementation ++ [pack] ++ regroup ++ [contract] ++ cleanup
    let .ok result := Functions.check (program body) env | throw (IO.userError "valid tensor packing/contraction rejected")
    ensure "actual receipts exclude probes" (result.context.tensorViews.size == 5 &&
      result.context.tensorPacks.size == 1 && result.context.tensorContractions.size == 1)
    ensure "no hidden data allocations or copies" (result.statements.countP (fun s => match s with
      | .action (.allocate ..) => true | _ => false) == 4 && result.statements.countP (fun s => match s with
      | .action (.pack3 ..) => true | _ => false) == 1)
    let some receipt := result.context.tensorContractions[0]? | throw (IO.userError "missing contraction")
    let changed := receipt.values.map fun (name, view) =>
      (name, if name == receipt.output then {view with axes := view.axes.reverse} else view)
    ensure "equal-sized boundary axes cannot be exchanged" (!(Tensor.checkContraction env receipt.numerical
      receipt.resources changed receipt.left receipt.right receipt.output .nativeFast).isOk)
    let some packing := result.context.tensorPacks[0]? | throw (IO.userError "missing packing")
    ensure "packing returns its exact accepted state" ((checkAction packing.resources
      (Tensor.packAction packing.checked.input packing.checked.output)).toOption == some packing.after)
    let .ok native := Native.compile result.statements | throw (IO.userError "tensor native lowering rejected")
    let forged := native.instructions.map fun instruction => match instruction with
      | .pack3 source input target output i k j => .pack3 source input target output i j k
      | other => other
    ensure "forged packing dimensions fail native regeneration" (!(Native.generate {native with instructions := forged}).isOk)
    let forged := native.instructions.map fun instruction => match instruction with
      | .gemm a av ac b bv bc c cv mode policy alpha beta => .gemm a av (!ac) b bv bc c cv mode policy alpha beta
      | other => other
    ensure "tensor contraction cannot inject conjugation" (!(Native.generate {native with instructions := forged}).isOk)
  for condition in [false, true] do
    let extra : Functions.Statement := .tensor (.view 70 32 [4, 9, 6] Tensor.unpacked)
    let body := setup .complexF64 "Complex" ++ [pack, .branch condition [extra, pack] [extra, pack], pack] ++
      regroup ++ [contract, .branch condition [contract] [contract], contract] ++ cleanup
    let .ok result := Functions.check (program body) env | throw (IO.userError "valid tensor branches rejected")
    ensure "all branch/prefix/suffix receipt families retained once" (result.context.tensorViews.size == 7 &&
      result.context.tensorPacks.size == 4 && result.context.tensorContractions.size == 4)
    ensure "all tensor receipt declaration origins retained" (result.context.tensorViews.all (fun r => r.environment == env) &&
      result.context.tensorPacks.all (fun r => r.environment == env) && result.context.tensorContractions.all (fun r => r.environment == env))
  let before := setup .complexF64 "Complex"
  for (label, tail) in [
      ("uninitialized scratch cannot be read", regroup),
      ("released input cannot pack", [.action (.release 32), pack]),
      ("write-only packing destination cannot become readable", [pack, .action (.borrow 70 (.loan 34) (layout 4 3) .read)]),
      ("factor labels do not separate mutable input storage", [.action (.borrow 70 (.owner 20) (layout 2 6) .write)]),
      ("grouping duplicate axes rejected", [.tensor (.view 70 32 [4, 9, 6] ⟨[0, 0, 2], 1⟩)]),
      ("packing cannot change corresponding dual basis", [.tensor (.view 70 34 [4, 5, 6] Tensor.packed), .tensor (.pack 40 70)])] do
    ensure label (!((Functions.expand 4096 [] [] [] (before ++ tail)).run {environment := env}).isOk)
  IO.println "Tensor packing: actual axes/dual origins, explicit copies, initialized outputs, all branch receipts and forged native plans passed"

end VastitasKernel.Storage.TensorRegression
