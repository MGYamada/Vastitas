import VastitasStorageTest.NumericalFixture

namespace VastitasKernel.Storage.TreeRegression
open NumericalFixture Numerical TensorTree

private def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"contraction trees: {label}")

private def setup (scalar : Scalar) (implementation : String) : List Functions.Statement := [
  .numerical (.space 0 (id implementation) 2), .numerical (.basis 10 0),
  .numerical (.space 1 (id implementation) 2), .numerical (.basis 11 1),
  .numerical (.space 2 (id implementation) 2), .numerical (.basis 12 2),
  .numerical (.space 3 (id implementation) 2), .numerical (.basis 13 3),
  .numerical (.space 4 (id implementation) 2), .numerical (.basis 14 4),
  .numerical (.dualSpace 20 1), .numerical (.derivedBasis 21 11 20),
  .numerical (.dualSpace 22 2), .numerical (.derivedBasis 23 12 22),
  .numerical (.dualSpace 24 3), .numerical (.derivedBasis 25 13 24),
  .numerical (.dualSpace 26 4), .numerical (.derivedBasis 27 14 26),
  .action (.allocate 40 scalar 8), .action (.allocate 41 scalar 4), .action (.allocate 42 scalar 4),
  .action (.allocate 43 scalar 8), .action (.allocate 44 scalar 8), .action (.allocate 45 scalar 8),
  .action (.borrow 50 (.owner 40) (layout 2 4) .write), .action (.fill 50 (payload scalar)), .action (.release 50),
  .action (.borrow 51 (.owner 41) (layout 2 2) .write), .action (.fill 51 (payload scalar)), .action (.release 51),
  .action (.borrow 52 (.owner 42) (layout 2 2) .write), .action (.fill 52 (payload scalar)), .action (.release 52),
  .action (.borrow 53 (.owner 40) (layout 2 4) .read),
  .action (.borrow 54 (.owner 41) (layout 2 2) .read),
  .action (.borrow 55 (.owner 42) (layout 2 2) .read),
  .action (.borrow 56 (.owner 45) (layout 4 2) .write),
  .tensor (.view 60 53 [10, 21, 23] Tensor.unpacked),
  .tensor (.view 61 54 [11, 25] Tensor.matrix), .tensor (.view 62 55 [12, 27] Tensor.matrix),
  .tensor (.view 63 56 [10, 25, 27] Tensor.boundary)]

private def graph : Graph := ⟨[⟨"t",60⟩,⟨"a",61⟩,⟨"b",62⟩],
  [⟨"v",⟨"t",1⟩,⟨"a",0⟩⟩,⟨"w",⟨"t",2⟩,⟨"b",0⟩⟩], [⟨"t",0⟩,⟨"a",1⟩,⟨"b",1⟩]⟩
private def plan : List (PlanStep Symbol Action) := [
  .action (.borrow 70 (.owner 43) (layout 4 2) .write), .view 71 70 [10,21,23] Tensor.packed,
  .regroup "t" 71, .action (.release 70),
  .action (.borrow 72 (.owner 43) (layout 4 2) .read), .view 73 72 [10,21,23] Tensor.packed,
  .rebind "t" 73, .action (.borrow 74 (.owner 44) (layout 4 2) .write),
  .view 75 74 [10,23,25] Tensor.boundary, .join "ta" "v" "t" "a" 75,
  .action (.release 74), .action (.release 72),
  .action (.borrow 76 (.owner 44) (layout 4 2) .read), .view 77 76 [10,23,25] Tensor.boundary,
  .rebind "ta" 77, .action (.borrow 78 (.owner 43) (layout 4 2) .write),
  .view 79 78 [10,23,25] Tensor.packed, .regroup "ta" 79,
  .action (.release 78), .action (.release 76),
  .action (.borrow 80 (.owner 43) (layout 4 2) .read), .view 81 80 [10,23,25] Tensor.packed,
  .rebind "ta" 81, .join "done" "w" "ta" "b" 63, .action (.release 80)]
private def tree : Functions.Statement := .tree graph 63 .nativeFast plan
private def cleanup : List Functions.Statement := [
  .action (.release 56), .action (.release 55), .action (.release 54), .action (.release 53),
  .action (.drop 45), .action (.drop 44), .action (.drop 43),
  .action (.drop 42), .action (.drop 41), .action (.drop 40)]

#eval show IO Unit from do
  let .ok declarations := Indexed.Source.checkDeclarations source | throw (IO.userError "tree declaration fixture")
  let env := declarations.resolved.declarations.indexed
  for (scalar, implementation) in [(Scalar.f64,"Real"),(.complexF64,"Complex")] do
    for condition in [false,true] do
      let body := setup scalar implementation ++ [tree, .branch condition [tree] [tree], tree] ++ cleanup
      let .ok result := Functions.check (program body) env | throw (IO.userError "valid complete contraction trees rejected")
      ensure "all prefix/branch/suffix receipts retained once, no probes" (result.context.trees.size == 4)
      ensure "all tree origins preserved" (result.context.trees.all fun r => r.environment == env)
      for receipt in result.context.trees do
        ensure "all declared occurrences survive into result" (receipt.checked.result.members.length == 3)
        ensure "explicit event order covered exactly" (receipt.checked.receipts.length == plan.length)
        ensure "all selected contraction witnesses retained" (receipt.checked.receipts.countP (fun r => match r.operation with
          | .contraction .. => true | _ => false) == 2)
        ensure "both actual regroup witnesses retained" (receipt.checked.receipts.countP (fun r => match r.operation with
          | .regroup .. => true | _ => false) == 2)
      let .ok native := Native.compile result.statements | throw (IO.userError "tree native lowering")
      let forged := native.instructions.map fun instruction => match instruction with
        | .regroup3 source input target output dimensions grouping regrouping =>
          .regroup3 source input target output dimensions grouping {regrouping with order := [2,0,1]}
        | other => other
      ensure "regroup code forgery rejected by exact regeneration" (!(Native.generate {native with instructions := forged}).isOk)
      ensure "only caller allocation/copy costs" (result.statements.countP (fun s => match s with
        | .action (.allocate ..) => true | _ => false) == 6)
  -- A disconnected cycle beside a boundary component passes n-1 edges and
  -- exact port coverage. Start accepts those local properties; no complete
  -- contraction plan can finish it by silently forgetting the third node.
  let initial := setup .f64 "Real" ++ [.tensor (.view 65 54 [11,21] Tensor.matrix)]
  let .ok (_, context) := (Functions.expand 4096 [] [] [] initial).run {environment := env}
    | throw (IO.userError "tree cycle fixture")
  let some view := context.tensors.head? | throw (IO.userError "cycle actual view")
  let cycle : Graph := ⟨[⟨"x",view.1⟩,⟨"y",view.1⟩,⟨"z",view.1⟩],
    [⟨"yz",⟨"y",1⟩,⟨"z",0⟩⟩,⟨"zy",⟨"z",1⟩,⟨"y",0⟩⟩], [⟨"x",0⟩,⟨"x",1⟩]⟩
  let .ok cycleStart := TensorTree.start env context.numerical context.resources context.tensors cycle
    | throw (IO.userError "disconnected cycle must pass local port/count audit")
  ensure "cycle cannot disappear into unrelated boundary" (!(TensorTree.check env context.numerical context.resources
    context.tensors cycle view.1 []).isOk)
  ensure "a cycle edge cannot trace one active component" (!(TensorTree.executeEvent env context.numerical cycle
    cycleStart.runtime (.join "result" "yz" "y" "y" view.1)).isOk)
  IO.println "Contraction trees: exact producers, finite connected coverage, both branch receipts, operation witnesses and forged native plans passed"

end VastitasKernel.Storage.TreeRegression
