import VastitasStorageTest.NumericalFixture

namespace VastitasKernel.Storage.NetworkRegression
open NumericalFixture Numerical TensorNetwork

private def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"finite network: {label}")

private def graph : Graph :=
  ⟨[⟨"a", 30⟩, ⟨"b", 31⟩], [⟨⟨"a", .input⟩, ⟨"b", .output⟩⟩],
    [⟨"b", .input⟩], [⟨"a", .output⟩]⟩

#eval show IO Unit from do
  let .ok declarations := Indexed.Source.checkDeclarations source
    | throw (IO.userError "network declarations failed")
  let env := declarations.resolved.declarations.indexed
  for (scalar, implementation) in [(Scalar.f64, "Real"), (.complexF64, "Complex")] do
    let body := setup scalar implementation ++ [.network graph 32 .nativeFast] ++ cleanup
    let .ok result := Functions.check (program body) env
      | throw (IO.userError "valid network rejected")
    ensure "one actual graph, excluding all-body probes" (result.context.networks.size == 1)
    let some receipt := result.context.networks[0]? | throw (IO.userError "missing graph")
    ensure "exact emitted product" (receipt.checked.request.conjugateLeft == false &&
      receipt.checked.request.conjugateRight == false && receipt.checked.request.mode == .overwrite)
    ensure "no allocation/copy from ports" (result.statements.countP (fun s => match s with
      | .action (.allocate ..) => true | _ => false) == 3 && result.statements.all (fun s => match s with
      | .action (.copy ..) => false | _ => true))
    let reversed := {receipt.graph with occurrences := receipt.graph.occurrences.reverse}
    let .ok reordered := TensorNetwork.check env receipt.resources receipt.values reversed receipt.output .nativeFast
      | throw (IO.userError "declaration order affected acceptance")
    ensure "declaration order cannot change the plan" (reordered.request == receipt.checked.request)
    for (label, changed) in [
        ("duplicate port consumption", {receipt.graph with inputs := [⟨"a", .input⟩]}),
        ("missing boundary", {receipt.graph with outputs := []}),
        ("unknown occurrence", {receipt.graph with outputs := [⟨"missing", .output⟩]}),
        ("two primal legs", {receipt.graph with edges := [⟨⟨"a", .output⟩, ⟨"b", .output⟩⟩], inputs := [⟨"b", .input⟩], outputs := [⟨"a", .input⟩]}),
        ("two dual legs", {receipt.graph with edges := [⟨⟨"a", .input⟩, ⟨"b", .input⟩⟩], inputs := [⟨"b", .output⟩], outputs := [⟨"a", .output⟩]}),
        ("reversed boundary roles", {receipt.graph with inputs := receipt.graph.outputs, outputs := receipt.graph.inputs}),
        ("trace is not this profile", {receipt.graph with edges := [⟨⟨"a", .input⟩, ⟨"a", .output⟩⟩], outputs := [⟨"b", .output⟩]}),
        ("duplicate occurrence identity", {receipt.graph with occurrences := receipt.graph.occurrences.map fun n => {n with name := "a"}}),
        ("hyperedge/copy", {receipt.graph with edges := receipt.graph.edges ++ receipt.graph.edges})] do
      ensure label (!(TensorNetwork.check env receipt.resources receipt.values changed receipt.output .nativeFast).isOk)
    let forged := receipt.values.map fun (name, value) => (name,
      if name == receipt.checked.left.value then
        .map {receipt.checked.product.product.left with conjugate := true} else value)
    ensure "forged implicit conjugation" (!(TensorNetwork.check env receipt.resources forged
      receipt.graph receipt.output .nativeFast).isOk)
    let .ok native := Native.compile result.statements | throw (IO.userError "network native lowering failed")
    let bad := native.instructions.map fun instruction => match instruction with
      | .gemm l lv lc r rv rc o ov mode policy alpha beta => .gemm l lv (!lc) r rv rc o ov mode policy alpha beta
      | other => other
    ensure "changed native conjugation cannot reuse graph acceptance" (!(Native.generate {native with instructions := bad}).isOk)
  let reused : Graph := {graph with occurrences := [⟨"a", 30⟩, ⟨"b", 30⟩]}
  let square := (setup .complexF64 "Complex" 2).map fun statement => match statement with
    | .numerical (.map 30 loan _ _) => .numerical (.map 30 loan 3 3)
    | .numerical (.map 32 loan _ _) => .numerical (.map 32 loan 3 3)
    | other => other
  ensure "same immutable tensor, distinct occurrences" (Functions.check
    (program (square ++ [.network reused 32 .nativeFast] ++ cleanup)) env).isOk
  ensure "ports do not grant disjoint mutable storage" (!((Functions.expand 4096 [] [] []
    (square ++ [.network reused 30 .nativeFast])).run {environment := env}).isOk)
  let invalid : List (String × List Functions.Statement) := [
      ("same dimension, different middle", [.numerical (.space 40 (id "Complex") 3),
        .numerical (.basis 41 40), .numerical (.map 42 23 3 41)]),
      ("same space, different basis", [.numerical (.basis 41 1), .numerical (.map 42 23 3 41)]),
      ("unsupported dual identification", [.numerical (.dualSpace 40 1),
        .numerical (.derivedBasis 41 4 40), .numerical (.map 42 23 3 41)]),
      ("conjugate is not dual", [.numerical (.involution 39 1), .numerical (.conjugateSpace 40 1 39),
        .numerical (.derivedBasis 41 4 40), .numerical (.map 42 23 3 41)])]
  for (label, extra) in invalid do
    let changed : Graph := {graph with occurrences := [⟨"a", 30⟩, ⟨"b", 42⟩]}
    ensure label (!((Functions.expand 4096 [] [] [] (setup .complexF64 "Complex" ++ extra ++
      [.network changed 32 .nativeFast])).run {environment := env}).isOk)
  IO.println "Finite networks: nominal ports, exact coverage, boundaries, reuse, forged flags and deterministic GEMM passed"

end VastitasKernel.Storage.NetworkRegression
