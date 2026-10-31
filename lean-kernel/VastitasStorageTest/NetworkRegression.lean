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
  for condition in [false, true] do
    let network : Functions.Statement := .network graph 32 .nativeFast
    for (yes, no) in [([network], [multiply]), ([multiply], [network])] do
      let .ok branched := Functions.check (program (setup .complexF64 "Complex" ++ [network,
          .branch condition yes no, network] ++ cleanup)) env
        | throw (IO.userError "valid mixed network/GEMM branch rejected")
      ensure "branch receipts retain prefix, either arm and suffix exactly once"
        (branched.context.networks.size == 3 && branched.context.products.size == 4)
      ensure "branch network origins retain the actual environment"
        (branched.context.networks.all fun receipt => receipt.environment == env)
    let nested : Functions.Statement := .branch condition [network] [network]
    let .ok branched := Functions.check (program (setup .complexF64 "Complex" ++ [network,
        .branch condition [nested] [nested], network] ++ cleanup)) env
      | throw (IO.userError "valid nested network branch rejected")
    ensure "both nested arms retain all six actual receipts, excluding probes"
      (branched.context.networks.size == 6 && branched.context.products.size == 6)
  let vectors : List Functions.Statement := [
    .numerical (.dualSpace 40 0), .numerical (.derivedBasis 41 3 40),
    .numerical (.involution 42 0), .numerical (.conjugateSpace 43 0 42),
    .numerical (.derivedBasis 44 3 43), .numerical (.metric 45 3 42 .identity),
    .action (.allocate 50 .complexF64 2), .action (.allocate 51 .complexF64 1),
    .action (.borrow 52 (.owner 50) (layout 2 1) .write),
    .action (.fill 52 (payload .complexF64)), .action (.release 52),
    .action (.borrow 53 (.owner 50) (layout 2 1) .read),
    .action (.borrow 54 (.owner 50) (layout 2 1) .read),
    .action (.borrow 55 (.owner 51) (layout 1 1) .write),
    .numerical (.vector 56 53 3), .numerical (.vector 57 53 41), .numerical (.vector 58 54 3)]
  let network : Functions.Statement := .network graph 32 .nativeFast
  let evaluate : Functions.Statement := .numerical (.evaluate 57 56 55 .dual .overwrite .nativeFast)
  let hermitian : List Functions.Statement := [.numerical (.conjugateVector 59 56 44 42),
    .numerical (.evaluate 59 58 55 (.hermitian 45) .overwrite .nativeFast), .action (.release 59)]
  let releaseVectors : List Functions.Statement := [.action (.release 55),
    .action (.release 53), .action (.release 54), .action (.drop 50), .action (.drop 51)]
  for condition in [false, true] do
    for (yes, no) in [([network] ++ hermitian, [evaluate, network]),
        ([evaluate, network], [network] ++ hermitian)] do
      let body := setup .complexF64 "Complex" ++ vectors ++ [network, evaluate,
        .branch condition yes no, network, evaluate] ++ releaseVectors ++ cleanup
      let .ok combined := Functions.check (program body) env
        | throw (IO.userError "combined network/vector evaluation branch rejected")
      ensure "combined branches retain every receipt family exactly once"
        (combined.context.networks.size == 4 && combined.context.products.size == 4 &&
          combined.context.evaluations.size == 4 && combined.context.vectorConjugates.size == 1)
      ensure "combined receipt origins retain the actual environment"
        (combined.context.networks.all (fun receipt => receipt.environment == env) &&
          combined.context.evaluations.all (fun receipt => receipt.environment == env) &&
          combined.context.vectorConjugates.all (fun receipt => receipt.environment == env))
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
