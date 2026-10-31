import VastitasStorageTest.NumericalFixture

namespace VastitasKernel.Storage.OwnedPackageRegression
open Indexed NumericalFixture

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"owned package regression failed: {label}")

private def padded (scalar : Scalar) (rows := 3) : Layout := ⟨scalar.width, rows, 2, max 1 (rows + 1), false⟩

private def producer (scalar : Scalar) (implementation : String) (rows := 3) : Functions.Function :=
  ⟨1, [.space 0 (id implementation) 2, .basis 1 0], [(9, .ownedMapTo 1 rows)], [
    .numerical (.space 2 (id implementation) rows), .numerical (.basis 3 2),
    .action (.allocate 4 scalar (2 * rows + 4)),
    .action (.borrow 5 (.owner 4) (padded scalar rows) .write),
    .action (.fill 5 (payload scalar)), .action (.release 5),
    .numerical (.ownedMap 6 4 (padded scalar rows) 1 3), .numerical (.packMap 9 6)]⟩

private def relay (implementation : String) (rows := 3) : Functions.Function :=
  ⟨2, [.space 0 (id implementation) 2, .basis 1 0, .ownedMapTo 2 1 rows], [(7, .ownedMapTo 1 rows)], [
    .numerical (.unpackMap 2 3 4 5), .call 3 [0, 1, 3, 4, 5] [6], .numerical (.packMap 7 6)]⟩

private def helper (implementation : String) (rows := 3) : Functions.Function :=
  ⟨3, [.space 0 (id implementation) 2, .basis 1 0,
    .space 2 (id implementation) rows, .basis 3 2, .ownedMap 4 1 3], [(4, .ownedMap 1 3)], [
    .numerical (.borrowOwned 5 4 .read), .numerical (.ownedView 6 5 4), .action (.release 5)]⟩

private def body (implementation : String) : List Functions.Statement := [
  .numerical (.space 0 (id implementation) 2), .numerical (.basis 1 0),
  .call 1 [0, 1] [10], .call 2 [0, 1, 10] [11], .action (.move 11 12),
  .numerical (.unpackMap 12 13 14 15), .numerical (.borrowOwned 16 15 .read),
  .numerical (.ownedView 17 16 15), .action (.release 16), .action (.drop 15)]

private def program (scalar : Scalar) (implementation : String)
    (statements : List Functions.Statement) (rows := 3) : Functions.Program :=
  ⟨[⟨0, [], [], statements⟩, producer scalar implementation rows, relay implementation rows, helper implementation rows], 0⟩

#eval show IO Unit from do
  let .ok declarations := Indexed.Source.checkDeclarations source
    | throw (IO.userError "common numerical declaration audit failed")
  let env := declarations.resolved.declarations.indexed
  for (scalar, implementation) in [(Scalar.f64, "Real"), (.complexF64, "Complex")] do
    for rows in [0, 3] do
      let .ok checked := Functions.check (program scalar implementation (body implementation) rows) env
        | throw (IO.userError "valid dependent generative package rejected")
      check "actual result receipts exclude probes" (checked.context.packageResults.size == 2)
      check "closed entry has no resources or numerical values" (checked.context.resources.allocations.isEmpty &&
        checked.context.resources.loans.isEmpty && checked.context.numerical.isEmpty)
      let openings := checked.context.packages.toList.filter fun receipt => match receipt.operation with
        | .open .. => true | _ => false
      let [first, second] := openings | throw (IO.userError "expected two actual openings")
      check "repack/reopen introduces a fresh target and basis" (
        first.checked.original.target.space.dimension == rows &&
        (first.operation.view first.checked.original first.output).target.brand !=
          (second.operation.view second.checked.original second.output).target.brand)
      let .ok native := Native.compile checked.statements | throw (IO.userError "package schedule lowering failed")
      check "packages add no allocation/copy or numerical runtime" (
        native.instructions.countP (fun i => match i with | .allocate .. => true | _ => false) == 1 &&
        native.instructions.all (fun i => match i with | .copy .. => false | _ => true) && !native.needsNumerical)
      let some receipt := openings.head? | throw (IO.userError "missing opening")
      check "forged stale allocation cannot open" (!(Numerical.checkPackage env
        {receipt.resources with allocations := []} receipt.values receipt.operation receipt.source receipt.output).isOk)
      check "forged reused witness cannot open" (!(Numerical.checkPackage env receipt.resources receipt.values
        (.open receipt.checked.original.source.space.brand receipt.checked.original.source.brand)
        receipt.source receipt.output).isOk)
      let forged := receipt.values.map fun (key, value) => (key, match value with
        | .ownedPackage view => .ownedPackage {view with target := {view.target with space := {view.target.space with origin := .dual 999}}}
        | other => other)
      check "forged hidden origin cannot open" (!(Numerical.checkPackage env receipt.resources forged
        receipt.operation receipt.source receipt.output).isOk)
      let forgedProfile := receipt.values.map fun (key, value) => (key, match value with
        | .ownedPackage view => .ownedPackage {view with target := {view.target with space := {
            view.target.space with coefficient := if scalar == .f64 then .complex else .real}}}
        | other => other)
      check "forged hidden coefficient cannot open" (!(Numerical.checkPackage env receipt.resources forgedProfile
        receipt.operation receipt.source receipt.output).isOk)
      let forgedOwner := receipt.values.map fun (key, value) => (key, match value with
        | .ownedPackage view => .ownedPackage {view with owner := view.owner + 1000}
        | other => other)
      check "opaque value name must equal owner" (!(decide (Numerical.Valid env forgedOwner)))
      let invalidContext : Functions.Context := {
        environment := env
        resources := receipt.resources
        numerical := receipt.values.map (fun (key, value) => ((if key == receipt.source then key + 1000 else key), value))
        nextSymbol := receipt.output + 10 }
      check "forged alternative package key cannot expose raw borrow" (
        !(Functions.operation [(0, receipt.checked.original.owner), (1, receipt.output + 1)]
          (.borrow 2 (.owner 0) receipt.checked.original.layout .read) |>.run invalidContext).isOk)
    let root := body implementation
    let replaceCall (extra : List Functions.Statement) := root.take 3 ++ extra ++ root.drop 3
    for (label, extra) in [
        ("opaque raw borrow", [.action (.borrow 50 (.owner 10) (padded scalar) .read), .action (.release 50)]),
        ("opaque owned-map reinterpretation", [.numerical (.ownedMap 50 10 (padded scalar) 1 1)]),
        ("double opening", [.numerical (.unpackMap 10 50 51 52), .numerical (.unpackMap 10 53 54 55)]),
        ("moved package", [.action (.move 10 50)]),
        ("wrong source basis", [.numerical (.basis 50 0), .call 2 [0, 50, 10] [51]])] do
      check label (!(Functions.check (program scalar implementation (replaceCall extra)) env).isOk)
    let branching : Functions.Program := program scalar implementation [.branch true root root]
    let .ok branched := Functions.check branching env | throw (IO.userError "both closed package branches rejected")
    check "both branch package/result receipts retained" (branched.context.packageResults.size == 4 &&
      branched.context.packages.size > 10)
    let bad : Functions.Function := {producer scalar implementation with
      body := (producer scalar implementation).body.filter fun statement => match statement with
        | .action (.fill ..) => false | _ => true}
    check "unused uninitialized package producer rejected"
      (!(Functions.check ⟨[⟨0, [], [], []⟩, bad], 0⟩ env).isOk)
    let borrowed : Functions.Function := {producer scalar implementation with
      body := (producer scalar implementation).body.filter fun statement => match statement with
        | .action (.release ..) => false | _ => true}
    check "outstanding loans cannot be packaged"
      (!(Functions.check ⟨[⟨0, [], [], []⟩, borrowed], 0⟩ env).isOk)
    let rawResult : Functions.Function := {producer scalar implementation with
      results := [(9, .owned ⟨scalar, 10, [padded scalar]⟩)]}
    check "package cannot escape through raw result"
      (!(Functions.check ⟨[⟨0, [], [], []⟩, rawResult], 0⟩ env).isOk)
    let escape : Functions.Function := {producer scalar implementation with results := [(6, .ownedMap 1 3)]}
    check "hidden local basis cannot escape unboxed"
      (!(Functions.check ⟨[⟨0, [], [], []⟩, escape], 0⟩ env).isOk)

end VastitasKernel.Storage.OwnedPackageRegression
