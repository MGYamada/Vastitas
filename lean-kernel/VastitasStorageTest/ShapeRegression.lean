import VastitasKernel.StorageShapeFunctions

namespace VastitasKernel.Storage.ShapeRegression

private def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"runtime shapes: {label}")

private def get (label : String) (result : Except Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error problem => throw (IO.userError s!"runtime shapes: {label}: {repr problem}")

private def slots : Shapes.Slots := (List.range 10).map fun n => (n, if n % 2 == 0 then .nat else .int)
private def literal : Scalar → Literal
  | .f64 => .f64 0
  | .complexF64 => .complexF64 0 0

-- Logical m×k, k×n and m×n maps have independent leading dimensions,
-- capacities and destination-row slot. Both input transposes are physical.
private def aShape (transposed : Bool) : Shapes.Layout :=
  if transposed then ⟨.slot 2, .slot 0, .slot 3, true⟩
  else ⟨.slot 0, .slot 2, .slot 3, false⟩
private def bShape (transposed : Bool) : Shapes.Layout :=
  if transposed then ⟨.slot 1, .slot 2, .slot 4, true⟩
  else ⟨.slot 2, .slot 1, .slot 4, false⟩
private def cShape : Shapes.Layout := ⟨.slot 9, .slot 1, .slot 5, false⟩

private def setup (scalar : Scalar) (ta tb : Bool) (mode : GemmMode) : List Shapes.Action :=
  [.allocate 10 scalar (.slot 6) (aShape ta),
   .allocate 11 scalar (.slot 7) (bShape tb), .allocate 12 scalar (.slot 8) cShape,
   .borrow 20 (.owner 10) .write, .fill 20 (literal scalar), .release 20,
   .borrow 21 (.owner 10) .read,
   .borrow 22 (.owner 11) .write, .fill 22 (literal scalar), .release 22,
   .borrow 23 (.owner 11) .read] ++
  (if mode == .accumulate then
    [.borrow 24 (.owner 12) .write, .fill 24 (literal scalar), .release 24,
     .borrow 25 (.owner 12) .readWrite]
   else [.borrow 25 (.owner 12) .write])

private def request (mode : GemmMode) : Gemm :=
  ⟨21, 23, 25, false, false, mode, .nativeFast, none, none⟩
private def cleanup : List Shapes.Action :=
  [.release 21, .release 23, .release 25, .move 12 30, .drop 10, .drop 11, .drop 30]

private def capacity (rows columns leading : Nat) : Nat :=
  if rows == 0 || columns == 0 then 0 else (columns - 1) * leading + rows
private def valuation (m n k padding : Nat) (ta tb : Bool) : Shapes.Valuation :=
  let ar := if ta then k else m
  let ac := if ta then m else k
  let br := if tb then n else k
  let bc := if tb then k else n
  let lda := max 1 ar + padding
  let ldb := max 1 br + padding + 1
  let ldc := max 1 m + padding + 2
  fun slot => match slot with
    | 0 => m | 1 => n | 2 => k | 3 => lda | 4 => ldb | 5 => ldc
    | 6 => capacity ar ac lda | 7 => capacity br bc ldb | 8 => capacity m n ldc
    | 9 => m | _ => 0

private def guardsPass (values : Shapes.Valuation) (guards : List Shapes.Guard) : Bool :=
  guards.all (Shapes.Guard.eval values)

#eval show IO Unit from do
  let mut concreteCases := 0
  for scalar in [Scalar.f64, .complexF64] do
    for ta in [false, true] do
      for tb in [false, true] do
        for mode in [GemmMode.overwrite, .accumulate] do
          let code := setup scalar ta tb mode ++ [.gemm (request mode)]
          let checked ← get "symbolic rectangular GEMM" (Shapes.check slots {} code)
          let closed ← get "symbolic cleanup" (Shapes.check slots {} (code ++ cleanup))
          for (m, n, k) in [(2, 5, 3), (0, 5, 3), (2, 0, 3), (2, 5, 0), (0, 0, 0)] do
            let values := valuation m n k 2 ta tb
            ensure "all physical and GEMM guards hold" (guardsPass values checked.guards)
            let concrete ← get "instantiate exact GEMM schedule" (Shapes.instantiate values 4096 {} code)
            let actual ← get "actual GEMM resource run" (Storage.run 4096 {} concrete)
            ensure "exact whole state equals symbolic interpretation" (actual == checked.after.eval values)
            ensure "independent actual final audit" (auditState actual)
            let some destination := actual.allocation? 2 | throw (IO.userError "missing destination")
            ensure "exact overwrite/accumulate version count"
              (destination.version == if mode == .accumulate then 2 else 1)
            if m == 0 || n == 0 then
              ensure "empty actual writes retain real normalized history" (destination.initialization == .none)
            let concreteClosed ← get "instantiate cleanup" (Shapes.instantiate values 4096 {} (code ++ cleanup))
            let actualClosed ← get "actual cleanup" (Storage.run 4096 {} concreteClosed)
            ensure "closed state exact, including used names and next identity"
              (actualClosed == closed.after.eval values && actualClosed.allocations.isEmpty && actualClosed.loans.isEmpty)
            concreteCases := concreteCases + 1
  ensure "all scalar/orientation/mode/zero combinations ran" (concreteCases == 80)

  let code := setup .f64 true false .overwrite
  let checked ← get "live caller fixture" (Shapes.check slots {} code)
  let frame := checked.after
  let some original := frame.allocation? 0 | throw (IO.userError "missing source")
  let some input := frame.loan? 21 | throw (IO.userError "missing source loan")
  let some output := frame.loan? 25 | throw (IO.userError "missing destination loan")
  for (label, forged) in [
      ("duplicate allocation identity", {frame with allocations := original :: frame.allocations}),
      ("reused lexical name", {frame with used := 10 :: frame.used}),
      ("owner absent from ledger", {frame with used := frame.used.filter (· != 10)}),
      ("forged recorded loan layout", {frame with loans := frame.loans.map fun loan =>
        if loan.name == 21 then {loan with layout := {loan.layout with leading := .slot 99}} else loan}),
      ("noncanonical write history", {frame with allocations := frame.allocations.map fun allocation =>
        if allocation.identity == 0 then {allocation with initialization := .record cShape .none} else allocation}),
      ("uninitialized readable input", {frame with allocations := frame.allocations.map fun allocation =>
        if allocation.identity == 0 then {allocation with initialization := .none} else allocation}),
      ("missing loan parent", {frame with loans := frame.loans.map fun loan =>
        if loan.name == 21 then {loan with parent := some 999} else loan}),
      ("conflicting whole write loan", {frame with used := 90 :: frame.used, loans := {output with name := 90} :: frame.loans})] do
    ensure label (!Shapes.auditFrame forged && !(Shapes.check slots forged []).isOk)
  ensure "symbolically different layout slots cannot be identified by one sample"
    (({input.layout with leading := .slot 99}).eval (fun n => if n == 99 then 5 else valuation 2 5 3 2 true false n) ==
      input.layout.eval (valuation 2 5 3 2 true false))
  ensure "parent cannot be used while child is live" (!(Shapes.run 4096 frame
    [.borrow 90 (.loan 21) .read, .expect 21 0 0 (.f64 0)]).isOk)
  ensure "read parent cannot authorize writes" (!(Shapes.run 4096 frame [.borrow 90 (.loan 21) .write]).isOk)
  ensure "child must be returned inside out" (!(Shapes.run 4096 frame
    [.borrow 90 (.loan 21) .read, .release 21]).isOk)
  ensure "owner cannot move with active loans" (!(Shapes.run 4096 frame [.move 10 90]).isOk)
  ensure "accumulate cannot use write-only output" (!(Shapes.checkStep frame (.gemm (request .accumulate))).isOk)
  ensure "overwrite rejects beta even zero" (!(Shapes.checkStep frame
    (.gemm {request .overwrite with beta := some (.literal (.f64 0))})).isOk)
  ensure "coefficient loans remain outside this profile" (!(Shapes.checkStep frame
    (.gemm {request .overwrite with alpha := some (.loan 21)})).isOk)
  ensure "literal coefficient scalar is independently checked" (!(Shapes.checkStep frame
    (.gemm {request .overwrite with alpha := some (.literal (.complexF64 0 0))})).isOk)
  let singleton : Shapes.Layout := ⟨.slot 0, .slot 0, .slot 3, false⟩
  let aliasCode : List Shapes.Action := [.allocate 10 .f64 (.slot 6) singleton,
    .borrow 20 (.owner 10) .write, .fill 20 (.f64 0), .release 20,
    .borrow 21 (.owner 10) .readWrite,
    .gemm ⟨21, 21, 21, false, false, .overwrite, .nativeFast, none, none⟩]
  ensure "whole-map alias is rejected without empty-shape specialization" (!(Shapes.check slots {} aliasCode).isOk)
  ensure "even a literal empty allocation cannot grant an unwritten read" (!(Shapes.check [] {}
    [.allocate 10 .f64 (.literal 0) ⟨.literal 0, .literal 5, .literal 1, false⟩,
     .borrow 21 (.owner 10) .read]).isOk)
  let transposedOutput := code.map fun operation => match operation with
    | .allocate 12 scalar elements layout => .allocate 12 scalar elements {layout with transposed := true}
    | other => other
  ensure "transposed GEMM output rejected before valuation" (!(Shapes.check slots {}
    (transposedOutput ++ [.gemm (request .overwrite)])).isOk)


  for (label, malformed) in [
      ("missing extent slot", slots.filter (fun p => p.1 != 0)),
      ("Bool extent substitution", slots.map fun p => if p.1 == 0 then (0, .bool) else p),
      ("Unit capacity substitution", slots.map fun p => if p.1 == 6 then (6, .unit) else p),
      ("duplicate scalar slot", (0, Indexed.Core.PureType.nat) :: slots)] do
    ensure label (!(Shapes.check malformed {} code).isOk)
  ensure "renaming cannot introduce an unchecked extent slot" (!(Shapes.check slots {}
    [.allocate 10 .f64 (.slot 6) ((aShape true).rename fun n => if n == 0 then 99 else n)]).isOk)
  ensure "negative Int does not silently saturate" ((Shapes.narrowInt (-1)).isNone)
  ensure "Nat and positive Int narrowing agree at byte bound"
    (Shapes.narrowNat byteLimit == some byteLimit && Shapes.narrowInt (Int.ofNat byteLimit) == some byteLimit)
  ensure "oversized arbitrary-precision Nat is rejected" ((Shapes.narrowNat (byteLimit + 1)).isNone)

  let values := valuation 2 5 3 2 true false
  let badShape := fun slot => if slot == 9 then 3 else if slot == 8 then 100 else values slot
  let product ← get "dimension guards deferred to valuation" (Shapes.check slots {} (code ++ [.gemm (request .overwrite)]))
  ensure "mismatch passes separate physical frame guards" (guardsPass badShape frame.guards)
  ensure "mismatched output dimension fails actual operation guards" (!guardsPass badShape product.guards)
  let badConcrete ← get "instantiate dimension mismatch for negative concrete check"
    (Shapes.instantiate badShape 4096 {} (code ++ [.gemm (request .overwrite)]))
  ensure "existing concrete checker independently rejects mismatch" (!(Storage.run 4096 {} badConcrete).isOk)
  let cell ← get "checked last logical cell" (Shapes.check slots frame [.expect 21 1 2 (.f64 0)])
  ensure "padded transposed cell guard" (guardsPass values cell.guards)
  let concreteCell ← get "instantiate cell" (Shapes.instantiate values 4096 frame [.expect 21 1 2 (.f64 0)])
  ensure "actual initialized cell read" ((Storage.run 4096 (frame.eval values) concreteCell).isOk)
  let outside ← get "out-of-range cell emits guard" (Shapes.check slots frame [.expect 21 2 2 (.f64 0)])
  ensure "out-of-range cell guard rejects" (!guardsPass values outside.guards)
  let outsideCode ← get "instantiate out-of-range cell" (Shapes.instantiate values 4096 frame [.expect 21 2 2 (.f64 0)])
  ensure "concrete out-of-range cell rejects" (!(Storage.run 4096 (frame.eval values) outsideCode).isOk)
  let tooWide := fun slot => if slot == 6 then byteLimit else values slot
  ensure "byte capacity multiplication overflow is guarded" (!guardsPass tooWide frame.guards)
  let tooLarge := fun slot => if slot == 3 then dimensionLimit + 1 else values slot
  ensure "LP64 layout narrowing is guarded" (!guardsPass tooLarge frame.guards)

  let caller : Shapes.Functions.Context := {resources := frame}
  let child ← get "call exact whole-map child" (caller.step (.borrow 90 (.loan 21) .read))
  ensure "call cannot leave its child live" (!(Shapes.Functions.checkCall caller child).isOk)
  let returned ← get "call returns child" (child.step (.release 90))
  let receipt ← get "actual call slice receipt" (Shapes.Functions.checkCall caller returned)
  ensure "exact source call slice" (receipt.slice == [.borrow 90 (.loan 21) .read, .release 90])
  let actualCall ← get "call slice instantiation" (Shapes.instantiate values 4096 frame receipt.slice)
  let actualAfter ← get "call slice concrete run" (Storage.run 4096 (frame.eval values) actualCall)
  ensure "call restores exact concrete parent loan table" (actualAfter.loans == (frame.eval values).loans)
  let writer ← get "call write child" (caller.step (.borrow 91 (.loan 25) .write))
  let writer ← get "call actual whole-map write" (writer.step (.fill 91 (.f64 0)))
  let writer ← get "call write child return" (writer.step (.release 91))
  let writerReceipt ← get "initialized caller destination may survive" (Shapes.Functions.checkCall caller writer)
  let writerCode ← get "write call instantiation" (Shapes.instantiate values 4096 frame writerReceipt.slice)
  let writerState ← get "write call actual run" (Storage.run 4096 (frame.eval values) writerCode)
  let some written := writerState.allocation? 2 | throw (IO.userError "missing write-call destination")
  ensure "real call preserves parents while recording an actual write"
    (writerState == writer.resources.eval values && writerState.loans == (frame.eval values).loans && written.version == 1)

  ensure "call replay rejects forged resulting epoch" (!(Shapes.Functions.checkCall caller
    {returned with resources := {returned.resources with allocations := returned.resources.allocations.map fun a =>
      if a.identity == 0 then {a with version := a.version + 1} else a}}).isOk)
  let escaped ← get "local allocation for exit rejection" (returned.step (.allocate 91 .f64 (.slot 6) (aShape true)))
  ensure "call cannot escape a local owner" (!(Shapes.Functions.checkCall caller escaped).isOk)
  IO.println "runtime shapes: 80 exact concrete GEMM valuations; forged frames, snapshots, initialization, aliases, typed slots, guards, narrowing and caller restoration passed"

end VastitasKernel.Storage.ShapeRegression
