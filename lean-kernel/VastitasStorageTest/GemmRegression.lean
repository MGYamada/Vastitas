import VastitasKernel.StorageCodegen
import VastitasKernel.StorageProtocol
import VastitasKernel.StorageFunctions

namespace VastitasKernel.Storage.GemmRegression

private def view : Layout := ⟨0, 2, 2, 2, false⟩
private def setup : List Statement := [
  .action (.allocate 0 .f64 4), .action (.allocate 1 .f64 4),
  .action (.borrow 10 (.owner 0) view .write), .action (.fill 10 (.f64 0)),
  .action (.release 10), .action (.borrow 11 (.owner 0) view .read),
  .action (.borrow 12 (.owner 1) view .write)]
private def operation : Gemm := ⟨11, 11, 12, false, false, .overwrite, .nativeFast, none, none⟩

#eval show IO Unit from do
  let .ok state := run 4096 {} setup | throw (IO.userError "invalid GEMM setup")
  let .ok written := checkAction state (.gemm operation) | throw (IO.userError "read/read alias rejected")
  let some output := written.owner? 1 | throw (IO.userError "lost output")
  unless output.initialization.covers .f64 view && output.version == 1 do
    throw (IO.userError "overwrite failed to initialize/version output")
  let rejected := [
    {operation with mode := .accumulate}, -- write-only output cannot read
    {operation with conjugateLeft := true}, -- conjugation alone is not C
    {operation with left := 12}, -- write-only/uninitialized input
    {operation with output := 11}, -- read-only output
    {operation with right := 99}]
  for request in rejected do
    if (checkAction state (.gemm request)).isOk then throw (IO.userError "invalid GEMM accepted")
  let one : Layout := ⟨0, 1, 1, 1, false⟩
  let .ok coefficients := run 4096 state [
    .action (.allocate 20 .f64 1), .action (.borrow 21 (.owner 20) one .write),
    .action (.fill 21 (.f64 0x3fe0000000000000)), .action (.release 21),
    .action (.borrow 22 (.owner 20) one .read)]
    | throw (IO.userError "coefficient setup rejected")
  let scaled := {operation with alpha := some (.loan 22)}
  unless (checkAction coefficients (.gemm scaled)).isOk do
    throw (IO.userError "runtime coefficient loan rejected")
  unless (checkAction state (.gemm {operation with alpha := some (.literal (.f64 0x4000000000000000))})).isOk do
    throw (IO.userError "explicit real coefficient rejected")
  for request in [
      {operation with alpha := some (.literal (.complexF64 0 0))},
      {operation with alpha := some (.loan 11)}, -- a matrix is not one coefficient
      {operation with alpha := some (.loan 12)}, -- write-only coefficient
      {operation with beta := some (.literal (.f64 0))}, -- overwrite has no beta operand
      {operation with mode := .accumulate, beta := some (.literal (.f64 0))}] do
    if (checkAction coefficients (.gemm request)).isOk then throw (IO.userError "invalid coefficient contract accepted")
  let .ok suspendedCoefficient := checkAction coefficients (.borrow 23 (.loan 22) one .read)
    | throw (IO.userError "coefficient reborrow rejected")
  if (checkAction suspendedCoefficient (.gemm scaled)).isOk then throw (IO.userError "suspended coefficient read accepted")
  let .ok releasedCoefficient := checkAction coefficients (.release 22)
    | throw (IO.userError "coefficient release rejected")
  if (checkAction releasedCoefficient (.gemm scaled)).isOk then throw (IO.userError "released coefficient read accepted")
  let uninitialized := {coefficients with allocations := coefficients.allocations.map fun allocation =>
    if allocation.owner == 20 then {allocation with initialization := .none} else allocation}
  if (checkGemm uninitialized scaled).isOk then throw (IO.userError "forged uninitialized coefficient accepted")
  -- Same read/write loan cannot bypass GEMM's explicit physical separation.
  let .ok alias := run 4096 {} [
    .action (.allocate 0 .f64 4), .action (.borrow 1 (.owner 0) view .write),
    .action (.fill 1 (.f64 0)), .action (.release 1),
    .action (.borrow 2 (.owner 0) view .readWrite)]
    | throw (IO.userError "invalid alias setup")
  if (checkAction alias (.gemm {operation with left := 2, right := 2, output := 2})).isOk then
    throw (IO.userError "same-loan output alias accepted")
  let .ok suspended := checkAction state (.borrow 13 (.loan 11) view .read)
    | throw (IO.userError "valid input reborrow rejected")
  if (checkAction suspended (.gemm operation)).isOk then throw (IO.userError "suspended input accepted")
  let .ok transposed := checkAction state (.transpose 12) | throw (IO.userError "transpose rejected")
  if (checkAction transposed (.gemm operation)).isOk then throw (IO.userError "transposed output accepted")
  let .ok inputTransposed := checkAction state (.transpose 11) | throw (IO.userError "input transpose rejected")
  unless (checkAction inputTransposed (.gemm {operation with conjugateLeft := true})).isOk do
    throw (IO.userError "explicit supported conjugate-transpose rejected")
  let shapeSetup := setup.map fun s => match s with
    | .action (.borrow 12 source layout access) => .action (.borrow 12 source {layout with rows := 1} access)
    | other => other
  let .ok badShape := run 4096 {} shapeSetup | throw (IO.userError "shape setup rejected")
  if (checkAction badShape (.gemm operation)).isOk then throw (IO.userError "mismatched shape accepted")
  let .ok separate := run 4096 {} [
    .action (.allocate 0 .f64 8), .action (.borrow 1 (.owner 0) view .write),
    .action (.fill 1 (.f64 0)), .action (.release 1),
    .action (.borrow 11 (.owner 0) view .read),
    .action (.borrow 12 (.owner 0) {view with offset := 32} .write)]
    | throw (IO.userError "disjoint same-allocation setup rejected")
  unless (checkAction separate (.gemm operation)).isOk do
    throw (IO.userError "disjoint same-allocation GEMM rejected")
  let .ok joined := join written state | throw (IO.userError "branch join rejected")
  let .ok returned := checkAction joined (.release 12) | throw (IO.userError "join loan return rejected")
  if (checkAction returned (.borrow 14 (.owner 1) view .read)).isOk then
    throw (IO.userError "branch-only initialization became readable")
  -- The affine function path must recheck actual caller layouts and preserve
  -- its output initialization contract, including two inputs sharing a parent.
  let multiply : Functions.Function := ⟨1,
    [.borrowed 0 .f64 2 2 .read false, .borrowed 1 .f64 2 2 .read false,
      .borrowed 2 .f64 2 2 .write true], [],
    [.action (.gemm {operation with left := 0, right := 1, output := 2})]⟩
  let body : List Functions.Statement := setup.map fun statement => match statement with
    | .action action => .action action
    | _ => .branch false [] []
  let main : Functions.Function := ⟨0, [], [], body ++ [.call 1 [11, 11, 12] [],
    .action (.release 11), .action (.release 12),
    .action (.borrow 14 (.owner 1) view .read), .action (.release 14),
    .action (.drop 0), .action (.drop 1)]⟩
  unless (Functions.check ⟨[main, multiply], 0⟩).isOk do
    throw (IO.userError "checked affine GEMM call rejected")
  let .ok json := Lean.Json.parse (include_str "../../tests/fixtures/storage-gemm.json")
    | throw (IO.userError "invalid shared GEMM fixture")
  let .ok checked := Wire.check json | throw (IO.userError "shared GEMM fixture rejected")
  let .ok plan := Native.compile checked.input | throw (IO.userError "GEMM lowering rejected")
  unless plan.needsNumerical do throw (IO.userError "GEMM runtime dependency omitted")
  for mutation in [0, 1, 2, 3, 4, 5, 6, 7] do
    let instructions := plan.instructions.map fun instruction => match instruction with
      | .gemm l lv lc r rv rc o ov mode policy alpha beta => match mutation with
        | 0 => .gemm o lv lc r rv rc o ov mode policy alpha beta
        | 1 => .gemm l lv (!lc) r rv rc o ov mode policy alpha beta
        | 2 => .gemm l lv lc r rv (!rc) o ov mode policy alpha beta
        | 3 => .gemm l lv lc r rv rc o {ov with offset := ov.offset + 8} mode policy alpha beta
        | 4 => .gemm l lv lc r rv rc o ov (if mode == .overwrite then .accumulate else .overwrite) policy alpha beta
        | 5 => .gemm l lv lc r rv rc o ov mode policy (.literal (.f64 0x3ff0000000000000)) beta
        | 6 => .gemm l lv lc r rv rc o ov mode policy alpha (.view o ov.offset)
        | _ => .skip
      | other => other
    if instructions == plan.instructions then throw (IO.userError "ineffective native GEMM mutation")
    if (Native.generate {plan with instructions}).isOk then
      throw (IO.userError "forged GEMM operands/flags/mode accepted")
  IO.println "GEMM resource checks: initialization, permissions, aliases, views and forged lowering passed"

end VastitasKernel.Storage.GemmRegression
