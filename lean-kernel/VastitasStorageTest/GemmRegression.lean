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
    [.action (.gemm {operation with left := 0, right := 1, output := 2})], none⟩
  let body : List Functions.Statement := setup.map fun statement => match statement with
    | .action action => .action action
    | _ => .branch false [] []
  let main : Functions.Function := ⟨0, [], [], body ++ [.call 1 [11, 11, 12] [],
    .action (.release 11), .action (.release 12),
    .action (.borrow 14 (.owner 1) view .read), .action (.release 14),
    .action (.drop 0), .action (.drop 1)], none⟩
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

#eval show IO Unit from do
  -- N/T/R/C share physical obligations. Non-square inputs distinguish a
  -- transpose from conjugation; neither flag can alter layout or access rights.
  for scalar in [Scalar.f64, .complexF64] do
    for ta in [false, true] do
      for tb in [false, true] do
        let a : Layout := if ta then ⟨scalar.width, 3, 2, 5, true⟩ else ⟨scalar.width, 2, 3, 4, false⟩
        let b : Layout := if tb then ⟨scalar.width, 2, 3, 4, true⟩ else ⟨scalar.width, 3, 2, 5, false⟩
        let c : Layout := ⟨scalar.width, 2, 2, 4, false⟩
        let zero : Literal := if scalar == .f64 then .f64 0 else .complexF64 0 0
        let preparation : List Statement := [
          .action (.allocate 0 scalar 16), .action (.allocate 1 scalar 16), .action (.allocate 2 scalar 16),
          .action (.borrow 10 (.owner 0) a .write), .action (.fill 10 zero), .action (.release 10),
          .action (.borrow 11 (.owner 1) b .write), .action (.fill 11 zero), .action (.release 11),
          .action (.borrow 20 (.owner 0) a .read), .action (.borrow 21 (.owner 1) b .read),
          .action (.borrow 22 (.owner 2) c .write)]
        let .ok state := run 4096 {} preparation | throw (IO.userError "orientation setup rejected")
        for ca in [false, true] do
          for cb in [false, true] do
            let request : Gemm := ⟨20, 21, 22, ca, cb, .overwrite, .nativeFast, none, none⟩
            let .ok written := checkAction state (.gemm request)
              | throw (IO.userError "valid N/T/R/C operation rejected")
            let some output := written.owner? 2 | throw (IO.userError "orientation lost output")
            unless output.initialization.covers scalar c && output.version == 1 do
              throw (IO.userError "orientation lost exact output initialization")
            let .ok code := Native.action state (.gemm request)
              | throw (IO.userError "orientation lowering rejected")
            unless code == [.gemm 0 a ca 1 b cb 2 c .overwrite .nativeFast] do
              throw (IO.userError "orientation lowering changed layouts or flags")
            for bad in [{request with output := 20}, {request with left := 22},
                {request with mode := .accumulate}] do
              if (checkAction state (.gemm bad)).isOk then
                throw (IO.userError "orientation bypassed access or initialization")
            let .ok suspended := checkAction state (.borrow 23 (.loan 20) a .read)
              | throw (IO.userError "orientation reborrow rejected")
            if (checkAction suspended (.gemm request)).isOk then
              throw (IO.userError "orientation used suspended input")
            let .ok transposed := checkAction state (.transpose 20)
              | throw (IO.userError "orientation transpose rejected")
            if (checkAction transposed (.gemm request)).isOk then
              throw (IO.userError "conjugation concealed a shape mismatch")
            let input := preparation ++ [.action (.gemm request), .action (.release 20),
              .action (.release 21), .action (.release 22), .action (.drop 0),
              .action (.drop 1), .action (.drop 2)]
            let .ok plan := Native.compile input | throw (IO.userError "orientation plan rejected")
            let forged := plan.instructions.map fun instruction => match instruction with
              | .gemm l lv lc r rv rc o ov mode policy alpha beta =>
                .gemm l lv (!lc) r rv (!rc) o ov mode policy alpha beta
              | other => other
            if (Native.generate {plan with instructions := forged}).isOk then
              throw (IO.userError "numerically different but resource-valid flags were trusted")
  IO.println "GEMM N/T/R/C: exact flags, physical layouts and resource obligations passed"

end VastitasKernel.Storage.GemmRegression
