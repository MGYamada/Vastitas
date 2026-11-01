import VastitasKernel.StorageCodegen
import VastitasKernel.StorageProtocol

namespace VastitasKernel.Storage.Native.Regression

#eval show IO Unit from do
  let .ok json := Lean.Json.parse (include_str "../../tests/fixtures/storage.json")
    | throw (IO.userError "invalid storage fixture")
  let .ok checked := Wire.check json | throw (IO.userError "storage fixture rejected")
  let .ok plan := compile checked.input | throw (IO.userError "native lowering rejected")
  let mutations : List (String × (Instruction → Instruction)) := [
    ("allocation identity", fun i => match i with | .allocate _ s n => .allocate 99 s n | _ => i),
    ("allocation size", fun i => match i with | .allocate id s n => .allocate id s (n+1) | _ => i),
    ("scalar", fun i => match i with | .allocate id _ n => .allocate id .complexF64 n | _ => i),
    ("drop provenance", fun i => match i with | .drop _ => .drop 99 | _ => i),
    ("fill view", fun i => match i with | .fill id l v => .fill id {l with offset := 8} v | _ => i),
    ("literal payload", fun i => match i with | .fill id l _ => .fill id l (.f64 0) | _ => i),
    ("store cell", fun i => match i with | .store id l r c v => .store id l (r+1) c v | _ => i),
    ("transpose", fun i => match i with | .expect id l r c v => .expect id l.transpose r c v | _ => i),
    ("copy alias", fun i => match i with | .copy id l _ out => .copy id l id out | _ => i),
    ("copy transpose", fun i => match i with | .copy id l dest out => .copy id l.transpose dest out | _ => i),
    ("branch selection", fun i => match i with | .branch b => .branch (!b) | _ => i),
    ("branch structure", fun i => match i with | .otherwise => .finish | _ => i)]
  for (name, mutate) in mutations do
    let changed := plan.instructions.map mutate
    if changed == plan.instructions then throw (IO.userError s!"ineffective mutation: {name}")
    if (generate {plan with instructions := changed}).isOk then
      throw (IO.userError s!"generated forged native plan: {name}")
  for changed in [plan.instructions.drop 1, plan.instructions ++ [.drop 0], []] do
    if (generate {plan with instructions := changed}).isOk then throw (IO.userError "forged operation sequence accepted")
  if (generate plan false (byteLimit+1)).isOk then throw (IO.userError "oversized budget accepted")
  -- Even the unchosen arm must satisfy resource initialization and closure.
  let bad : List Statement := [.branch false [.action (.allocate 100 .f64 1)] []]
  if (generate {input := bad, instructions := []}).isOk then throw (IO.userError "unchecked branch accepted")
  let view : Layout := ⟨8,2,3,4,false⟩
  let stores := [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2)].map fun (row, column) =>
    Statement.action (.store 1 row column (.f64 0))
  let input := [Statement.action (.allocate 0 .f64 12), .action (.borrow 1 (.owner 0) view .write)] ++
    stores ++ [.action (.release 1), .action (.borrow 2 (.owner 0) view.transpose .read),
      .action (.expect 2 2 1 (.f64 0)), .action (.release 2), .action (.drop 0)]
  let .ok initialized := compile input | throw (IO.userError "complete cell writes failed native compilation")
  let instructions := initialized.instructions.filter fun i => match i with
    | .store _ _ 1 2 _ => false | _ => true
  if (generate {initialized with instructions}).isOk then
    throw (IO.userError "forged native omission of one initializing store accepted")
  let input := initialized.input.filter fun s => match s with
    | .action (.store _ 1 2 _) => false | _ => true
  if (generate {initialized with input, instructions}).isOk then
    throw (IO.userError "matching forged input/native omission bypassed initialization")
  let selfCopy := [Action.allocate 0 .f64 12, .borrow 1 (.owner 0) view .write,
    .fill 1 (.f64 0), .release 1, .borrow 2 (.owner 0) view.transpose .readWrite,
    .copy 2 2, .release 2, .drop 0] |>.map Statement.action
  let .ok erased := compile selfCopy | throw (IO.userError "valid self-copy rejected")
  if erased.instructions.any (fun i => match i with | .copy .. => true | _ => false) then
    throw (IO.userError "self-copy emitted a native operation")
  if !(generate erased).isOk then throw (IO.userError "erased self-copy generation failed")
  let injected := erased.instructions.take 2 ++ [.copy 0 view.transpose 0 view.transpose] ++
    erased.instructions.drop 2
  if (generate {erased with instructions := injected}).isOk then
    throw (IO.userError "forged native self-copy accepted")
  let invalid := selfCopy.map fun s => match s with
    | .action (.copy _ _) => .action (.copy 1 1) | _ => s
  if (generate {erased with input := invalid}).isOk then
    throw (IO.userError "erasure bypassed returned-loan rejection")
  IO.println s!"native storage: exact lowering, self-copy erasure and {mutations.length + 9} forged/boundary cases passed"

end VastitasKernel.Storage.Native.Regression
