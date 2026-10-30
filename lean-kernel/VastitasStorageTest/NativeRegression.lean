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
  IO.println s!"native storage: exact lowering and {mutations.length + 5} forged/boundary cases passed"

end VastitasKernel.Storage.Native.Regression
