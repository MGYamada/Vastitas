import VastitasKernel.StorageCodegen
import VastitasKernel.StorageProtocol
import VastitasKernel.StorageFunctionProtocol

open VastitasKernel.Storage

/-! Test-only compiler harness, not an alternative public wire protocol. -/
def main (args : List String) : IO UInt32 := do
  let [input, output, budget] := args
    | IO.eprintln "expected input.json output.lean live-byte-budget"; return 1
  let source ← IO.FS.readFile input
  let .ok json := Lean.Json.parse source | IO.eprintln "invalid JSON"; return 1
  let some budget := budget.toNat? | IO.eprintln "invalid budget"; return 1
  let generated := if (json.getObjVal? "functions").isOk then do
    let checked ← Functions.Wire.check json
    Functions.generate checked.input true budget
  else do
    let checked ← Wire.check json
    let plan ← Native.compile checked.input
    Native.generate plan true budget
  match generated with
  | .error error => IO.eprintln s!"resource component rejected: {error.code}: {error.message}"; return 1
  | .ok result => IO.FS.writeFile output result; return 0
