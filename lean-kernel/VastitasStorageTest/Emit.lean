import VastitasKernel.StorageCodegen
import VastitasKernel.StorageProtocol

open VastitasKernel.Storage

/-! Test-only compiler harness, not an alternative public wire protocol. -/
def main (args : List String) : IO UInt32 := do
  let [input, output, budget] := args
    | IO.eprintln "expected input.json output.lean live-byte-budget"; return 1
  let source ← IO.FS.readFile input
  let .ok json := Lean.Json.parse source | IO.eprintln "invalid JSON"; return 1
  let .ok checked := Wire.check json | IO.eprintln "resource component rejected"; return 1
  let .ok plan := Native.compile checked.input | IO.eprintln "native plan rejected"; return 1
  let some budget := budget.toNat? | IO.eprintln "invalid budget"; return 1
  match Native.generate plan true budget with
  | .error error => IO.eprintln error.message; return 1
  | .ok result => IO.FS.writeFile output result; return 0
