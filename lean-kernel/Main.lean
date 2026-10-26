import VastitasKernel.Protocol
import VastitasKernel.Checker
import VastitasKernel.Codegen

open VastitasKernel

private def process (mode input : String) : Lean.Json := Id.run do
  let parsed := Lean.Json.parse input >>= decodeModule
  match parsed with
  | .error message => return failureJson { code := "E_PROTOCOL", message }
  | .ok raw =>
    match checkModule raw (mode == "emit") with
    | .error diagnostic => return failureJson diagnostic
    | .ok checked =>
      if mode == "check" then return successJson
      match Codegen.generate checked with
      | .ok source => return successJson (some source)
      | .error message => return failureJson { code := "E_CODEGEN", message }

def main (args : List String) : IO UInt32 := do
  let output ← IO.getStdout
  let mode := args.headD "check"
  if args.length > 1 || !(mode == "check" || mode == "emit") then
    output.putStrLn ((failureJson { code := "E_ARGUMENT", message := "usage: vastitas-kernel [check|emit]" }).compress)
    return 1
  let input ← (← IO.getStdin).readToEnd
  let response := process mode input
  output.putStrLn response.compress
  match response.getObjValAs? Bool "ok" with
  | .ok true => return 0
  | _ => return 1
