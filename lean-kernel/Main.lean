import VastitasKernel.SurfaceProtocol
import VastitasKernel.NamespaceProtocol
import VastitasKernel.NamespaceChecker
import VastitasKernel.NamespaceDiagnostics
import VastitasKernel.FunctionChecker
import VastitasKernel.Codegen
import VastitasKernel.Runtime

open VastitasKernel

private def process (mode input : String) : Lean.Json := Id.run do
  let parsed := Lean.Json.parse input
  match parsed with
  | .error message => return failureJson { code := "E_PROTOCOL", message }
  | .ok json =>
    let version := if (json.getObjValAs? Nat "version").toOption == some 3 then 3 else 2
    let checked : Except Diagnostic CertifiedModule := do
      if version == 3 then
        let raw ← (decodeNamespaceProgram json).mapError fun message => { code := "E_PROTOCOL", message }
        checkNamespaceProgram raw (mode == "emit") (Namespace.describeDiagnostic raw)
      else
        let raw ← (decodeSurfaceModule json).mapError fun message => { code := "E_PROTOCOL", message }
        (checkSurfaceProgram raw (mode == "emit")).mapError (DispatchChecker.describeDiagnostic (Surface.headers raw))
    match checked with
    | .error diagnostic => return failureJson diagnostic version
    | .ok checked =>
      if mode == "check" then return successJson none version
      match Codegen.generate checked with
      | .ok source => return successJson (some source) version
      | .error message => return failureJson { code := "E_CODEGEN", message } version

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
