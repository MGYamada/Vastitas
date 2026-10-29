import VastitasKernel.SurfaceProtocol
import VastitasKernel.NamespaceProtocol
import VastitasKernel.NamespaceChecker
import VastitasKernel.Edit
import VastitasKernel.Authority
import VastitasKernel.NamespaceDiagnostics
import VastitasKernel.FunctionChecker
import VastitasKernel.Codegen
import VastitasKernel.IndexedRuntime
import VastitasKernel.IndexedAcceptance

open VastitasKernel

private def process (mode input : String) : Lean.Json := Id.run do
  let parsed := Lean.Json.parse input
  match parsed with
  | .error message => return failureJson { code := "E_PROTOCOL", message }
  | .ok json =>
    let requested := (json.getObjValAs? Nat "version").toOption
    let version := requested.getD 2
    if version == 7 then
      if mode == "emit" then
        match Indexed.Wire.check json true with
        | .error diagnostic => return failureJson diagnostic version
        | .ok accepted =>
          match Indexed.Core.Codegen.generate accepted.checked.executable.core with
          | .error message => return failureJson { code := "E_CODEGEN", message } version
          | .ok source => return successJson (some source) version
      else
        match Indexed.Wire.check json false with
        | .error diagnostic => return failureJson diagnostic version
        | .ok _ => return successJson none version
    let checked : Except Diagnostic CertifiedModule := do
      unless supportedProtocolVersions.contains version do
        throw { code := "E_PROTOCOL", message := unsupportedProtocolVersion version }
      if version == 3 || version == 5 || version == 6 || (version == 4 && (json.getObjValAs? String "input").toOption == some "package") then
        let raw ← (decodeNamespaceProgram json).mapError fun message => { code := "E_PROTOCOL", message }
        if version == 5 || version == 6 then
          (if version == 6 then checkAuthorityProgram raw (mode == "emit") else checkEditProgram raw (mode == "emit")).mapError fun diagnostic =>
            match Namespace.lower raw.indexed with
            | .ok lowered => Namespace.describeDiagnostic raw lowered diagnostic
            | .error _ => diagnostic
        else checkNamespaceProgram raw (mode == "emit") (Namespace.describeDiagnostic raw)
      else
        let raw ← (decodeSurfaceModule json).mapError fun message => { code := "E_PROTOCOL", message }
        (checkSurfaceProgram raw (mode == "emit")).mapError (DispatchChecker.describeDiagnostic (Surface.headers raw))
    match checked with
    | .error diagnostic => return failureJson diagnostic version
    | .ok checked =>
      if mode == "check" then
        match LegacyIndexed.check checked.val false with
        | .ok _ => return successJson none version
        | .error diagnostic => return failureJson diagnostic version
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
