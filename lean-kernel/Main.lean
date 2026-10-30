import VastitasKernel.LegacySource
import VastitasKernel.IndexedRuntime
import VastitasKernel.ResourceProtocol

open VastitasKernel

private def process (mode input : String) : Lean.Json := Id.run do
  let parsed := Lean.Json.parse input
  match parsed with
  | .error message => return failureJson { code := "E_PROTOCOL", message }
  | .ok json =>
    let requested := (json.getObjValAs? Nat "version").toOption
    let version := requested.getD 2
    if version == 8 then
      match ResourceSource.Wire.check json (mode == "emit") with
      | .error diagnostic => return failureJson diagnostic version
      | .ok accepted =>
        if mode == "emit" then
          match ResourceSource.Codegen.generate accepted.input with
          | .error diagnostic => return failureJson diagnostic version
          | .ok generated =>
            return ((successJson (some generated.source) version).setObjVal! "storage_runtime" (Lean.toJson generated.storageRuntime)).setObjVal!
              "numerical_runtime" (Lean.toJson generated.numericalRuntime)
        else return successJson none version
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
    unless supportedProtocolVersions.contains version do
      return failureJson { code := "E_PROTOCOL", message := unsupportedProtocolVersion version } version
    if mode == "emit" then
      match Indexed.LegacySource.check json true with
      | .error diagnostic => return failureJson diagnostic version
      | .ok accepted =>
        match Indexed.Core.Codegen.generate accepted.checked.executable.core with
        | .ok source => return successJson (some source) version
        | .error message => return failureJson { code := "E_CODEGEN", message } version
    else
      match Indexed.LegacySource.check json false with
      | .error diagnostic => return failureJson diagnostic version
      | .ok _ => return successJson none version

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
