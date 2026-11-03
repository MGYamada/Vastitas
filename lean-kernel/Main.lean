import VastitasKernel.LegacySource
import VastitasKernel.IndexedRuntime
import VastitasKernel.ResourceProtocol
import VastitasKernel.BuildIdentity

open VastitasKernel

private def process (mode input : String) : Lean.Json := Id.run do
  let parsed := Lean.Json.parse input
  match parsed with
  | .error message => return failureJson { code := "E_PROTOCOL", message }
  | .ok json =>
    let .ok version := json.getObjValAs? Nat "version"
      | return failureJson { code := "E_PROTOCOL", message := "IR version must be a natural number" }
    if version == 8 || version == 9 then
      if mode == "emit" then
        match ResourceSource.Wire.emit json with
        | .error diagnostic => return failureJson diagnostic version
        | .ok generated =>
          return ((successJson (some generated.source) version).setObjVal! "storage_runtime" (Lean.toJson generated.storageRuntime)).setObjVal!
            "numerical_runtime" (Lean.toJson generated.numericalRuntime)
      else
        match ResourceSource.Wire.check json false with
        | .error diagnostic => return failureJson diagnostic version
        | .ok _ => return successJson none version
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

/-- Every response identifies this build: the digest of `Main` and its kernel
imports, and the Lean version. See `VastitasKernel.BuildIdentity`. -/
private def identity : Lean.Json :=
  Lean.Json.mkObj [("sources", Lean.Json.str kernel_source_digest%), ("lean", Lean.Json.str Lean.versionString)]

private def respond (output : IO.FS.Stream) (response : Lean.Json) : IO Unit :=
  output.putStrLn (response.setObjVal! "kernel" identity).compress

def main (args : List String) : IO UInt32 := do
  let output ← IO.getStdout
  let mode := args.headD "check"
  if args.length > 1 || !(mode == "check" || mode == "emit") then
    respond output (failureJson { code := "E_ARGUMENT", message := "usage: vastitas-kernel [check|emit]" })
    return 1
  let response ← try
    let input ← (← IO.getStdin).readToEnd
    pure (process mode input)
  catch error =>
    pure (failureJson { code := "E_PROTOCOL", message := s!"cannot read UTF-8 IR input: {error}" })
  respond output response
  match response.getObjValAs? Bool "ok" with
  | .ok true => return 0
  | _ => return 1
