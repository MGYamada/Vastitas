import VastitasKernel.LegacySource
import VastitasKernel.IndexedRuntime
import VastitasKernel.ResourceProtocol
import VastitasKernel.WireScan

open VastitasKernel

private def process (mode input : String) : Lean.Json := Id.run do
  if let .error message := WireScan.scan input then
    return failureJson { code := "E_PROTOCOL", message }
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

/-- Stop reading past the byte bound, so an oversized request is never
buffered whole; `main` then answers it with `E_PROTOCOL`. -/
private partial def readBounded (stream : IO.FS.Stream) (limit : Nat) (data : ByteArray) : IO ByteArray := do
  if data.size > limit then return data
  let chunk ← stream.read 65536
  if chunk.isEmpty then return data
  readBounded stream limit (data ++ chunk)

def main (args : List String) : IO UInt32 := do
  let output ← IO.getStdout
  let mode := args.headD "check"
  if args.length > 1 || !(mode == "check" || mode == "emit") then
    output.putStrLn ((failureJson { code := "E_ARGUMENT", message := "usage: vastitas-kernel [check|emit]" }).compress)
    return 1
  let limit := ({} : WireScan.Bounds).bytes
  let response ← try
    let data ← readBounded (← IO.getStdin) limit .empty
    if data.size > limit then
      pure (failureJson { code := "E_PROTOCOL", message := s!"IR input exceeds {limit} bytes" })
    else match String.fromUTF8? data with
      | some input => pure (process mode input)
      | none => pure (failureJson { code := "E_PROTOCOL", message := "cannot read UTF-8 IR input: invalid UTF-8" })
  catch error =>
    pure (failureJson { code := "E_PROTOCOL", message := s!"cannot read UTF-8 IR input: {error}" })
  output.putStrLn response.compress
  match response.getObjValAs? Bool "ok" with
  | .ok true => return 0
  | _ => return 1
