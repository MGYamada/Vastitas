import VastitasKernel.IndexedRuntime
import VastitasKernel.ResourceProtocol
import VastitasKernel.LLVM.Emission
import VastitasKernel.WireScan
import VastitasKernel.BuildIdentity

open VastitasKernel

private inductive Action where
  | check | emit | revision
  | llvm (header : LLVM.TargetHeader) (requireExecutable : Bool)

private def action : List String → Except Diagnostic Action
  | [] | ["check"] => .ok .check
  | ["emit"] => .ok .emit
  | ["function-revision"] => .ok .revision
  | [mode, triple, layout] => do
    unless mode == "llvm-check" || mode == "llvm-build" do
      throw {code := "E_ARGUMENT", message := "unknown kernel action"}
    let some t := LLVM.checkTargetText .triple triple.toUTF8.data.toList
      | throw {code := "E_ARGUMENT", message := "invalid LLVM target triple"}
    let some l := LLVM.checkTargetText .dataLayout layout.toUTF8.data.toList
      | throw {code := "E_ARGUMENT", message := "invalid LLVM data layout"}
    return .llvm ⟨t,l⟩ (mode == "llvm-build")
  | _ => .error {code := "E_ARGUMENT", message :=
      "usage: vastitas-kernel [check|emit|function-revision] or [llvm-check|llvm-build] TRIPLE LAYOUT"}

private def process (mode : Action) (input : String) : Lean.Json := Id.run do
  if let .error message := WireScan.scan input then
    return failureJson { code := "E_PROTOCOL", message }
  let parsed := Lean.Json.parse input
  match parsed with
  | .error message => return failureJson { code := "E_PROTOCOL", message }
  | .ok json =>
    let .ok version := json.getObjValAs? Nat "version"
      | return failureJson { code := "E_PROTOCOL", message := "IR version must be a natural number" }
    -- The version comes first: a request of any other version is never read
    -- under the schema of this one (#533).
    unless version == currentProtocol do
      return failureJson { code := "E_PROTOCOL", message := unsupportedProtocolVersion version } version
    let acknowledge (response : Lean.Json) :=
      if (json.getObjVal? "expected_function_revision").isOk then
        response.setObjVal! "function_revision_matched" true else response
    match mode with
    | .llvm header requireExecutable =>
      match LLVM.Emission.check json header requireExecutable with
      | .error d => return failureJson d
      | .ok artifact =>
        let evidence := Lean.Json.mkObj [
          ("kind", artifact.kind), ("ir", artifact.text),
          ("triple", String.ofList (header.triple.bytes.map fun b => Char.ofNat b.toNat)),
          ("layout", String.ofList (header.dataLayout.bytes.map fun b => Char.ofNat b.toNat)),
          ("verification_endpoint", "modeled-llvm-bytes"), ("verifier", "compiled-lean-checker"),
          ("official_kernel_checked", false), ("native_generated", false)]
        return acknowledge ((successJson none).setObjVal! "llvm" evidence)
    | .emit =>
      match ResourceSource.Wire.emit json with
      | .error diagnostic => return failureJson diagnostic
      | .ok generated =>
        return acknowledge <| ((successJson (some generated.source)).setObjVal! "storage_runtime" (Lean.toJson generated.storageRuntime)).setObjVal!
          "numerical_runtime" (Lean.toJson generated.numericalRuntime)
    | .check | .revision =>
      match ResourceSource.Wire.check json false with
      | .error diagnostic => return failureJson diagnostic
      | .ok input =>
        if let .revision := mode then
          let artifact := ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) input.checked
          unless ResourceSource.FunctionRevision.bounded artifact do
            return failureJson { code := "E_LIMIT", message := "function revision exceeds its 64 MiB output limit" }
          return acknowledge <| (successJson none).setObjVal! "function_revision" artifact
        return acknowledge (successJson none)

/-- Stop reading past the byte bound, so an oversized request is never
buffered whole; `main` then answers it with `E_PROTOCOL`. -/
private partial def readBounded (stream : IO.FS.Stream) (limit : Nat) (data : ByteArray) : IO ByteArray := do
  if data.size > limit then return data
  let chunk ← stream.read 65536
  if chunk.isEmpty then return data
  readBounded stream limit (data ++ chunk)

/-- Every response identifies this build: the digest of `Main`, of its kernel
imports and of the compiler limits, and the Lean version. See
`VastitasKernel.BuildIdentity`. -/
private def identity : Lean.Json :=
  Lean.Json.mkObj [("sources", Lean.Json.str kernel_source_digest%), ("lean", Lean.Json.str Lean.versionString)]

private def respond (output : IO.FS.Stream) (response : Lean.Json) : IO Unit :=
  output.putStrLn (response.setObjVal! "kernel" identity).compress

def main (args : List String) : IO UInt32 := do
  let output ← IO.getStdout
  let mode ← match action args with
    | .ok mode => pure (some mode)
    | .error d => respond output (failureJson d); pure none
  let some mode := mode | return 1
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
  respond output response
  match response.getObjValAs? Bool "ok" with
  | .ok true => return 0
  | _ => return 1
