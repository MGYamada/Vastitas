import Lean.Data.Json
import VastitasKernel.Program

namespace VastitasKernel
open Lean

/-- The wire schema epoch: the one protocol version that this kernel accepts
and answers with (#533). The frontend's `ir::PROTOCOL` and its `--version`
take the number from this definition (`build.rs` reads it), so a compiler and a
kernel of the same build agree on it. -/
def currentProtocol : Nat := 10

/-- The message of a request at any other version: the retired protocols 2 to
9 and every other number. A request is never read under another schema. -/
def unsupportedProtocolVersion (version : Nat) : String :=
  s!"IR protocol version {version} is not protocol {currentProtocol} of this kernel; " ++
    "the compiler and the kernel must come from the same Vastitas build: rebuild them together"

def spanJson (s : Span) : Json := Json.mkObj [
  ("start", toJson s.start), ("end", toJson s.end),
  ("line", toJson s.line), ("column", toJson s.column)]

def diagnosticJson (d : Diagnostic) : Json := Json.mkObj [
  ("code", toJson d.code), ("message", toJson d.message), ("span", spanJson d.span),
  ("notes", toJson (d.notes.map fun note => Json.mkObj [
    ("message", toJson note.message), ("span", spanJson note.span)]))]

def failureJson (d : Diagnostic) (version : Nat := currentProtocol) : Json := Json.mkObj [
  ("version", toJson version), ("ok", toJson false),
  ("diagnostics", toJson [diagnosticJson d])]

def successJson (source : Option String := none) (version : Nat := currentProtocol) : Json := Json.mkObj <|
  [("version", toJson version), ("ok", toJson true)] ++
  (source.toList.map fun s => ("lean_source", toJson s))

end VastitasKernel
