import Lean.Data.Json
import VastitasKernel.Program

namespace VastitasKernel
open Lean

def spanJson (s : Span) : Json := Json.mkObj [
  ("start", toJson s.start), ("end", toJson s.end),
  ("line", toJson s.line), ("column", toJson s.column)]

def diagnosticJson (d : Diagnostic) : Json := Json.mkObj [
  ("code", toJson d.code), ("message", toJson d.message), ("span", spanJson d.span),
  ("notes", toJson (d.notes.map fun note => Json.mkObj [
    ("message", toJson note.message), ("span", spanJson note.span)]))]

def failureJson (d : Diagnostic) (version : Nat := 2) : Json := Json.mkObj [
  ("version", toJson version), ("ok", toJson false),
  ("diagnostics", toJson [diagnosticJson d])]

def successJson (source : Option String := none) (version : Nat := 2) : Json := Json.mkObj <|
  [("version", toJson version), ("ok", toJson true)] ++
  (source.toList.map fun s => ("lean_source", toJson s))

end VastitasKernel
