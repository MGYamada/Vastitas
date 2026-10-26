import Lean.Data.Json
import VastitasKernel.Program

namespace VastitasKernel
open Lean

private def str (j : Json) (key : String) : Except String String :=
  j.getObjValAs? String key

private def field (j : Json) (key : String) : Except String Json :=
  j.getObjVal? key

private def array (j : Json) (key : String) : Except String (List Json) := do
  pure (← (← field j key).getArr?).toList

private def decodeSpan (j : Json) : Except String Span := do
  let s ← field j "span"
  let start ← s.getObjValAs? Nat "start"
  let finish ← s.getObjValAs? Nat "end"
  let line ← s.getObjValAs? Nat "line"
  let column ← s.getObjValAs? Nat "column"
  if start > finish || line == 0 || column == 0 then
    throw "invalid source span"
  pure { start, «end» := finish, line, column }

private def decodeIndex (j : Json) : Except String RawIndex := do
  match ← str j "kind" with
  | "name" => pure (.name (← str j "name"))
  | "base" => pure (.base (← str j "ring"))
  | k => throw s!"unknown index kind '{k}'"

private def decodeType (j : Json) : Except String RawType := do
  match ← str j "kind" with
  | "named" => pure (.named (← str j "name"))
  | "point" => pure (.point (← decodeIndex (← field j "target")) (← decodeIndex (← field j "source")))
  | "morphism" => pure (.morphism (← decodeIndex (← field j "source")) (← decodeIndex (← field j "target")))
  | "pointed" => pure (.pointed (← str j "setting") (← str j "base"))
  | k => throw s!"unknown type kind '{k}'"

mutual
  private def decodeExpr : Nat → Json → Except String RawExpr
    | 0, _ => throw "IR nesting exceeds the supported limit"
    | fuel + 1, j => do
      let s ← decodeSpan j
      match ← str j "kind" with
      | "integer" => pure (.integer (← str j "value") s)
      | "boolean" => pure (.boolean (← j.getObjValAs? Bool "value") s)
      | "unit" => pure (.unit s)
      | "variable" => pure (.variable (← str j "name") s)
      | "call" => pure (.call (← str j "callee") (← (← array j "args").mapM (decodeExpr fuel)) s)
      | "unary" => pure (.unary (← str j "op") (← decodeExpr fuel (← field j "operand")) s)
      | "binary" => pure (.binary (← str j "op") (← decodeExpr fuel (← field j "left"))
          (← decodeExpr fuel (← field j "right")) s)
      | "if" => pure (.ite (← decodeExpr fuel (← field j "condition"))
          (← decodeBlock fuel (← field j "then_branch")) (← decodeBlock fuel (← field j "else_branch")) s)
      | "block" => pure (.block (← decodeBlock fuel (← field j "body")) s)
      | "pack" => pure (.pack (← decodeExpr fuel (← field j "scheme")) (← decodeExpr fuel (← field j "point")) s)
      | k => throw s!"unknown expression kind '{k}'"
  private def decodeStmt : Nat → Json → Except String RawStmt
    | 0, _ => throw "IR nesting exceeds the supported limit"
    | fuel + 1, j => do
      let s ← decodeSpan j
      match ← str j "kind" with
      | "let" =>
        let annotation ← field j "annotation"
        let annotation ← if annotation == Json.null then pure none else some <$> decodeType annotation
        pure (.letE (← str j "name") annotation (← decodeExpr fuel (← field j "value")) s)
      | "unpack" => pure (.unpack (← decodeExpr fuel (← field j "value")) (← str j "scheme") (← str j "point") s)
      | k => throw s!"unknown statement kind '{k}'"
  private def decodeBlock : Nat → Json → Except String RawBlock
    | 0, _ => throw "IR nesting exceeds the supported limit"
    | fuel + 1, j => do
      pure (.mk (← (← array j "statements").mapM (decodeStmt fuel))
        (← decodeExpr fuel (← field j "result")) (← decodeSpan j))
end

private def decodeParam (j : Json) : Except String RawParam := do
  pure { name := ← str j "name", ty := ← decodeType (← field j "ty"), span := ← decodeSpan j }

private def decodeFunction (j : Json) : Except String RawFunction := do
  let name ← str j "name"
  let params ← (← array j "params").mapM decodeParam
  let returnType ← decodeType (← field j "return_type")
  let body ← decodeBlock 512 (← field j "body")
  let span ← decodeSpan j
  pure { name, params, returnType, body, span }

private def decodeGeneric (j : Json) : Except String RawGeneric := do
  let params ← (← array j "params").mapM fun param => do
    pure { name := ← str param "name", span := ← decodeSpan param : RawGenericParam }
  let domain ← (← array j "domain").mapM fun key => do
    (← key.getArr?).toList.mapM decodeType
  pure { name := ← str j "name", params, domain, span := ← decodeSpan j }

private def decodeMethod (j : Json) : Except String RawMethod := do
  pure {
    name := ← str j "name"
    params := ← (← array j "params").mapM decodeParam
    returnType := ← decodeType (← field j "return_type")
    requirements := ← (← array j "requires").mapM Json.getStr?
    body := ← decodeBlock 512 (← field j "body")
    span := ← decodeSpan j }

def decodeModule (j : Json) : Except String RawProgram := do
  let version ← j.getObjValAs? Nat "version"
  if version != 2 then throw s!"unsupported IR protocol version {version}; expected 2"
  pure {
    version
    file := ← str j "file"
    functions := ← (← array j "functions").mapM decodeFunction
    generics := ← (← array j "generics").mapM decodeGeneric
    methods := ← (← array j "methods").mapM decodeMethod }

def spanJson (s : Span) : Json := Json.mkObj [
  ("start", toJson s.start), ("end", toJson s.end),
  ("line", toJson s.line), ("column", toJson s.column)]

def diagnosticJson (d : Diagnostic) : Json := Json.mkObj [
  ("code", toJson d.code), ("message", toJson d.message), ("span", spanJson d.span),
  ("notes", toJson (d.notes.map fun note => Json.mkObj [
    ("message", toJson note.message), ("span", spanJson note.span)]))]

def failureJson (d : Diagnostic) : Json := Json.mkObj [
  ("version", toJson (2 : Nat)), ("ok", toJson false),
  ("diagnostics", toJson [diagnosticJson d])]

def successJson (source : Option String := none) : Json := Json.mkObj <|
  [("version", toJson (2 : Nat)), ("ok", toJson true)] ++
  (source.toList.map fun s => ("lean_source", toJson s))

end VastitasKernel
