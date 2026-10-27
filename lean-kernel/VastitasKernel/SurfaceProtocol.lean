import VastitasKernel.Surface
import VastitasKernel.Protocol

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

private def decodeType : Nat → Json → Except String Surface.TypeExpr
  | 0, _ => throw "IR type nesting exceeds the supported limit"
  | fuel + 1, j => do
    match ← str j "kind" with
    | "function" => pure (.function (← (← array j "params").mapM (decodeType fuel))
        (← decodeType fuel (← field j "return_type")))
    | "named" => pure (.data (.named (← str j "name")))
    | "point" => pure (.data (.point (← decodeIndex (← field j "target")) (← decodeIndex (← field j "source"))))
    | "morphism" => pure (.data (.morphism (← decodeIndex (← field j "source")) (← decodeIndex (← field j "target"))))
    | "pointed" => pure (.data (.pointed (← str j "setting") (← str j "base")))
    | k => throw s!"unknown type kind '{k}'"

private def decodeParam (j : Json) : Except String Surface.Param := do
  pure { name := ← str j "name", ty := ← decodeType 64 (← field j "ty"), span := ← decodeSpan j }

mutual
  private def decodeExpr : Nat → Json → Except String Surface.Expr
    | 0, _ => throw "IR nesting exceeds the supported limit"
    | fuel + 1, j => do
      let s ← decodeSpan j
      match ← str j "kind" with
      | "integer" => pure (.integer (← str j "value") s)
      | "boolean" => pure (.boolean (← j.getObjValAs? Bool "value") s)
      | "unit" => pure (.unit s)
      | "variable" => pure (.variable (← str j "name") s)
      | "call" => pure (.call (← str j "callee") (← (← array j "args").mapM (decodeExpr fuel)) s)
      | "invoke" => pure (.invoke (← decodeExpr fuel (← field j "callee"))
          (← (← array j "args").mapM (decodeExpr fuel)) s)
      | "lambda" => pure (.lambda (← (← array j "params").mapM decodeParam)
          (← decodeType 64 (← field j "return_type")) (← decodeBlock fuel (← field j "body")) s)
      | "unary" => pure (.unary (← str j "op") (← decodeExpr fuel (← field j "operand")) s)
      | "binary" => pure (.binary (← str j "op") (← decodeExpr fuel (← field j "left"))
          (← decodeExpr fuel (← field j "right")) s)
      | "if" => pure (.ite (← decodeExpr fuel (← field j "condition"))
          (← decodeBlock fuel (← field j "then_branch")) (← decodeBlock fuel (← field j "else_branch")) s)
      | "block" => pure (.block (← decodeBlock fuel (← field j "body")) s)
      | "pack" => pure (.pack (← decodeExpr fuel (← field j "scheme")) (← decodeExpr fuel (← field j "point")) s)
      | k => throw s!"unknown expression kind '{k}'"
  private def decodeStmt : Nat → Json → Except String Surface.Stmt
    | 0, _ => throw "IR nesting exceeds the supported limit"
    | fuel + 1, j => do
      let s ← decodeSpan j
      match ← str j "kind" with
      | "let" =>
        let annotation ← field j "annotation"
        let annotation ← if annotation == Json.null then pure none else some <$> decodeType 64 annotation
        pure (.letE (← str j "name") annotation (← decodeExpr fuel (← field j "value")) s)
      | "unpack" => pure (.unpack (← decodeExpr fuel (← field j "value")) (← str j "scheme") (← str j "point") s)
      | k => throw s!"unknown statement kind '{k}'"
  private def decodeBlock : Nat → Json → Except String Surface.Block
    | 0, _ => throw "IR nesting exceeds the supported limit"
    | fuel + 1, j => do
      pure (.mk (← (← array j "statements").mapM (decodeStmt fuel))
        (← decodeExpr fuel (← field j "result")) (← decodeSpan j))
end

private def decodeFunction (j : Json) : Except String Surface.Function := do
  let name ← str j "name"
  let params ← (← array j "params").mapM decodeParam
  let result ← decodeType 64 (← field j "return_type")
  let body ← decodeBlock 512 (← field j "body")
  let span ← decodeSpan j
  pure { name, params, result, body, span }

private def decodeGeneric (j : Json) : Except String RawGeneric := do
  let params ← (← array j "params").mapM fun param => do
    pure { name := ← str param "name", span := ← decodeSpan param : RawGenericParam }
  let domain ← (← array j "domain").mapM fun key => do
    (← key.getArr?).toList.mapM fun ty => do
      let .data raw ← decodeType 64 ty | throw "dispatch domains require scalar types"
      pure raw
  pure { name := ← str j "name", params, domain, span := ← decodeSpan j }

private def decodeMethod (j : Json) : Except String Surface.Method := do
  pure {
    name := ← str j "name"
    params := ← (← array j "params").mapM decodeParam
    result := ← decodeType 64 (← field j "return_type")
    requirements := ← (← array j "requires").mapM Json.getStr?
    body := ← decodeBlock 512 (← field j "body")
    span := ← decodeSpan j }

def decodeSurfaceModule (j : Json) : Except String Surface.Program := do
  let version ← j.getObjValAs? Nat "version"
  if version != 2 then throw s!"unsupported IR protocol version {version}; expected 2"
  pure {
    version
    file := ← str j "file"
    functions := ← (← array j "functions").mapM decodeFunction
    generics := ← (← array j "generics").mapM decodeGeneric
    methods := ← (← array j "methods").mapM decodeMethod }


end VastitasKernel
