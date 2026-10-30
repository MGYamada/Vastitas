import VastitasKernel.Surface
import VastitasKernel.Protocol
import VastitasKernel.JsonDecode

namespace VastitasKernel
open Lean JsonDecode

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
    | "pair" => pure (.data (.pair (← str j "element")))
    | "point" => pure (.data (.point (← decodeIndex (← field j "target")) (← decodeIndex (← field j "source"))))
    | "morphism" => pure (.data (.morphism (← decodeIndex (← field j "source")) (← decodeIndex (← field j "target"))))
    | "pointed" => pure (.data (.pointed (← str j "setting") (← str j "base")))
    | k => throw s!"unknown type kind '{k}'"

private def decodeParam (j : Json) : Except String Surface.Param := do
  pure { name := ← str j "name", ty := ← decodeType Limits.typeNesting (← field j "ty"), span := ← decodeSpan j }

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
          (← decodeType Limits.typeNesting (← field j "return_type")) (← decodeBlock fuel (← field j "body")) s)
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
        let annotation ← if annotation == Json.null then pure none else some <$> decodeType Limits.typeNesting annotation
        pure (.letE (← str j "name") annotation (← decodeExpr fuel (← field j "value")) s)
      | "unpack" => pure (.unpack (← decodeExpr fuel (← field j "value")) (← str j "scheme") (← str j "point") s)
      | k => throw s!"unknown statement kind '{k}'"
  private def decodeBlock : Nat → Json → Except String Surface.Block
    | 0, _ => throw "IR nesting exceeds the supported limit"
    | fuel + 1, j => do
      pure (.mk (← (← array j "statements").mapM (decodeStmt fuel))
        (← decodeExpr fuel (← field j "result")) (← decodeSpan j))
end

def decodeSurfaceFunction (j : Json) : Except String Surface.Function := do
  let name ← str j "name"
  let params ← (← array j "params").mapM decodeParam
  let result ← decodeType Limits.typeNesting (← field j "return_type")
  let body ← decodeBlock Limits.sourceNesting (← field j "body")
  let span ← decodeSpan j
  pure { name, params, result, body, span }

def decodeSurfaceGeneric (j : Json) : Except String RawGeneric := do
  let params ← (← array j "params").mapM fun param => do
    pure { name := ← str param "name", span := ← decodeSpan param : RawGenericParam }
  let domain ← (← array j "domain").mapM fun key => do
    (← key.getArr?).toList.mapM fun ty => do
      let .data raw ← decodeType Limits.typeNesting ty | throw "dispatch domains require scalar types"
      pure raw
  pure { name := ← str j "name", params, domain, span := ← decodeSpan j }

def decodeSurfaceMethod (j : Json) : Except String Surface.Method := do
  pure {
    name := ← str j "name"
    params := ← (← array j "params").mapM decodeParam
    result := ← decodeType Limits.typeNesting (← field j "return_type")
    requirements := ← (← array j "requires").mapM Json.getStr?
    body := ← decodeBlock Limits.sourceNesting (← field j "body")
    span := ← decodeSpan j }

def decodeTypePath (j : Json) : Except String TypePath := do
  fields j ["path", "span"]
  let path ← (← array j "path").mapM Json.getStr?
  if path.isEmpty || path.any String.isEmpty then throw "empty type path"
  return { path, span := ← decodeSpan j }

def decodeAbstractType (j : Json) : Except String RawAbstractType := do
  return {
    name := ← str j "name", parents := ← (← array j "parents").mapM decodeTypePath,
    span := ← decodeSpan j }

def decodeSubtype (j : Json) : Except String RawSubtype := do
  fields j ["scalar", "target", "span"]
  return { scalar := ← str j "scalar", target := ← decodeTypePath (← field j "target"), span := ← decodeSpan j }

def decodeAbstractMethod (j : Json) : Except String RawAbstractMethod := do
  fields j ["name", "params", "return_type", "requires", "domain", "span"]
  let params ← (← array j "params").mapM fun param => do
    let decoded ← decodeParam param
    let .data ty := decoded.ty | throw "abstract method selectors cannot be function types"
    pure { name := decoded.name, ty, span := decoded.span : RawParam }
  let .data returnType ← decodeType Limits.typeNesting (← field j "return_type")
    | throw "abstract method results cannot be function types"
  let domain ← (← array j "domain").mapM fun clause => do
    (← clause.getArr?).toList.mapM decodeTypePath
  return {
    name := ← str j "name", params, returnType
    requirements := ← (← array j "requires").mapM Json.getStr?, domain, span := ← decodeSpan j }

def decodeSurfaceModule (j : Json) : Except String Surface.Program := do
  let version ← j.getObjValAs? Nat "version"
  if version != 2 && version != 4 then throw s!"unsupported IR protocol version {version}; expected 2 or 4"
  if version == 4 then
    fields j ["version", "file", "functions", "generics", "methods", "input", "abstract_types", "subtypes", "abstract_methods"]
    if (← str j "input") != "flat" then throw "protocol 4 input must be flat"
  else
    -- Preserve v2's treatment of unrelated, untrusted hint metadata, but never
    -- silently erase declarations from a downgraded protocol-4 request.
    for key in ["input", "abstract_types", "subtypes", "abstract_methods"] do
      if (j.getObjVal? key).isOk then throw "abstract declarations require protocol 4"
    for key in ["grants", "contributions", "assembly", "delegations", "transfers", "packages", "root", "indexed_declarations", "geometry_compat"] do
      if (j.getObjVal? key).isOk then throw "package and authority declarations require their package protocol"
    if (j.getObjVal? "resources").isOk then throw "resource plans are not supported by protocol 2"
    if (j.getObjVal? "resource_functions").isOk then throw "resource functions require package protocol 8"
  let abstractTypes ← (← optionalArray j "abstract_types").mapM fun t => do
    fields t ["name", "parents", "span"]
    decodeAbstractType t
  let subtypes ← (← optionalArray j "subtypes").mapM decodeSubtype
  pure {
    version
    file := ← str j "file"
    functions := ← (← array j "functions").mapM decodeSurfaceFunction
    generics := ← (← array j "generics").mapM decodeSurfaceGeneric
    methods := ← (← array j "methods").mapM decodeSurfaceMethod
    abstractTypes, subtypes, abstractMethods := ← (← optionalArray j "abstract_methods").mapM decodeAbstractMethod }


end VastitasKernel
