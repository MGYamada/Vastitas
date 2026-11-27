import VastitasKernel.IndexedDeclarationProtocol

/-! Strict decoding into the rich source AST. The decoded body is untrusted:
the authority/Fn/dispatch composition must still audit every returned Core body. -/
namespace VastitasKernel.Indexed.Wire
open Lean JsonDecode

def namedPath (name : String) (span : Span) : Except String Source.Path := do
  let parts := name.splitOn "::"
  if parts.any String.isEmpty then throw "empty component in indexed reference"
  return ⟨parts, span⟩

def pureType (j : Json) : Except String Core.PureType := do
  match ← str j "kind" with
  | "named" =>
    fields j ["kind", "name"]
    match ← str j "name" with
    | "Nat" => return .nat
    | "Int" => return .int
    | "Bool" => return .bool
    | "Unit" => return .unit
    | _ => throw "expected a concrete scalar type"
  | "pair" =>
    fields j ["kind", "element"]
    match ← str j "element" with
    | "Nat" => return .pair .nat
    | "Int" => return .pair .int
    | _ => throw "Pair elements must be Nat or Int"
  | _ => throw "expected a scalar or homogeneous Pair type"

def typeArgument (j : Json) : Except String Source.TypeArgument := do
  match ← str j "kind" with
  | "name" => fields j ["kind", "reference"]; return .name (← path (← field j "reference"))
  | "natural" => fields j ["kind", "value"]; return .natural (← natural j)
  | _ => throw "unknown indexed type argument"

def legacyIndex (j : Json) : Except String RawIndex := do
  match ← str j "kind" with
  | "name" => fields j ["kind", "name"]; return .name (← str j "name")
  | "base" => fields j ["kind", "ring"]; return .base (← str j "ring")
  | _ => throw "unknown legacy geometry index"

def dataType (j : Json) : Except String Source.DataType := do
  match ← str j "kind" with
  | "named" =>
    fields j ["kind", "name"]
    let name ← str j "name"
    if name == "Scheme" || name == "CInfScheme" then return .legacy (.named name)
    return .pure (← pureType j)
  | "pair" => return .pure (← pureType j)
  | "point" =>
    fields j ["kind", "target", "source"]
    return .legacy (.point (← legacyIndex (← field j "target")) (← legacyIndex (← field j "source")))
  | "morphism" =>
    fields j ["kind", "source", "target"]
    return .legacy (.morphism (← legacyIndex (← field j "source")) (← legacyIndex (← field j "target")))
  | "pointed" =>
    fields j ["kind", "setting", "base"]
    return .legacy (.pointed (← str j "setting") (← str j "base"))
  | "indexed_object" =>
    fields j ["kind", "domain", "marker"]
    return .object ⟨← path (← field j "domain"), ← path (← field j "marker")⟩
  | "finite_hom" =>
    fields j ["kind", "category", "source", "target"]
    return .finiteHom (← path (← field j "category")) (← path (← field j "source"))
      (← path (← field j "target"))
  | "indexed_apply" =>
    fields j ["kind", "family", "arguments"]
    return .application (← path (← field j "family")) (← (← array j "arguments").mapM typeArgument)
  | _ => throw "expected an indexed object/application or pure data type"

/-- Decode source paths at every Hom leaf. Resolution needs the checked namespace
and the scope in which the signature was written. -/
def callableType : Nat → Json → Except String FunctionSource.SignatureSyntax
  | 0, _ => throw "IR type nesting exceeds the supported limit"
  | fuel + 1, j => do
    match ← str j "kind" with
    | "function" =>
      fields j ["kind", "params", "return_type"]
      return .function (← (← array j "params").mapM (callableType fuel))
        (← callableType fuel (← field j "return_type"))
    | "named" =>
      fields j ["kind", "name"]
      let name ← str j "name"
      if let .ok t := pureType j then return .data (.pure t)
      return .data (.legacy (.named name))
    | "finite_hom" | "pair" | "point" | "morphism" | "pointed" => return .data (← dataType j)
    | _ => throw "Fn signatures support scalars, finite Hom and recursive Fn types"

def fnType (j : Json) : Except String FunctionSource.FnType := do
  if (← str j "kind") == "function" then
    return .function (← callableType Limits.typeNesting j)
  return .data (← dataType j)

def fnParam (j : Json) : Except String FunctionSource.Param := do
  fields j ["name", "ty", "span"]
  return ⟨← str j "name", ← fnType (← field j "ty"), ← decodeSpan j⟩

def staticBinder (j : Json) : Except String FunctionSource.StaticBinder := do
  match ← str j "kind" with
  | "category" =>
    fields j ["kind", "name", "schema", "span"]
    return .category (← str j "name") (← path (← field j "schema")) (← decodeSpan j)
  | "object" =>
    fields j ["kind", "name", "category", "span"]
    return .object (← str j "name") (← str j "category") (← decodeSpan j)
  | "monad_object" =>
    fields j ["kind", "name", "monad", "span"]
    return .monadObject (← str j "name") (← str j "monad") (← decodeSpan j)
  | _ => throw "unknown finite function binder kind"

mutual
  def expression : Nat → Json → Except String FunctionSource.Expr
    | 0, _ => throw "IR nesting exceeds the supported limit"
    | fuel + 1, j => do
      let span ← decodeSpan j
      let common := ["kind", "span"]
      match ← str j "kind" with
      | "integer" => fields j (common ++ ["value"]); return .integer (← str j "value") span
      | "boolean" => fields j (common ++ ["value"]); return .boolean (← j.getObjValAs? Bool "value") span
      | "unit" => fields j common; return .unit span
      | "variable" =>
        fields j (common ++ ["name"])
        let name ← str j "name"
        let reference ← namedPath name span
        if reference.path.length == 1 then return .variable name span
        return .functionValue reference span
      | "call" =>
        fields j (common ++ ["callee", "args"])
        return .call (← namedPath (← str j "callee") span)
          (← (← array j "args").mapM (expression fuel)) span
      | "finite_lookup" =>
        fields j (common ++ ["table", "args"])
        let args ← array j "args"
        if args.length > FiniteTables.maxInputs then throw "finite lookup exceeds its arity limit"
        return .finiteLookup (← path (← field j "table")) (← args.mapM (expression fuel)) span
      | "finite_call" =>
        fields j (common ++ ["callee", "indices", "args"])
        let indices ← array j "indices"
        if indices.isEmpty then throw "an explicit finite call requires indices"
        return .finiteCall (← path (← field j "callee")) (← indices.mapM path)
          (← (← array j "args").mapM (expression fuel)) span
      | "invoke" =>
        fields j (common ++ ["callee", "args"])
        return .invoke (← expression fuel (← field j "callee"))
          (← (← array j "args").mapM (expression fuel)) span
      | "lambda" =>
        fields j (common ++ ["params", "return_type", "body"])
        return .lambda (← (← array j "params").mapM fnParam)
          (← fnType (← field j "return_type")) (← block fuel (← field j "body")) span
      | "unary" =>
        fields j (common ++ ["op", "operand"])
        return .unary (← str j "op") (← expression fuel (← field j "operand")) span
      | "binary" =>
        fields j (common ++ ["op", "left", "right"])
        return .binary (← str j "op") (← expression fuel (← field j "left"))
          (← expression fuel (← field j "right")) span
      | "if" =>
        fields j (common ++ ["condition", "then_branch", "else_branch"])
        return .branch (← expression fuel (← field j "condition"))
          (← block fuel (← field j "then_branch")) (← block fuel (← field j "else_branch")) span
      | "block" => fields j (common ++ ["body"]); return .block (← block fuel (← field j "body")) span
      | "indexed_pack" =>
        fields j (common ++ ["package", "witness", "fields"])
        return .pack (← dataType (← field j "package"))
          (← expression fuel (← field j "witness")) (← (← array j "fields").mapM (expression fuel)) span
      | "pack" =>
        fields j (common ++ ["scheme", "point"])
        return .pack .inferredPackage (← expression fuel (← field j "scheme"))
          [← expression fuel (← field j "point")] span
      | _ => throw "unknown indexed expression kind"
  def statement : Nat → Json → Except String FunctionSource.Stmt
    | 0, _ => throw "IR nesting exceeds the supported limit"
    | fuel + 1, j => do
      let span ← decodeSpan j
      match ← str j "kind" with
      | "let" =>
        fields j ["kind", "span", "name", "annotation", "value"]
        let annotation ← field j "annotation"
        let annotation ← if annotation.isNull then pure none else some <$> fnType annotation
        return .letE (← str j "name") annotation (← expression fuel (← field j "value")) span
      | "unpack_fields" =>
        fields j ["kind", "span", "value", "witness", "fields"]
        return .unpack (← expression fuel (← field j "value"))
          (← str j "witness") (← (← array j "fields").mapM Json.getStr?) span
      | "unpack" =>
        fields j ["kind", "span", "value", "scheme", "point"]
        return .unpack (← expression fuel (← field j "value"))
          (← str j "scheme") [← str j "point"] span
      | _ => throw "unknown indexed statement kind"
  def block : Nat → Json → Except String FunctionSource.Block
    | 0, _ => throw "IR nesting exceeds the supported limit"
    | fuel + 1, j => do
      fields j ["statements", "result", "span"]
      return .mk (← (← array j "statements").mapM (statement fuel))
        (← expression fuel (← field j "result")) (← decodeSpan j)
end

def function (j : Json) : Except String FunctionSource.Function := do
  fields j ["name", "finite_binders", "params", "return_type", "body", "span", "public"]
  return {
    name := ← str j "name", params := ← (← array j "params").mapM fnParam,
    result := ← fnType (← field j "return_type"), body := ← block Limits.sourceNesting (← field j "body"),
    isPublic := ← j.getObjValAs? Bool "public", span := ← decodeSpan j,
    finiteBinders := ← (← optionalArray j "finite_binders").mapM staticBinder }

def methodParam (j : Json) : Except String Surface.Param := do
  fields j ["name", "ty", "span"]
  let type ← field j "ty"
  fields type ["kind", "name"]
  if (← str type "kind") != "named" then throw "method selectors require finite scalar/abstract names"
  return ⟨← str j "name", .data (.named (← str type "name")), ← decodeSpan j⟩

def method (j : Json) : Except String DispatchSource.Method := do
  fields j ["name", "params", "return_type", "body", "span", "requires"]
  let span ← decodeSpan j
  return {
    target := ← namedPath (← str j "name") span,
    params := ← (← array j "params").mapM methodParam,
    result := ← pureType (← field j "return_type"),
    requirements := ← (← array j "requires").mapM Json.getStr?,
    body := ← block Limits.sourceNesting (← field j "body"), span }

def contribution (j : Json) : Except String DispatchSource.Contribution := do
  fields j ["name", "target", "methods", "span", "public"]
  let target ← segments j "target"
  let span ← decodeSpan j
  if target.isEmpty || target.any String.isEmpty then throw "empty contribution target"
  return {
    name := ← str j "name", target := ⟨target, span⟩,
    methods := ← (← array j "methods").mapM method,
    isPublic := ← j.getObjValAs? Bool "public", span }

end VastitasKernel.Indexed.Wire
