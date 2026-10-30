import VastitasKernel.ResourceCodegen
import VastitasKernel.StorageFunctionProtocol
import VastitasKernel.IndexedProtocol

namespace VastitasKernel.ResourceSource.Wire
open Lean JsonDecode

private def size (j : Json) (key : String) : Except String Nat := do
  let value ← j.getObjValAs? Nat key
  if value ≥ 2^64 then throw "resource source integer exceeds 64 bits"
  return value

private def parameter (j : Json) : Except String Parameter := do
  let span ← decodeSpan j
  match ← str j "kind" with
  | "owned" =>
    fields j ["kind", "name", "type", "span"]
    return .owned (← str j "name") (← Storage.Functions.Wire.ownedType (← field j "type")) span
  | "borrowed" =>
    fields j ["kind", "name", "scalar", "rows", "columns", "access", "initializes", "span"]
    return .borrowed (← str j "name") (← Storage.Wire.scalar (← str j "scalar"))
      (← size j "rows") (← size j "columns") (← Storage.Wire.access (← str j "access"))
      (← j.getObjValAs? Bool "initializes") span
  | _ => throw "unknown resource source parameter kind"

private def action (j : Json) : Except String Action := do
  match ← str j "op" with
  | "allocate" =>
    fields j ["op", "owner", "scalar", "elements"]
    return .allocate (← str j "owner") (← Storage.Wire.scalar (← str j "scalar")) (← size j "elements")
  | "move" => fields j ["op", "source", "target"]; return .move (← str j "source") (← str j "target")
  | "drop" => fields j ["op", "owner"]; return .drop (← str j "owner")
  | "borrow" =>
    fields j ["op", "name", "source", "layout", "access"]
    return .borrow (← str j "name") (← str j "source") (← Storage.Wire.layout (← field j "layout"))
      (← Storage.Wire.access (← str j "access"))
  | "release" => fields j ["op", "loan"]; return .release (← str j "loan")
  | "transpose" => fields j ["op", "loan"]; return .transpose (← str j "loan")
  | "fill" =>
    fields j ["op", "loan", "value"]
    return .fill (← str j "loan") (← Storage.Wire.literal (← field j "value"))
  | "store" | "expect" =>
    fields j ["op", "loan", "row", "column", "value"]
    let operation := if (← str j "op") == "store" then Action.store else Action.expect
    return operation (← str j "loan") (← size j "row") (← size j "column")
      (← Storage.Wire.literal (← field j "value"))
  | "copy" => fields j ["op", "source", "target"]; return .copy (← str j "source") (← str j "target")
  | _ => throw "unknown resource source operation"

private def statements : Nat → List Json → Except String (List Statement)
  | _, [] => pure []
  | 0, _ :: _ => throw "resource source exceeds decoding depth bound"
  | fuel + 1, first :: rest => do
    let span ← decodeSpan first
    let statement ← match ← str first "kind" with
      | "action" =>
        fields first ["kind", "action", "span"]
        pure (.action (← action (← field first "action")) span)
      | "call" =>
        fields first ["kind", "callee", "arguments", "results", "span"]
        pure (.call (← Indexed.Wire.namedPath (← str first "callee") span)
          (← (← array first "arguments").mapM Json.getStr?)
          (← (← array first "results").mapM Json.getStr?) span)
      | "branch" =>
        fields first ["kind", "condition", "yes", "no", "span"]
        pure (.branch (← first.getObjValAs? Bool "condition")
          (← statements fuel (← array first "yes")) (← statements fuel (← array first "no")) span)
      | _ => throw "unknown resource source statement"
    return statement :: (← statements fuel rest)

def function (j : Json) : Except String Function := do
  fields j ["name", "parameters", "results", "body", "value_type", "value_body", "span", "public"]
  let results ← (← array j "results").mapM fun result => do
    fields result ["name", "type"]
    return (← str result "name", ← Storage.Functions.Wire.ownedType (← field result "type"))
  return {
    name := ← str j "name", parameters := ← (← array j "parameters").mapM parameter, results,
    body := ← statements 4096 (← array j "body"), valueType := ← Indexed.Wire.pureType (← field j "value_type"),
    valueBody := ← Indexed.Wire.block Limits.sourceNesting (← field j "value_body"),
    isPublic := ← j.getObjValAs? Bool "public", span := ← decodeSpan j }

private def without (j : Json) (key : String) : Except String Json := do
  return Json.mkObj ((← j.getObj?).toArray.toList.filter (·.1 != key))

def module (j : Json) : Except String Module := do
  let pureModule ← Indexed.Wire.module (← without j "resource_functions")
  return ⟨pureModule, ← (← optionalArray j "resource_functions").mapM function⟩

def package (j : Json) : Except String Package := do
  let modules ← (← array j "modules").mapM module
  -- Reuse the exact package metadata decoder, with no resource body projected
  -- into a pure function. Unknown metadata fields remain rejected.
  let stripped ← (← array j "modules").mapM (without · "resource_functions")
  let metadata := (← without j "modules").setObjVal! "modules" (toJson stripped)
  let pkg ← Indexed.Wire.package metadata
  return ⟨pkg.id, pkg.dependencies, modules, pkg.geometryCompat⟩

def program (j : Json) : Except String Program := do
  fields j ["version", "input", "file", "root", "packages"]
  if (← j.getObjValAs? Nat "version") != 8 then throw "expected protocol 8"
  if (← str j "input") != "package" then throw "protocol 8 requires package input"
  return ⟨← str j "file", ← str j "root", ← (← array j "packages").mapM package⟩

structure CheckedInput (json : Json) (requireMain : Bool) where
  input : Program
  decoded : program json = .ok input
  checked : Checked input requireMain
  accepted : ResourceSource.check input requireMain = .ok checked

def check (json : Json) (requireMain : Bool) : Except Diagnostic (CheckedInput json requireMain) :=
  match decoded : program json with
  | .error message => .error {code := "E_PROTOCOL", message}
  | .ok input => match accepted : ResourceSource.check input requireMain with
    | .error diagnostic => .error diagnostic
    | .ok checked => .ok ⟨input, decoded, checked, accepted⟩

end VastitasKernel.ResourceSource.Wire
