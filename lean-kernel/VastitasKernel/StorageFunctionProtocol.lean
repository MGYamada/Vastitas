import VastitasKernel.StorageFunctions
import VastitasKernel.StorageProtocol

/-! Strict Rust/Lean component schema. Not a public protocol entry point. -/
namespace VastitasKernel.Storage.Functions.Wire
open Lean JsonDecode

private def unsigned (bits : Nat) (j : Json) : Except String Nat := do
  let value ← fromJson? j
  if value ≥ 2^bits then throw s!"resource function integer exceeds {bits} bits"
  return value

private def symbol (j : Json) (name : String) : Except String Nat := do unsigned 32 (← field j name)
private def size (j : Json) (name : String) : Except String Nat := do unsigned 64 (← field j name)

def ownedType (j : Json) : Except String OwnedType := do
  fields j ["scalar", "elements", "initialized"]
  return ⟨← Storage.Wire.scalar (← str j "scalar"), ← size j "elements",
    ← (← array j "initialized").mapM Storage.Wire.layout⟩

def parameter (j : Json) : Except String Parameter := do
  match ← str j "kind" with
  | "owned" =>
    fields j ["kind", "name", "type"]
    return .owned (← symbol j "name") (← ownedType (← field j "type"))
  | "borrowed" =>
    fields j ["kind", "name", "scalar", "rows", "columns", "access", "initializes"]
    return .borrowed (← symbol j "name") (← Storage.Wire.scalar (← str j "scalar"))
      (← size j "rows") (← size j "columns") (← Storage.Wire.access (← str j "access"))
      (← j.getObjValAs? Bool "initializes")
  | _ => throw "resource parameters must be owned or borrowed"

def result (j : Json) : Except String (Symbol × OwnedType) := do
  fields j ["name", "type"]
  return (← symbol j "name", ← ownedType (← field j "type"))

def statements : Nat → List Json → Except String (List Statement)
  | _, [] => pure []
  | 0, _ :: _ => throw "resource function exceeds the decoding depth bound"
  | fuel + 1, first :: rest => do
    let statement ← match ← str first "kind" with
      | "action" => do
        fields first ["kind", "action"]
        pure (.action (← Storage.Wire.action (← field first "action")))
      | "call" => do
        fields first ["kind", "callee", "arguments", "results"]
        pure (.call (← symbol first "callee")
          (← (← array first "arguments").mapM (unsigned 32))
          (← (← array first "results").mapM (unsigned 32)))
      | "branch" => do
        fields first ["kind", "condition", "yes", "no"]
        pure (.branch (← first.getObjValAs? Bool "condition")
          (← statements fuel (← array first "yes")) (← statements fuel (← array first "no")))
      | _ => throw "unknown resource function statement"
    return statement :: (← statements fuel rest)

def function (j : Json) : Except String Function := do
  fields j ["id", "parameters", "results", "body"]
  return ⟨← symbol j "id", ← (← array j "parameters").mapM parameter,
    ← (← array j "results").mapM result, ← statements 4096 (← array j "body")⟩

def program (j : Json) : Except String Program := do
  fields j ["functions", "entry"]
  return ⟨← (← array j "functions").mapM function, ← symbol j "entry"⟩

structure CheckedInput (json : Json) where
  input : Program
  decoded : program json = .ok input
  checked : Checked input
  accepted : Functions.check input = .ok checked

def check (json : Json) : Except Error (CheckedInput json) :=
  match decoded : program json with
  | .error message => .error ⟨"E_PROTOCOL", message⟩
  | .ok input => match accepted : Functions.check input with
    | .error diagnostic => .error diagnostic
    | .ok checked => .ok ⟨input, decoded, checked, accepted⟩

end VastitasKernel.Storage.Functions.Wire
