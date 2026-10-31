import VastitasKernel.Storage
import VastitasKernel.JsonDecode

/-! Untrusted resource-plan component schema shared with Rust `storage.rs`.
This decoder is not an alternative public wire version. Protocol 8 must compose
it with actual package/function acceptance and checked native generation. -/
namespace VastitasKernel.Storage.Wire
open Lean JsonDecode

private def boundedNat (j : Json) (name : String) (bits : Nat) : Except String Nat := do
  let value ← j.getObjValAs? Nat name
  if value ≥ 2^bits then throw s!"resource field '{name}' exceeds its {bits}-bit unsigned input representation"
  pure value

private def symbol (j : Json) (name : String) : Except String Symbol := boundedNat j name 32
private def size (j : Json) (name : String) : Except String Nat := boundedNat j name 64

def scalar (value : String) : Except String Scalar := match value with
  | "f64" => pure .f64 | "complex_f64" => pure .complexF64
  | _ => throw "unsupported resource scalar representation"

def access (value : String) : Except String Access := match value with
  | "read" => pure .read | "write" => pure .write | "read_write" => pure .readWrite
  | _ => throw "unsupported resource access mode"

def layout (j : Json) : Except String Layout := do
  fields j ["offset", "rows", "columns", "leading", "transposed"]
  return ⟨← size j "offset", ← size j "rows", ← size j "columns", ← size j "leading",
    ← j.getObjValAs? Bool "transposed"⟩

def source (j : Json) : Except String Source := do
  fields j ["kind", "name"]
  match ← str j "kind" with
  | "owner" => return .owner (← symbol j "name")
  | "loan" => return .loan (← symbol j "name")
  | _ => throw "resource source must name an owner or a loan"

def literal (j : Json) : Except String Literal := do
  match ← str j "kind" with
  | "f64" =>
    fields j ["kind", "bits"]
    return .f64 (UInt64.ofNat (← size j "bits"))
  | "complex_f64" =>
    fields j ["kind", "real", "imaginary"]
    return .complexF64 (UInt64.ofNat (← size j "real")) (UInt64.ofNat (← size j "imaginary"))
  | _ => throw "invalid resource literal representation"

def gemmMode (value : String) : Except String GemmMode := match value with
  | "overwrite" => pure .overwrite | "accumulate" => pure .accumulate
  | _ => throw "unsupported GEMM output mode"

def coefficient (j : Json) : Except String Coefficient := do
  match ← str j "kind" with
  | "literal" => fields j ["kind", "value"]; return .literal (← literal (← field j "value"))
  | "loan" => fields j ["kind", "loan"]; return .loan (← symbol j "loan")
  | _ => throw "unknown coefficient operand kind"

def optionalCoefficient (j : Json) (name : String) : Except String (Option Coefficient) :=
  match j.getObjVal? name with
  | .error _ => pure none
  | .ok value => some <$> coefficient value

def numericalPolicy (value : String) : Except String NumericalPolicy := match value with
  | "native_fast" => pure .nativeFast
  | _ => throw "unsupported numerical policy"

def action (j : Json) : Except String Action := do
  match ← str j "op" with
  | "allocate" =>
    fields j ["op", "owner", "scalar", "elements"]
    return .allocate (← symbol j "owner") (← scalar (← str j "scalar")) (← size j "elements")
  | "move" =>
    fields j ["op", "source", "target"]
    return .move (← symbol j "source") (← symbol j "target")
  | "drop" =>
    fields j ["op", "owner"]
    return .drop (← symbol j "owner")
  | "borrow" =>
    fields j ["op", "name", "source", "layout", "access"]
    return .borrow (← symbol j "name") (← source (← field j "source"))
      (← layout (← field j "layout")) (← access (← str j "access"))
  | "release" =>
    fields j ["op", "loan"]
    return .release (← symbol j "loan")
  | "transpose" =>
    fields j ["op", "loan"]
    return .transpose (← symbol j "loan")
  | "fill" =>
    fields j ["op", "loan", "value"]
    return .fill (← symbol j "loan") (← literal (← field j "value"))
  | "store" =>
    fields j ["op", "loan", "row", "column", "value"]
    return .store (← symbol j "loan") (← size j "row") (← size j "column") (← literal (← field j "value"))
  | "expect" =>
    fields j ["op", "loan", "row", "column", "value"]
    return .expect (← symbol j "loan") (← size j "row") (← size j "column") (← literal (← field j "value"))
  | "copy" =>
    fields j ["op", "source", "target"]
    return .copy (← symbol j "source") (← symbol j "target")
  | "gemm" =>
    fields j ["op", "left", "right", "output", "conjugate_left", "conjugate_right", "mode", "policy", "alpha", "beta"]
    return .gemm ⟨← symbol j "left", ← symbol j "right", ← symbol j "output",
      ← j.getObjValAs? Bool "conjugate_left", ← j.getObjValAs? Bool "conjugate_right",
      ← gemmMode (← str j "mode"), ← numericalPolicy (← str j "policy"),
      ← optionalCoefficient j "alpha", ← optionalCoefficient j "beta"⟩
  | _ => throw "unknown resource operation"

def statements : Nat → List Json → Except String (List Statement)
  | _, [] => pure []
  | 0, _ :: _ => throw "resource plan exceeds the decoding traversal bound"
  | fuel + 1, first :: rest => do
    let statement ← match ← str first "kind" with
      | "action" => do
        fields first ["kind", "action"]
        pure (.action (← action (← field first "action")))
      | "branch" => do
        fields first ["kind", "condition", "yes", "no"]
        pure (.branch (← first.getObjValAs? Bool "condition")
          (← statements fuel (← array first "yes")) (← statements fuel (← array first "no")))
      | _ => throw "unknown resource statement"
    return statement :: (← statements fuel rest)

def plan (j : Json) : Except String (List Statement) := do
  fields j ["statements"]
  statements 4096 (← array j "statements")

structure CheckedInput (json : Json) where
  input : List Statement
  decoded : plan json = .ok input
  checked : CheckedPlan input
  accepted : checkPlan input = .ok checked

def check (json : Json) : Except Error (CheckedInput json) :=
  match decoded : plan json with
  | .error message => .error ⟨"E_PROTOCOL", message⟩
  | .ok input => match accepted : checkPlan input with
    | .error diagnostic => .error diagnostic
    | .ok checked => .ok ⟨input, decoded, checked, accepted⟩

end VastitasKernel.Storage.Wire
