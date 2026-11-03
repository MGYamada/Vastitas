import VastitasKernel.WireScan
import VastitasKernel.JsonDecode
import VastitasKernel.StorageLayout
import VastitasKernel.Dispatch

/-! Kernel regressions for the v0.1.0-alpha review fixes (#535, #553, #562).
Each case runs the actual kernel definition; no separate model is tested. -/
namespace VastitasKernel.ReviewRegression
open Lean

private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"review regression failed: {name}")

private def scanRejects (input : String) (fragment : String) (bounds : WireScan.Bounds := {}) : Bool :=
  match WireScan.scan input bounds with
  | .ok () => false
  | .error message => (message.splitOn fragment).length > 1

private def scanAccepts (input : String) (bounds : WireScan.Bounds := {}) : Bool :=
  (WireScan.scan input bounds).isOk

-- #562.1: bounded numbers, nesting and size; the scan never builds a value.
#eval check "plain request" (scanAccepts "{\"version\":2,\"spans\":[0,1,-3,4.5,6e-2,7E+10]}")
#eval check "huge exponent" (scanRejects "{\"version\":1e1000000000}" "exponent exceeds")
#eval check "three-digit exponent" (scanRejects "{\"version\":1e400}" "exponent exceeds")
#eval check "two-digit exponent" (scanAccepts "{\"version\":1e99}")
#eval check "digit bound" (scanRejects ("[" ++ "".pushn '1' 65 ++ "]") "significant digits")
#eval check "digit bound boundary" (scanAccepts ("[" ++ "".pushn '1' 64 ++ "]"))
#eval check "fraction digits count" (scanRejects ("[1." ++ "".pushn '0' 64 ++ "]") "significant digits")
#eval check "nesting bound" (scanRejects ("".pushn '[' 9 ++ "".pushn ']' 9) "nesting exceeds" { depth := 8 })
#eval check "nesting boundary" (scanAccepts ("".pushn '[' 8 ++ "".pushn ']' 8) { depth := 8 })
#eval check "byte bound" (scanRejects "[1, 2]" "exceeds 4 bytes" { bytes := 4 })
#eval check "JSON grammar is unchanged" (scanRejects "[01]" "unexpected character")
#eval check "missing exponent digits" (scanRejects "[1e]" "requires a digit")
#eval check "trailing input" (scanRejects "{} {}" "expected end of input")

-- #562.2: duplicate keys are rejected after the parser's own string decoding.
#eval check "duplicate version" (scanRejects "{\"version\":2,\"version\":9}" "duplicate JSON object key 'version'")
#eval check "nested duplicate" (scanRejects "{\"a\":[{\"x\":1,\"x\":2}]}" "duplicate JSON object key 'x'")
#eval check "escaped duplicate" (scanRejects "{\"version\":2,\"ver\\u0073ion\":9}" "duplicate JSON object key")
#eval check "distinct sibling objects" (scanAccepts "[{\"x\":1},{\"x\":2}]")

-- #562.3: one digits-only decimal reader for literals and Gram entries.
#eval check "decimal natural" (decimalNat? "1000" == some 1000)
#eval check "natural rejects separators" (decimalNat? "1_000" == none)
#eval check "natural rejects empty" (decimalNat? "" == none)
#eval check "natural rejects sign" (decimalNat? "+1" == none)
#eval check "decimal integer" (decimalInt? "-10" == some (-10))
#eval check "integer rejects separators" (decimalInt? "-1_0" == none)
#eval check "integer rejects lone sign" (decimalInt? "-" == none)
#eval check "integer rejects double sign" (decimalInt? "--1" == none)

-- #562.4: wire path components are structured; `::` cannot be smuggled in.
private def pathJson (parts : List String) : Json := Json.mkObj [("path", toJson parts)]
#eval check "plain components" ((JsonDecode.segments (pathJson ["base", "choose"]) "path").toOption == some ["base", "choose"])
#eval check "joined component" (!(JsonDecode.segments (pathJson ["base::choose"]) "path").isOk)
#eval check "split colon components" (!(JsonDecode.segments (pathJson ["a:", ":b"]) "path").isOk)
#eval check "empty component" (!(JsonDecode.segments (pathJson ["a", ""]) "path").isOk)
#eval check "empty path is the caller's decision" ((JsonDecode.segments (pathJson []) "path").toOption == some [])

-- #535: the explainer reports the first failing conjunct with its numbers.
open Storage in
private def violation (capacity : Nat) (layout : Layout) : Option Layout.Violation :=
  layout.firstViolation .f64 capacity
open Storage in
#eval check "end byte" (violation 32 ⟨8, 2, 2, 2, false⟩ == some (.endByte 40 32 8))
open Storage in
#eval check "leading below rows" (violation 32 ⟨0, 2, 2, 1, false⟩ == some (.leadingBelowRows 1 2))
open Storage in
#eval check "alignment" (violation 32 ⟨4, 1, 1, 1, false⟩ == some (.alignment 4 8))
open Storage in
#eval check "empty view needs no alignment" (violation 32 ⟨4, 0, 1, 1, false⟩ == none)
open Storage in
#eval check "offset" (violation 32 ⟨40, 0, 0, 1, false⟩ == some (.offset 40 32))
open Storage in
#eval check "rows limit" (violation 32 ⟨0, 2^31, 0, 2^31, false⟩ == some (.rows (2^31)))
open Storage in
#eval check "columns limit" (violation 32 ⟨0, 1, 2^31, 1, false⟩ == some (.columns (2^31)))
open Storage in
#eval check "leading limit" (violation 32 ⟨0, 1, 1, 2^31, false⟩ == some (.leading (2^31)))
open Storage in
#eval check "capacity limit" (violation (2^63) ⟨0, 1, 1, 1, false⟩ == some (.capacity (2^63)))
open Storage in
#eval check "valid layout" (violation 32 ⟨0, 2, 2, 2, false⟩ == none)
open Storage in
#eval check "message names the numbers"
  (((violation 32 ⟨8, 2, 2, 2, false⟩).map Layout.Violation.message) ==
    some "view ends at byte 40, but the allocation has 32 bytes (4 elements of 8 bytes)")

-- #553: dispatch tables are charged before their quadratic steps.
open Dispatch in
private def tuples (choices : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => choices.flatMap fun s => (tuples choices n).map (s :: ·)
open Dispatch in
private def family (choices : List Nat) (k : Nat) : List Method :=
  (tuples choices k).zipIdx.map fun (selectors, id) => { id, selectors := selectors ++ List.replicate (6 - k) 5 }
open Dispatch in
private def code (result : Except Error Checked) : String :=
  match result with | .ok _ => "ok" | .error error => error.code
-- Measured positive: the 1296-method arity-6 family (7.0M table units,
-- 7.3M ranking units) is still accepted; 7776 methods exceed the table budget.
open Dispatch in
#eval check "large unambiguous family" (code (checkWith publicHierarchy 6 [] (family [0, 1, 2, 3, 4, 5] 4)) == "ok")
open Dispatch in
#eval check "oversized family" (code (checkWith publicHierarchy 6 [] (family [0, 1, 2, 3, 4, 5] 5)) == "E_DISPATCH_LIMIT")
open Dispatch in
#eval check "table work" (tableWork 4096 7776 > Limits.dispatchWork ∧ tableWork 4096 1296 ≤ Limits.dispatchWork)

end VastitasKernel.ReviewRegression
