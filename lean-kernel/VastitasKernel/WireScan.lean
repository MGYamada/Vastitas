import Lean.Data.Json.Parser
import Std.Data.HashSet
import VastitasKernel.Limits

/-! A strict pre-scan of the raw request text, run before `Lean.Json.parse`.
`Json.parse` keeps the last of duplicate object keys and expands every number
exponent into a natural number, so neither property can be audited after
parsing. This scan grants no acceptance; it only rejects requests outside the
documented wire bounds, so that every such request receives `E_PROTOCOL`.
Object keys are decoded by the same string parser that `Json.parse` uses. -/
namespace VastitasKernel.WireScan
open Std.Internal.Parsec Std.Internal.Parsec.String

structure Bounds where
  /-- UTF-8 bytes of one request, `requestBytes` of the compiler limits. The
  frontend bounds the requests that it writes by the same value. -/
  bytes : Nat := Limits.requestBytes
  /-- Nested arrays and objects; actual requests stay below 200 levels. -/
  depth : Nat := 16384
  /-- Integer and fraction digits of one number; frontend numbers fit in 20. -/
  digits : Nat := 64
  /-- Digits of one exponent; the frontend never writes an exponent. -/
  exponentDigits : Nat := 2
  deriving Repr, Inhabited

private partial def digitRun (count : Nat) : Parser Nat := do
  if ← isEof then return count
  let c ← peek!
  if '0' ≤ c && c ≤ '9' then
    skip
    digitRun (count + 1)
  else return count

private def requireDigit : Parser Unit := do
  let c ← peek!
  unless '0' ≤ c && c ≤ '9' do fail "JSON number requires a digit"

/-- RFC 8259 number syntax with bounded digit counts. -/
private def number (bounds : Bounds) : Parser Unit := do
  if (← peek!) == '-' then skip
  requireDigit
  let whole ← if (← peek!) == '0' then do skip; pure 1 else digitRun 0
  let mut digits := whole
  if !(← isEof) && (← peek!) == '.' then
    skip
    requireDigit
    digits := digits + (← digitRun 0)
  if digits > bounds.digits then
    fail s!"JSON number exceeds {bounds.digits} significant digits"
  if !(← isEof) then
    let c ← peek!
    if c == 'e' || c == 'E' then
      skip
      let sign ← peek!
      if sign == '-' || sign == '+' then skip
      requireDigit
      if (← digitRun 0) > bounds.exponentDigits then
        fail s!"JSON number exponent exceeds {bounds.exponentDigits} digits"

mutual
  private partial def value (bounds : Bounds) (depth : Nat) : Parser Unit := do
    let c ← peek!
    if c == '{' then
      if depth ≥ bounds.depth then fail s!"JSON nesting exceeds {bounds.depth} levels"
      skip; ws
      if (← peek!) == '}' then skip
      else object bounds (depth + 1) {}
    else if c == '[' then
      if depth ≥ bounds.depth then fail s!"JSON nesting exceeds {bounds.depth} levels"
      skip; ws
      if (← peek!) == ']' then skip
      else array bounds (depth + 1)
    else if c == '"' then
      skip
      discard Lean.Json.Parser.str
    else if c == 't' then skipString "true"
    else if c == 'f' then skipString "false"
    else if c == 'n' then skipString "null"
    else if c == '-' || ('0' ≤ c && c ≤ '9') then number bounds
    else fail "unexpected JSON input"

  private partial def array (bounds : Bounds) (depth : Nat) : Parser Unit := do
    value bounds depth; ws
    let c ← any
    if c == ']' then return
    else if c == ',' then
      ws
      array bounds depth
    else fail "unexpected character in JSON array"

  private partial def object (bounds : Bounds) (depth : Nat) (seen : Std.HashSet String) : Parser Unit := do
    unless (← peek!) == '"' do fail "JSON object key must be a string"
    skip
    let key ← Lean.Json.Parser.str
    if seen.contains key then fail s!"duplicate JSON object key '{key}'"
    ws
    unless (← any) == ':' do fail "expected ':' after JSON object key"
    ws
    value bounds depth; ws
    let c ← any
    if c == '}' then return
    else if c == ',' then
      ws
      object bounds depth (seen.insert key)
    else fail "unexpected character in JSON object"
end

private def document (bounds : Bounds) : Parser Unit := do
  ws
  value bounds 0
  ws
  eof

/-- Reject a request outside the wire bounds before it is parsed. -/
def scan (input : String) (bounds : Bounds := {}) : Except String Unit :=
  if input.utf8ByteSize > bounds.bytes then
    .error s!"IR input exceeds {bounds.bytes} bytes"
  else match (document bounds).run input with
    | .ok () => .ok ()
    | .error message => .error s!"invalid IR JSON: {message}"

end VastitasKernel.WireScan
