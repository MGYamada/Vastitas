import VastitasKernel.LegacySource
import VastitasKernel.IndexedAcceptance
import VastitasKernel.ResourceProtocol

/-! old-route(#533): the development-only Core parity check of #533, round 1
(W2), changed in round 2 (W6, W7). It is removed with the routes that it
compares at the cutover to epoch 10. No Lake library or executable contains
it, `Main` does not import it, and it grants no acceptance authority.

`tests/wire_parity.rs` writes request pairs: the request that the frontend
wrote for a corpus program before round 2 (protocols 2 to 6), or a wire
fixture of an older protocol, and the protocol-9 request of the same program.
This check decodes and checks both requests through the route of their
version, as `Main` does (`Indexed.LegacySource` for 2 to 6, `Indexed.Wire` for
7 and `ResourceSource.Wire` for 8 and 9), and compares the audit, executable
and reverse-compiled Core of the accepted requests by `reprStr`. Protocols 8
and 9 check the pure part of a request twice: as the pure program
(`pureProgram`, whose compiled Core code generation reads when there is no
resource entry) and with the pure fragments of the resource functions
(`values`). Protocols 2 to 7 check it once, and that Core stands for both. The
check compares the pure programs with each other and the passes with fragments
with each other. A protocol-9 request with `legacy_geometry` ends with the
compatibility profile that protocols 2 to 6 add, so the Core of a pair is the
same with it. A flat unit with observations of `show!` was a protocol-9
request without the profile; its Core is compared without the declarations
of the profile.

It also reports the namespace work that each accepted request is charged: the
price of its JSON (`Namespace.priceInput`, the `inputUnits` of its receipt)
and the namespace work of its passes, against `Limits.namespaceProgramWork`.

Run it after the Rust harness has written the pairs to `<directory>`:
`cd lean-kernel && lake env lean --run ../scripts/wire_parity.lean <directory>`
(`scripts/check_wire_parity.sh` runs both). -/
open Lean VastitasKernel

/-- The audit, executable and reverse-compiled Core of one check. -/
structure Passes where
  audit : Indexed.Core.Module
  executable : Indexed.Core.Module
  compiled : Indexed.Core.Module

/-- The package of the compatibility profile (`CompatibilityProfile.profilePackage`). -/
def profile : Namespace.PackageId := Indexed.CompatibilityProfile.profileId

/-- `m` without the declarations of the compatibility profile. -/
def withoutProfile (m : Indexed.Core.Module) : Indexed.Core.Module :=
  let declarations := m.declarations
  { m with declarations := { declarations with
      indexed := declarations.indexed.filter (·.id.scope.package != profile),
      packages := declarations.packages.filter (·.id.scope.package != profile),
      primitives := declarations.primitives.filter (·.id.scope.package != profile) } }

def Passes.withoutProfile (p : Passes) : Passes :=
  ⟨_root_.withoutProfile p.audit, _root_.withoutProfile p.executable, _root_.withoutProfile p.compiled⟩

/-- The namespace work that an accepted request is charged: the price of its
JSON and the work of its passes. -/
structure Budget where
  input : Nat
  passes : Nat

def Budget.total (b : Budget) : Nat := b.input + b.passes

/-- The passes of an accepted request, with the pure fragments of resource
functions and of the pure program, and its budget, or the code and message of
its rejection. Protocols 2 to 7 have one check, which stands for both. -/
def cores (json : Json) : Except String (Passes × Passes × Budget) := do
  let version ← (json.getObjValAs? Nat "version").mapError fun e => s!"no version: {e}"
  let failure (d : Diagnostic) := s!"{d.code}: {d.message}"
  if version == 8 || version == 9 then
    match ResourceSource.Wire.check json false with
    | .error d => throw (failure d)
    | .ok accepted =>
      let values := accepted.checked.values
      let program := accepted.checked.pureProgram
      return (⟨values.audit.core.module, values.executable.core.module, values.compiled.core.module⟩,
        ⟨program.audit.core.module, program.executable.core.module, program.compiled.core.module⟩,
        ⟨accepted.namespaceReceipt.inputUnits.val, ResourceSource.Wire.namespaceUnits accepted.checked⟩)
  else if version == 7 then
    match Indexed.Wire.check json false with
    | .error d => throw (failure d)
    | .ok accepted =>
      let c := accepted.checked
      let passes : Passes := ⟨c.audit.core.module, c.executable.core.module, c.compiled.core.module⟩
      return (passes, passes, ⟨accepted.namespaceReceipt.inputUnits.val, c.namespaceUnits⟩)
  else
    match Indexed.LegacySource.check json false with
    | .error d => throw (failure d)
    | .ok accepted =>
      let c := accepted.checked
      let passes : Passes := ⟨c.audit.core.module, c.executable.core.module, c.compiled.core.module⟩
      return (passes, passes, ⟨accepted.namespaceReceipt.inputUnits.val, c.namespaceUnits⟩)

/-- The passes in which `a` and `b` differ. -/
def differing (a b : Passes) : List String :=
  (if reprStr a.audit == reprStr b.audit then [] else ["audit"]) ++
  (if reprStr a.executable == reprStr b.executable then [] else ["executable"]) ++
  (if reprStr a.compiled == reprStr b.compiled then [] else ["compiled"])

/-- The first line of `text`, shortened. -/
private def short (text : String) : String :=
  let line := (text.splitOn "\n").headD ""
  if line.length > 160 then String.ofList (line.toList.take 160) ++ "…" else line

/-- Whether the Cores `a` of the original route and `b` of protocol 9 are the
same, or how they differ. A flat unit with observations of `show!` was a
protocol-9 request without the compatibility profile; with `legacy_geometry`
its Core also holds the declarations of the profile, which the comparison then
leaves out. -/
def describe (version : Nat) (a b : Passes) : String :=
  match differing a b with
  | [] => "same"
  | parts =>
    if version == 9 && (differing a.withoutProfile b.withoutProfile).isEmpty then
      "same without the profile declarations"
    else s!"differs: {", ".intercalate parts}"

/-- The verdict on the Core of one pair, and the budgets of both requests when
both are accepted. -/
def verdict (original current : Json) : String × Option (Budget × Budget) :=
  let version := (original.getObjValAs? Nat "version").toOption.getD 0
  match cores original, cores current with
  | .error a, .error b => (s!"both rejected ({short a} | {short b})", none)
  | .ok _, .error b => (s!"9 rejects: {short b}", none)
  | .error a, .ok _ => (s!"9 accepts what the original route rejects: {short a}", none)
  | .ok (a, aProgram, before), .ok (b, bProgram, after) =>
    let values := describe version a b
    let program := describe version aProgram bProgram
    (if values == program then values else s!"with fragments {values}; pure program {program}",
      some (before, after))

private def field (entry : Json) (key : String) : IO String :=
  match entry.getObjValAs? String key with
  | .ok value => pure value
  | .error message => throw (IO.userError s!"pairs.json: {key}: {message}")

private def readJson (path : System.FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok json => pure json
  | .error message => throw (IO.userError s!"{path}: {message}")

def main (args : List String) : IO UInt32 := do
  let [directory] := args
    | do
        IO.eprintln "usage: lean --run scripts/wire_parity.lean <directory>"
        return 2
  let directory : System.FilePath := directory
  let pairs ← match (← readJson (directory / "pairs.json")).getArr? with
    | .ok pairs => pure pairs
    | .error message => throw (IO.userError s!"pairs.json: {message}")
  let mut lines : Array String := #[]
  let mut kinds : Array String := #[]
  let mut budgets : Array (Budget × Budget) := #[]
  for entry in pairs do
    let name ← field entry "name"
    let from_ := (entry.getObjValAs? Nat "from").toOption.getD 0
    let original ← readJson (directory / (← field entry "original"))
    let current ← readJson (directory / (← field entry "current"))
    let (core, budget) := verdict original current
    let kind := (core.splitOn ":").headD core |>.splitOn " (" |>.headD core
    kinds := kinds.push s!"{from_}→9 core {kind}"
    let mut work := ""
    if let some (before, after) := budget then
      budgets := budgets.push (before, after)
      work := s!" | work: {before.input}+{before.passes}={before.total} → {after.input}+{after.passes}={after.total}"
    lines := lines.push s!"{name} | {from_}→9 | wire: {← field entry "wire"} | core: {core}{work}"
  IO.println "# Core parity of #533 round 2 (W6, W7): development-only"
  let mut counts : List (String × Nat) := []
  for key in kinds.qsort (· < ·) do
    counts := match counts with
      | (last, count) :: rest => if last == key then (last, count + 1) :: rest else (key, 1) :: counts
      | [] => [(key, 1)]
  for (key, count) in counts.reverse do
    IO.println s!"# {count} {key}"
  let largest := budgets.foldl (fun m (before, after) => max m (max before.total after.total)) 0
  let increase := budgets.foldl (fun m (before, after) => max m (after.total - before.total)) 0
  let decrease := budgets.foldl (fun m (before, after) => max m (before.total - after.total)) 0
  IO.println s!"# namespace work of {budgets.size} accepted pairs: largest {largest} of {Limits.namespaceProgramWork}, largest increase {increase}, largest decrease {decrease}"
  for line in lines do IO.println line
  IO.FS.writeFile (directory / "core.txt") ("\n".intercalate lines.toList ++ "\n")
  return 0
