import VastitasKernel.LegacySource
import VastitasKernel.IndexedAcceptance
import VastitasKernel.ResourceProtocol

/-! old-route(#533): the development-only Core parity check of #533, round 1
(W2). It is removed with the routes that it compares at the cutover to epoch
10. No Lake library or executable contains it, `Main` does not import it, and
it grants no acceptance authority.

`tests/wire_parity.rs` writes request pairs: the request of a corpus program
at the protocol that the frontend selects, and its protocol-9 encoding. This
check decodes and checks both requests through the route of their version, as
`Main` does (`Indexed.LegacySource` for 2 to 6, `Indexed.Wire` for 7 and
`ResourceSource.Wire` for 8 and 9), and compares the audit, executable and
reverse-compiled Core of the accepted requests by `reprStr`. Protocols 8 and 9
check the pure part of a request twice: as the pure program (`pureProgram`,
whose compiled Core code generation reads when there is no resource entry) and
with the pure fragments of the resource functions (`values`). Protocols 2 to 7
check it once, and that Core stands for both. The check compares the pure
programs with each other and the passes with fragments with each other.

Protocols 2 to 6 add an implicit compatibility package (`profilePackage`) to
every request, so its declarations are in their Core. When the Cores differ,
the check compares them again without the declarations of that package; a pair
that is then the same differs only by them.

Run it after the Rust harness has written the pairs to `<directory>`:
`cd lean-kernel && lake env lean --run ../scripts/wire_parity.lean <directory>`
(`scripts/check_wire_parity.sh` runs both). -/
open Lean VastitasKernel

/-- The audit, executable and reverse-compiled Core of one check. -/
structure Passes where
  audit : Indexed.Core.Module
  executable : Indexed.Core.Module
  compiled : Indexed.Core.Module

/-- The package of the implicit compatibility declarations of protocols 2 to 6
(`LegacySource.profilePackage`). -/
def compatibility : Namespace.PackageId := Indexed.LegacySource.profileId

/-- `m` without the declarations of the implicit compatibility package. -/
def withoutCompatibility (m : Indexed.Core.Module) : Indexed.Core.Module :=
  let declarations := m.declarations
  { m with declarations := { declarations with
      indexed := declarations.indexed.filter (·.id.scope.package != compatibility),
      packages := declarations.packages.filter (·.id.scope.package != compatibility),
      primitives := declarations.primitives.filter (·.id.scope.package != compatibility) } }

def Passes.withoutCompatibility (p : Passes) : Passes :=
  ⟨_root_.withoutCompatibility p.audit, _root_.withoutCompatibility p.executable,
    _root_.withoutCompatibility p.compiled⟩

/-- The passes of an accepted request, with the pure fragments of resource
functions and of the pure program, or the code and message of its rejection.
Protocols 2 to 7 have one check, which stands for both. -/
def cores (json : Json) : Except String (Passes × Passes) := do
  let version ← (json.getObjValAs? Nat "version").mapError fun e => s!"no version: {e}"
  let failure (d : Diagnostic) := s!"{d.code}: {d.message}"
  if version == 8 || version == 9 then
    match ResourceSource.Wire.check json false with
    | .error d => throw (failure d)
    | .ok accepted =>
      let values := accepted.checked.values
      let program := accepted.checked.pureProgram
      return (⟨values.audit.core.module, values.executable.core.module, values.compiled.core.module⟩,
        ⟨program.audit.core.module, program.executable.core.module, program.compiled.core.module⟩)
  else if version == 7 then
    match Indexed.Wire.check json false with
    | .error d => throw (failure d)
    | .ok accepted =>
      let c := accepted.checked
      let passes : Passes := ⟨c.audit.core.module, c.executable.core.module, c.compiled.core.module⟩
      return (passes, passes)
  else
    match Indexed.LegacySource.check json false with
    | .error d => throw (failure d)
    | .ok accepted =>
      let c := accepted.checked
      let passes : Passes := ⟨c.audit.core.module, c.executable.core.module, c.compiled.core.module⟩
      return (passes, passes)

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
same, the same without the implicit compatibility declarations of protocols 2
to 6, or how they differ. -/
def describe (version : Nat) (a b : Passes) : String :=
  match differing a b with
  | [] => "same"
  | parts =>
    if version ≤ 6 && (differing a.withoutCompatibility b).isEmpty then
      "same without the compatibility declarations"
    else s!"differs: {", ".intercalate parts}"

/-- The verdict on the Core of one pair. -/
def verdict (original current : Json) : String :=
  let version := (original.getObjValAs? Nat "version").toOption.getD 0
  match cores original, cores current with
  | .error a, .error b => s!"both rejected ({short a} | {short b})"
  | .ok _, .error b => s!"9 rejects: {short b}"
  | .error a, .ok _ => s!"9 accepts what the original route rejects: {short a}"
  | .ok (a, aProgram), .ok (b, bProgram) =>
    let values := describe version a b
    let program := describe version aProgram bProgram
    if values == program then values else s!"with fragments {values}; pure program {program}"

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
  for entry in pairs do
    let name ← field entry "name"
    let from_ := (entry.getObjValAs? Nat "from").toOption.getD 0
    let original ← readJson (directory / (← field entry "original"))
    let current ← readJson (directory / (← field entry "current"))
    let core := verdict original current
    let kind := (core.splitOn ":").headD core |>.splitOn " (" |>.headD core
    kinds := kinds.push s!"{from_}→9 core {kind}"
    lines := lines.push s!"{name} | {from_}→9 | wire: {← field entry "wire"} | core: {core}"
  IO.println "# Core parity of #533 round 1 (W2): development-only"
  let mut counts : List (String × Nat) := []
  for key in kinds.qsort (· < ·) do
    counts := match counts with
      | (last, count) :: rest => if last == key then (last, count + 1) :: rest else (key, 1) :: counts
      | [] => [(key, 1)]
  for (key, count) in counts.reverse do
    IO.println s!"# {count} {key}"
  for line in lines do IO.println line
  IO.FS.writeFile (directory / "core.txt") ("\n".intercalate lines.toList ++ "\n")
  return 0
