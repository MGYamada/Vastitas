import VastitasKernel.EnvelopeProtocol
import VastitasKernel.AssemblyText

/-! The finite source grammar of per-family assembly. The flattened item stream
retains the source operands, optional labels and spans, without nesting JSON.
It is independent of the event stream on which edit authority is decided. -/
namespace VastitasKernel.AssemblySource
open Lean JsonDecode Namespace

deriving instance DecidableEq for Namespace.EditEvent

structure RootFile where
  offset : Nat
  text : String

/-- The entry file and its base in the frontend's disjoint span space.
The file and aggregate limits match the public source loader; it reserves a
one-byte gap between each of at most 8192 physical inputs. -/
def rootFile (json : Json) : Except String RootFile := do
  let file ← field json "root_source"
  fields file ["offset", "text", "files"]
  let offset ← file.getObjValAs? Nat "offset"
  let text ← str file "text"
  if (← str json "root") == flatPackageId.source && offset != 0 then
    throw "the protected flat entry file must start at byte offset zero"
  if text.utf8ByteSize > 16 * 1024 * 1024 || offset + text.utf8ByteSize > 64 * 1024 * 1024 + 8191 then
    throw "root source is outside the file or compilation-unit byte limit"
  return ⟨offset, text⟩

private def item (j : Json) : Except String Item := do
  let span ← decodeSpan j
  match ← str j "kind" with
  | "family" => fields j ["kind","target","span"]; return .family (← segments j "target") span
  | "borrow" =>
    fields j ["kind","grant","label","span"]
    return .borrow (← segments j "grant") (← j.getObjValAs? (Option String) "label") span
  | "delegate" =>
    fields j ["kind","delegation","label","span"]
    return .delegate (← segments j "delegation") (← j.getObjValAs? (Option String) "label") span
  | "apply" =>
    fields j ["kind","contributions","span"]
    let paths ← array j "contributions"
    if paths.isEmpty || paths.length > Limits.assemblyEvents then throw "invalid grouped apply length"
    return .apply (← paths.mapM fun p => do (← p.getArr?).toList.mapM Json.getStr?) span
  | "transfer" =>
    fields j ["kind","declaration","span"]
    return .transfer (← segments j "declaration") span
  | "close" => fields j ["kind","span"]; return .close span
  | _ => throw "unknown structured assemble item"

/-- Only the raw root package's root module supplies the source. Authority
independently rejects assembly anywhere else and ambiguous root identities. -/
def read (json : Json) : Except String (List Item) := do
  let root ← str json "root"
  for pkg in ← array json "packages" do
    if (← str pkg "source") != root then continue
    for m in ← array pkg "modules" do
      unless (← array m "path").isEmpty do continue
      let .ok a := m.getObjVal? "assembly" | return []
      let items ← array a "source"
      if items.isEmpty || items.length > 2 * Limits.assemblyEvents then throw "invalid structured assembly size"
      return ← items.mapM item
  return []

structure Expansion where
  events : List EditEvent
  span : Option Span

/-- At most the number of explicit labels can conflict with successive
candidates. The counter is shared across every family block in the unit. -/
private def chooseLoan (labels : Std.HashSet String) (path : List String) (next : Nat) :
    Option String → Option (String × Nat)
  | some label => some (label, next)
  | none => do
    let last ← path.getLast?
    visit (labels.size + 1) next last
where
  visit : Nat → Nat → String → Option (String × Nat)
    | 0, _, _ => none
    | fuel + 1, n, last =>
      let label := s!"loan_{n}_{last}"
      if labels.contains label then visit fuel (n + 1) last else some (label, n + 1)

def expand (items : List Item) : Except String Expansion := do
  let labels := Std.HashSet.ofList (items.filterMap fun
    | .borrow _ label _ | .delegate _ label _ => label | _ => none)
  let mut next := 0
  let mut loans : List String := []
  let mut family : Option (List String) := none
  let mut span : Option Span := none
  let mut events : Array EditEvent := #[]
  let mut previousEnd := 0
  for cmd in items do
    if cmd.span.start < previousEnd || cmd.span.start ≥ cmd.span.end then
      throw "structured assembly source items must have nonempty, ordered byte spans"
    previousEnd := cmd.span.end
    match cmd with
    | .family target place =>
      if family.isSome || target.isEmpty then throw "invalid assemble header"
      family := some target
      span := span.or (some place)
    | _ =>
      let some target := family | throw "assembly item outside a family block"
      let remaining := Limits.assemblyEvents - events.size
      if remaining == 0 then throw "expanded source exceeds the assembly event limit"
      match cmd with
      | .borrow grant label place =>
        if !loans.isEmpty then throw "nested borrow in assemble"
        let some (name, n) := chooseLoan labels grant next label | throw "invalid borrow label"
        events := events.push (.borrow grant name place)
        next := n
        loans := [name]
      | .delegate delegation label place =>
        let parent :: _ := loans | throw "delegation without a parent loan"
        let some (name, n) := chooseLoan labels delegation next label | throw "invalid delegation label"
        events := events.push (.reborrow parent delegation name place)
        next := n
        loans := name :: loans
      | .apply paths place =>
        if paths.isEmpty || paths.length > remaining then throw "invalid grouped application"
        for path in paths do events := events.push (.apply path loans.head? place)
      | .transfer decl place =>
        if !loans.isEmpty then throw "transfer inside a loan"
        events := events.push (.transfer decl place)
      | .close place =>
        if place.end != place.start + 1 then throw "a closing brace must occupy one byte"
        match loans with
        | name :: rest =>
          events := events.push (.release name place)
          loans := rest
        | [] =>
          events := events.push (.seal target place)
          family := none
          span := span.map fun first => {first with «end» := place.end}
      | .family .. => throw "unexpected nested family header"
  if family.isSome then throw "missing closing brace in assemble"
  return ⟨events.toList, span⟩

/-- Equality is structural: each resolved path spelling, full source place,
order and nominal loan label reaches the very events used by Authority. -/
structure Corresponds (json : Json) (assembly : Namespace.Assembly) where
  file : RootFile
  supplied : rootFile json = .ok file
  items : List Item
  lexical : AssemblyText.parse file.text file.offset = .ok items
  decoded : read json = .ok items
  trace : Expansion
  expanded : expand items = .ok trace
  exactEvents : trace.events = assembly.events
  exactSpan : trace.span.all (· == assembly.span) = true

def check (json : Json) (a : Namespace.Assembly) : Except Diagnostic (Corresponds json a) := do
  match hsFile : rootFile json with
  | .error message => throw {code := "E_PROTOCOL", message, span := a.span}
  | .ok file =>
    match h : read json, hl : AssemblyText.parse file.text file.offset with
    | .error message, _ => throw {code := "E_PROTOCOL", message, span := a.span}
    | _, .error message => throw {code := "E_ASSEMBLY", message, span := a.span}
    | .ok items, .ok scanned =>
      if (json.getObjVal? "root").toOption == some (.str flatPackageId.source) && !items.isEmpty then
        throw {code := "E_ASSEMBLY", message := "assemble requires a package source file", span := a.span}
      if same : scanned = items then
        match he : expand items with
        | .error message => throw {code := "E_ASSEMBLY", message, span := a.span}
        | .ok trace =>
          if eq : trace.events = a.events then
            if hs : trace.span.all (· == a.span) then
              return ⟨file, hsFile, items, same ▸ hl, h, trace, he, eq, hs⟩
            else throw {code := "E_ASSEMBLY", message := "assembly source span differs from its block boundaries", span := a.span}
          else throw {code := "E_ASSEMBLY", message := "assembly events differ from the structured source expansion", span := a.span}
      else throw {code := "E_ASSEMBLY", message := "structured assembly differs from the entry source text", span := a.span}

end VastitasKernel.AssemblySource
