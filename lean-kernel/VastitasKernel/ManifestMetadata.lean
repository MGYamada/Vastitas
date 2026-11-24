import Std.Data.TreeMap.Basic

set_option autoImplicit false

/-! Read the fields that identify a package and select its edition in a Vastitas
manifest. All leaves of this manifest schema are strings. Table headers,
dotted keys and inline tables can address the same fields. -/
namespace VastitasKernel.ManifestMetadata

structure Metadata where
  name : String
  version : String
  edition : String
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq

private abbrev Parse := ReaderT String (StateT String.Pos.Raw Option)

private def peek : Parse (Option Char) := do
  return (← get).get? (← read)

private def take : Parse Char := do
  let text ← read
  let pos ← get
  let some c := pos.get? text | failure
  set (pos.next text)
  return c

private def accept (c : Char) : Parse Bool := do
  if (← peek) == some c then
    discard take
    return true
  return false

private def skipWhile (f : Char → Bool) : Parse Unit := do
  set (String.Pos.Raw.nextWhile (← read) f (← get))

private def space : Parse Unit := skipWhile fun c => c == ' ' || c == '\t'

private def newline : Parse Bool := do
  if ← accept '\r' then
    guard (← accept '\n')
    return true
  return ← accept '\n'

private def comment : Parse Unit := do
  if ← accept '#' then skipWhile fun c => c != '\n' && c != '\r'

private def hex (count : Nat) : Parse Char := do
  let mut n := 0
  for _ in [:count] do
    let c ← take
    let digit ← if c.isDigit then pure (c.toNat - '0'.toNat)
      else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
      else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
      else failure
    n := n * 16 + digit
  guard (n ≤ 0x10ffff && !(0xd800 ≤ n && n ≤ 0xdfff))
  return Char.ofNat n

private def escape (multi : Bool) : Parse (Option Char) := do
  if multi then
    let before ← get
    space
    if ← newline then
      let text ← read
      for _ in [:text.utf8ByteSize - (← get).byteIdx + 1] do
        space
        unless ← newline do break
      return none
    guard ((← get).byteIdx == before.byteIdx)
  match ← take with
  | 'b' => return some (Char.ofNat 8)
  | 't' => return some '\t'
  | 'n' => return some '\n'
  | 'f' => return some (Char.ofNat 12)
  | 'r' => return some '\r'
  | '"' => return some '"'
  | '\\' => return some '\\'
  | 'u' => return some (← hex 4)
  | 'U' => return some (← hex 8)
  | _ => failure

private def quoted (allowMulti : Bool) : Parse String := do
  let q ← take
  guard (q == '"' || q == '\'')
  let mut multi := false
  if ← accept q then
    if !(← accept q) then return ""
    guard allowMulti
    multi := true
    discard newline
  let text ← read
  let mut value := ""
  for _ in [:text.utf8ByteSize - (← get).byteIdx + 1] do
    let start ← get
    let stop := String.Pos.Raw.nextWhile text (fun c =>
      c != q && (q != '"' || c != '\\') && c ≥ ' ' && c != Char.ofNat 127) start
    value := value ++ String.Pos.Raw.extract text start stop
    set stop
    if ← accept q then
      if !multi then return value
      if !(← accept q) then value := value.push q; continue
      if !(← accept q) then value := (value.push q).push q; continue
      for _ in [:2] do
        if ← accept q then value := value.push q
      return value
    if q == '"' && (← accept '\\') then
      if let some c ← escape multi then value := value.push c
    else if ← accept '\t' then value := value.push '\t'
    else
      guard multi
      guard (← newline)
      value := value.push '\n'
  failure

private def bareKey (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_'

private def key : Parse String := do
  space
  if (← peek).any fun c => c == '"' || c == '\'' then return ← quoted false
  let text ← read
  let start ← get
  let stop := String.Pos.Raw.nextWhile text bareKey start
  guard (start.byteIdx < stop.byteIdx)
  set stop
  return String.Pos.Raw.extract text start stop

structure Written where
  text : String
  start : Nat
  stop : Nat
  deriving BEq

structure Dependency where
  alias : Written
  path : Written

/-- Key segments stay separate so quoted TOML keys containing periods cannot introduce a nested role. -/
private inductive Field where
  | root | package | name | version | edition | sourceRoot
  | dependencies | dependency (alias : Written) | dependencyPath (alias : Written)
  | geometry | setting (name : String) | role (key : List String)
  deriving BEq

private def path (base : Field) : Parse Field := do
  let mut field := base
  let text ← read
  for _ in [:text.utf8ByteSize - (← get).byteIdx + 1] do
    space
    let beginKey ← get
    let name ← key
    let endKey ← get
    field ← match field with
      | .root => match name with
        | "package" => pure .package | "dependencies" => pure .dependencies | "geometry_compat" => pure .geometry
        | _ => failure
      | .dependencies => pure (.dependency ⟨name, beginKey.byteIdx, endKey.byteIdx⟩)
      | .dependency alias => do guard (name == "path"); pure (.dependencyPath alias)
      | .geometry =>
        pure (if name == "scheme" || name == "smooth" then .setting name else .role [name])
      | .setting setting => pure (.role [setting, name])
      | .role _ | .dependencyPath _ => failure
      | .package => match name with
        | "name" => pure .name | "version" => pure .version | "edition" => pure .edition | "root" => pure .sourceRoot
        | _ => failure
      | .name | .version | .edition | .sourceRoot => failure
    space
    unless ← accept '.' do return field
  failure

private def Field.table : Field → Bool
  | .package | .dependencies | .dependency _ | .geometry | .setting _ => true
  | _ => false

structure Document where
  metadata : Metadata
  paths : Std.TreeMap String Dependency
  geometry : Option (List (List String × Written))

private structure Declarations where
  deps : Std.TreeMap String (Option Dependency) := {}
  geometry : Option (List (List String × Written)) := none

private def Declarations.table (d : Declarations) : Field → Declarations
  | .dependency alias => {d with deps := d.deps.insertIfNew alias.text none}
  | .geometry | .setting _ => {d with geometry := some (d.geometry.getD [])}
  | _ => d

private def Declarations.leaf (d : Declarations) (field : Field) (value : Written) : Option Declarations := do
  match field with
  | .dependencyPath alias =>
    guard ((d.deps.get? alias.text).join.isNone)
    return {d with deps := d.deps.insert alias.text (some ⟨alias, value⟩)}
  | .role key =>
    let rows := d.geometry.getD []
    -- Exactly 21 roles exist in a complete profile, so the duplicate check is bounded.
    guard (rows.length < 21 && !(rows.any (fun row => row.1 == key)))
    return {d with geometry := some ((key, value) :: rows)}
  | .dependencies | .dependency _ | .geometry | .setting _ => failure
  | _ => return d

private def document : Parse Document := do
  let text ← read
  discard (accept '\uFEFF')
  let mut tableField := Field.root
  let mut inlineTables : List Field := []
  let mut name := none
  let mut version := none
  let mut edition := none
  let mut hasSourceRoot := false
  let mut decls : Declarations := {}
  let mut endValue := false
  for _ in [:text.utf8ByteSize + 2] do
    space
    if endValue then
      match inlineTables with
      | _ :: rest =>
        if ← accept '}' then inlineTables := rest
        else
          guard (← accept ',')
          endValue := false
      | [] =>
        comment
        if (← peek).isNone then break
        guard (← newline)
        endValue := false
    else
      if inlineTables.isEmpty then
        comment
        if (← peek).isNone then break
        if ← newline then continue
        if ← accept '[' then
          tableField ← path .root
          guard (tableField.table && (← accept ']'))
          decls := decls.table tableField
          endValue := true
          continue
      let field ← path (inlineTables.headD tableField)
      guard (← accept '=')
      space
      if ← accept '{' then
        guard field.table
        decls := decls.table field
        space
        if ← accept '}' then endValue := true
        else inlineTables := field :: inlineTables
      else
        guard (field != .package)
        let start ← get
        let value ← quoted true
        match field with
        | .name =>
          guard name.isNone
          name := some value
        | .version =>
          guard version.isNone
          version := some value
        | .edition =>
          guard edition.isNone
          edition := some value
        | .sourceRoot =>
          guard (!hasSourceRoot && !value.isEmpty && !value.contains (Char.ofNat 0))
          hasSourceRoot := true
        | field =>
          let some next := decls.leaf field ⟨value, start.byteIdx, (← get).byteIdx⟩ | failure
          decls := next
        endValue := true
  guard (inlineTables.isEmpty && (← peek).isNone && hasSourceRoot)
  let some packageName := name | failure
  let some packageVersion := version | failure
  let some packageEdition := edition | failure
  let mut paths := {}
  for (alias, path) in decls.deps do
    let some value := path | failure
    paths := paths.insert alias value
  return ⟨⟨packageName, packageVersion, packageEdition⟩, paths, decls.geometry⟩

def readDocument? (text : String) : Option Document := (document.run text).run' 0

def read? (text : String) : Option Metadata := (readDocument? text).map (·.metadata)

end VastitasKernel.ManifestMetadata
