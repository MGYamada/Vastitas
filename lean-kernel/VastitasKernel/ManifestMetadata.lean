import Init

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

private inductive Field where | root | package | name | version | edition | other
  deriving BEq

private def path (base : Field) : Parse Field := do
  let mut field := base
  let text ← read
  for _ in [:text.utf8ByteSize - (← get).byteIdx + 1] do
    let name ← key
    field ← match field with
      | .root => pure (if name == "package" then .package else .other)
      | .package => pure <| match name with
        | "name" => .name
        | "version" => .version
        | "edition" => .edition
        | _ => .other
      | .name | .version | .edition => failure
      | .other => pure .other
    space
    unless ← accept '.' do return field
  failure

private def Field.table (field : Field) : Bool := field == .package || field == .other

private def document : Parse Metadata := do
  let text ← read
  discard (accept '\uFEFF')
  let mut tableField := Field.root
  let mut inlineTables : List Field := []
  let mut name := none
  let mut version := none
  let mut edition := none
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
          endValue := true
          continue
      let field ← path (inlineTables.headD tableField)
      guard (← accept '=')
      space
      if ← accept '{' then
        guard field.table
        space
        if ← accept '}' then endValue := true
        else inlineTables := field :: inlineTables
      else
        guard (field != .package)
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
        | _ => pure ()
        endValue := true
  guard (inlineTables.isEmpty && (← peek).isNone)
  let some packageName := name | failure
  let some packageVersion := version | failure
  let some packageEdition := edition | failure
  return ⟨packageName, packageVersion, packageEdition⟩

def read? (text : String) : Option Metadata := (document.run text).run' 0

end VastitasKernel.ManifestMetadata
