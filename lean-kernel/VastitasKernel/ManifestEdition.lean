import Init

set_option autoImplicit false

/-! Read the physical package.edition field in the TOML grammar of a Vastitas
manifest. Manifest leaves are strings. Dotted keys, table headers and inline
tables select the same field. Comments and strings are lexically distinct. -/
namespace VastitasKernel.ManifestEdition

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
  if (← peek) == some c then discard take; return true
  return false

private def skipWhile (f : Char → Bool) : Parse Unit := do
  set (String.Pos.Raw.nextWhile (← read) f (← get))

private def space : Parse Unit := skipWhile fun c => c == ' ' || c == '\t'

private def newline : Parse Bool := do
  if ← accept '\r' then guard (← accept '\n'); return true
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

private inductive Field where | root | package | edition | other
  deriving BEq

private def path (base : Field) : Parse Field := do
  let mut field := base
  let text ← read
  for _ in [:text.utf8ByteSize - (← get).byteIdx + 1] do
    let name ← key
    field ← match field with
      | .root => pure (if name == "package" then .package else .other)
      | .package => pure (if name == "edition" then .edition else .other)
      | .edition => failure
      | .other => pure .other
    space
    unless ← accept '.' do return field
  failure

private def document : Parse String := do
  let text ← read
  discard (accept '\uFEFF')
  let mut tableField := Field.root
  let mut inlineTables : List Field := []
  let mut edition := none
  let mut endValue := false
  for _ in [:text.utf8ByteSize + 2] do
    space
    if endValue then
      match inlineTables with
      | _ :: rest =>
        if ← accept '}' then inlineTables := rest
        else guard (← accept ','); endValue := false
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
          guard (tableField != .edition && (← accept ']'))
          endValue := true
          continue
      let field ← path (inlineTables.headD tableField)
      guard (← accept '=')
      space
      if ← accept '{' then
        guard (field != .edition)
        space
        if ← accept '}' then endValue := true
        else inlineTables := field :: inlineTables
      else
        guard (field != .package)
        let value ← quoted true
        if field == .edition then
          guard edition.isNone
          edition := some value
        endValue := true
  guard (inlineTables.isEmpty && (← peek).isNone)
  let some result := edition | failure
  return result

def readEdition (text : String) : Option String := (document.run text).run' 0

end VastitasKernel.ManifestEdition
