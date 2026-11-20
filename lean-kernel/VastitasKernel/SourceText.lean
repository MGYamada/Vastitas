import VastitasKernel.Core

set_option autoImplicit false

/-! Streaming tokens for the independent physical source comparisons. -/
namespace VastitasKernel.SourceText

structure Cursor where
  pos : String.Pos.Raw := 0
  line : Nat := 1
  column : Nat := 1
  deriving Inhabited

private def Cursor.advance (c : Cursor) (ch : Char) : Cursor :=
  ⟨⟨c.pos.byteIdx + ch.utf8Size⟩, if ch == '\n' then c.line + 1 else c.line,
    if ch == '\n' then 1 else c.column + 1⟩

def Cursor.ascii (c : Cursor) (n : Nat) : Cursor :=
  {c with pos := ⟨c.pos.byteIdx + n⟩, column := c.column + n}

private def white (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' ||
    [0xa0, 0x1680, 0x202f, 0x205f, 0x3000].contains c.toNat ||
    (0x2000 ≤ c.toNat && c.toNat ≤ 0x200a)

private def lineBreakOk (s : String) (p : String.Pos.Raw) (ch : Char) : Bool :=
  if ch == '\r' then (p.next s).get? s == some '\n'
  else !([0xb, 0xc, 0x1c, 0x1d, 0x1e, 0x85, 0x2028, 0x2029].contains ch.toNat)

private def deceptiveComment (ch : Char) : Bool :=
  [0x61c, 0x200b, 0x200e, 0x200f, 0xfeff].contains ch.toNat ||
    (0x202a ≤ ch.toNat && ch.toNat ≤ 0x202e) || (0x2060 ≤ ch.toNat && ch.toNat ≤ 0x206f)

private def identStart (ch : Char) : Bool := ch.isAlpha || ch == '_'
private def identRest (ch : Char) : Bool := identStart ch || ch.isDigit

/-- The cursor advances by Unicode scalars for columns and by UTF-8 bytes
for offsets. LF resets the column, including when preceded by CR. -/
private def trivia (s : String) : Nat → Cursor → Bool → Except String Cursor
  | 0, _, _ => .error "source scan exceeded its byte extent"
  | fuel + 1, c, comment =>
    match c.pos.get? s with
    | none => .ok c
    | some ch =>
      if comment && ' ' ≤ ch && ch ≤ '~' then
        let stop := String.Pos.Raw.nextWhile s (fun c => ' ' ≤ c && c ≤ '~') c.pos
        trivia s fuel (c.ascii (stop.byteIdx - c.pos.byteIdx)) true
      else if !lineBreakOk s c.pos ch then .error "unsupported source line separator"
      else if comment then
        if deceptiveComment ch then .error "invalid source comment character"
        else trivia s fuel (c.advance ch) (ch != '\n')
      else if white ch then trivia s fuel (c.advance ch) false
      else if ch == '/' && (c.pos.next s).get? s == some '/' then trivia s fuel (c.ascii 2) true
      else .ok c

private def quoted (s : String) : Nat → Cursor → Bool → Except String Cursor
  | 0, _, _ => .error "unterminated source string"
  | fuel + 1, c, escaped => do
    let some ch := c.pos.get? s | throw "unterminated source string"
    unless lineBreakOk s c.pos ch do throw "unsupported source line separator"
    if !escaped && ch == '"' then return c.advance ch
    quoted s fuel (c.advance ch) (!escaped && ch == '\\')

inductive Kind where
  | word (name : String)
  | symbol (ch : Char)
  | separator
  | opaque
  | eof
  deriving Inhabited

structure Token where
  kind : Kind
  span : Span
  after : Cursor
  deriving Inhabited

structure File where
  text : String
  base : Nat

def File.remaining (f : File) (c : Cursor) : Nat :=
  f.text.utf8ByteSize - c.pos.byteIdx + 1

def File.next (f : File) (before : Cursor) : Except String Token := do
  let c ← trivia f.text (f.remaining before) before false
  let make (kind : Kind) (after : Cursor) : Token :=
    ⟨kind, ⟨f.base + c.pos.byteIdx, f.base + after.pos.byteIdx, c.line, c.column⟩, after⟩
  let some ch := c.pos.get? f.text | return make .eof c
  if identStart ch then
    let stop := String.Pos.Raw.nextWhile f.text identRest c.pos
    return make (.word (String.Pos.Raw.extract f.text c.pos stop)) (c.ascii (stop.byteIdx - c.pos.byteIdx))
  if ch == '"' then
    let cursor ← quoted f.text (f.remaining c) (c.ascii 1) false
    return make .opaque cursor
  if ch == ':' && (c.pos.next f.text).get? f.text == some ':' then
    return make .separator (c.ascii 2)
  if ch == '/' && (c.pos.next f.text).get? f.text == some '*' then
    throw "block comments are outside the source grammar"
  if ch == '\uFEFF' then throw "unexpected byte order mark"
  return make (.symbol ch) (c.advance ch)

end VastitasKernel.SourceText
