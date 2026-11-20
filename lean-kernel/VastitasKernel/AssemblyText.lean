import VastitasKernel.Core
import VastitasKernel.Keywords

set_option autoImplicit false

namespace VastitasKernel.AssemblySource

inductive Item where
  | family (target : List String) (span : Span)
  | borrow (grant : List String) (label : Option String) (span : Span)
  | delegate (delegation : List String) (label : Option String) (span : Span)
  | apply (contributions : List (List String)) (span : Span)
  | transfer (declaration : List String) (span : Span)
  | close (span : Span)
  deriving Repr, Inhabited, DecidableEq

def Item.span : Item → Span
  | .family _ s | .borrow _ _ s | .delegate _ _ s | .apply _ s | .transfer _ s | .close s => s

end VastitasKernel.AssemblySource

/-! Recover the edit declarations from the submitted UTF-8 root file. Outside
these declarations the scanner only needs to find root declaration boundaries.
The full parser and the checking of the other declarations have distinct roles.
No token array or recursive representation of nested edit blocks is built. -/
namespace VastitasKernel.AssemblyText
open AssemblySource (Item)

private structure Cursor where
  pos : String.Pos.Raw := 0
  line : Nat := 1
  column : Nat := 1
  deriving Inhabited

private def Cursor.advance (c : Cursor) (ch : Char) : Cursor :=
  ⟨⟨c.pos.byteIdx + ch.utf8Size⟩, if ch == '\n' then c.line + 1 else c.line,
    if ch == '\n' then 1 else c.column + 1⟩

private def Cursor.ascii (c : Cursor) (n : Nat) : Cursor :=
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

private inductive Kind where
  | word (name : String)
  | symbol (ch : Char)
  | separator
  | opaque
  | eof
  deriving Inhabited

private structure Token where
  kind : Kind
  span : Span
  after : Cursor
  deriving Inhabited

private structure File where
  text : String
  base : Nat

private def File.remaining (f : File) (c : Cursor) : Nat :=
  f.text.utf8ByteSize - c.pos.byteIdx + 1

private def File.next (f : File) (before : Cursor) : Except String Token := do
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

private def component (t : Token) : Except String String := do
  let .word name := t.kind | throw "expected an edit path component"
  if name != "generic" && strictKeywords.contains name then throw "unexpected keyword in edit path"
  return name

/-- Parse a qualified path and consume its first following token. -/
private def pathTail (f : File) : Nat → List String → Cursor → Except String (List String × Token)
  | 0, _, _ => .error "incomplete edit path"
  | fuel + 1, parts, c => do
    let t ← f.next c
    if let .separator := t.kind then
      let next ← f.next t.after
      let name ← component next
      pathTail f fuel (name :: parts) next.after
    else return (parts.reverse, t)

private def path (f : File) (c : Cursor) : Except String (List String × Token) := do
  let first ← f.next c
  let name ← component first
  pathTail f (f.remaining first.after) [name] first.after

private def requireSymbol (t : Token) (ch : Char) : Except String Unit := do
  let .symbol found := t.kind | throw "expected punctuation in an edit declaration"
  unless found == ch do throw "unexpected punctuation in an edit declaration"

private def through (first last : Token) : Span :=
  {first.span with «end» := last.span.end}

/-- A grouped apply emits one authority event per path. Bound growth while
reading the group, including where a forged file omits its terminator. -/
private def applyPaths (f : File) : Nat → List (List String) → Token → Except String (List (List String) × Token)
  | 0, _, _ => .error "too many paths in grouped apply"
  | budget + 1, names, delim => do
    match delim.kind with
    | .symbol ';' => return (names.reverse, delim)
    | .symbol ',' =>
      let (name, next) ← path f delim.after
      applyPaths f budget (name :: names) next
    | _ => throw "expected comma or semicolon after an apply path"

private def command (f : File) (depth remaining : Nat) (head : Token) : Except String (Item × Cursor × Nat) := do
  if let .symbol '}' := head.kind then return (.close head.span, head.after, depth - 1)
  let .word name := head.kind | throw "expected an edit command"
  let (target, delim) ← path f head.after
  match name with
  | "assemble" =>
    unless depth == 0 do throw "nested assemble"
    requireSymbol delim '{'
    return (.family target (through head delim), delim.after, 1)
  | "borrow" | "delegate" =>
    unless (name == "borrow" && depth == 1) || (name == "delegate" && depth > 1) do
      throw "loan command at the wrong edit block depth"
    let (label, openBrace) ← match delim.kind with
      | .word "as" => do
        let t ← f.next delim.after
        let .word id := t.kind | throw "expected an edit loan label"
        if strictKeywords.contains id then throw "unexpected keyword as loan label"
        pure (some id, ← f.next t.after)
      | _ => pure (none, delim)
    requireSymbol openBrace '{'
    let span := through head openBrace
    let item := if name == "borrow" then Item.borrow target label span else Item.delegate target label span
    return (item, openBrace.after, depth + 1)
  | "apply" =>
    let (names, semi) ← applyPaths f remaining [target] delim
    return (.apply names (through head semi), semi.after, depth)
  | "transfer" =>
    unless depth == 1 do throw "transfer inside a loan"
    requireSymbol delim ';'
    return (.transfer target (through head delim), delim.after, depth)
  | _ => throw "unknown edit command"

private inductive Place where
  | declaration | afterPub | modKeyword | modName | other
  deriving BEq, Inhabited

private structure Scope where
  modules : Nat := 0
  braces : Nat := 0
  parens : Nat := 0
  brackets : Nat := 0
  place : Place := .declaration
  editDepth : Nat := 0
  events : Nat := 0
  deriving Inhabited

private def Scope.between (s : Scope) : Bool := s.braces == 0 && s.parens == 0 && s.brackets == 0

/-- Recognize inline module scopes at declaration boundaries. A word named
`assemble` in an import, function signature or expression is contextual. -/
private def ordinary (s : Scope) (k : Kind) : Except String Scope := do
  let other := {s with place := Place.other}
  match k with
  | .word "pub" => return {s with place := if s.place == .declaration then .afterPub else .other}
  | .word "mod" =>
    return {s with place := if s.place == .declaration || s.place == .afterPub then .modKeyword else .other}
  | .word _ => return {s with place := if s.place == .modKeyword then .modName else .other}
  | .symbol '{' =>
    if s.place == .modName then return {s with modules := s.modules + 1, place := .declaration}
    return {other with braces := s.braces + 1}
  | .symbol '}' =>
    if s.braces > 0 then
      let out := {other with braces := s.braces - 1}
      return {out with place := if out.between then .declaration else .other}
    unless s.between && s.modules > 0 do throw "unmatched source closing brace"
    return {s with modules := s.modules - 1, place := .declaration}
  | .symbol '(' => return {other with parens := s.parens + 1}
  | .symbol ')' =>
    if s.parens == 0 then throw "unmatched source closing parenthesis"
    return {other with parens := s.parens - 1}
  | .symbol '[' => return {other with brackets := s.brackets + 1}
  | .symbol ']' =>
    if s.brackets == 0 then throw "unmatched source closing bracket"
    return {other with brackets := s.brackets - 1}
  | .symbol ';' => return {s with place := if s.between then .declaration else .other}
  | _ => return other

private def scan (f : File) : Nat → Cursor → Scope → Array Item → Except String (List Item)
  | 0, _, _, _ => .error "source scan exceeded its byte extent"
  | fuel + 1, c, scope, items => do
    let t ← f.next c
    if let .eof := t.kind then
      if scope.editDepth > 0 then throw "unclosed assemble block"
      unless scope.between && scope.modules == 0 do throw "unclosed source delimiter"
      return items.toList
    let declaration := scope.place == .declaration || scope.place == .afterPub
    if declaration then
      if let .word "assembly" := t.kind then throw "retired assembly declaration"
    let family := match t.kind with | .word "assemble" => declaration | _ => false
    if family && (scope.modules != 0 || scope.place == .afterPub) then
      throw "assemble must be a private declaration in the root module"
    if scope.editDepth > 0 || family then
      if items.size ≥ 2 * Limits.assemblyEvents then throw "too many structured assemble items"
      let (item, after, depth) ← command f scope.editDepth (Limits.assemblyEvents - scope.events) t
      let count := match item with | .family .. => 0 | .apply paths _ => paths.length | _ => 1
      let events := scope.events + count
      if events > Limits.assemblyEvents then throw "too many edit events in source"
      let nextScope := {scope with
        place := if depth == 0 then .declaration else .other
        editDepth := depth
        events := events}
      scan f fuel after nextScope (items.push item)
    else
      scan f fuel t.after (← ordinary scope t.kind) items

/-- Project every root-level assembly in this original module file to commands
with absolute byte spans and file-local line/column positions. -/
def parse (source : String) (base : Nat) : Except String (List Item) :=
  scan ⟨source, base⟩ (source.utf8ByteSize + 1) {} {} #[]

/-- A model declaration's expected lexemes, rebuilt from the decoded syntax.
Qualified operands retain their complete original path span. -/
inductive ExactLexeme where
  | ident (name : String)
  | punctuation (ch : Char)
  | reference (parts : List String) (span : Span)
  | dimension (value : Nat)
  | separator
  | arrow
  | closeList (ch : Char) (allowTrailingComma : Bool)
  deriving Inhabited

structure ExactHeader where
  packageSource : String
  modulePath : List String
  span : Span
  isPublic : Bool
  lexemes : List ExactLexeme
  deriving Inhabited

structure ResourceOwner where
  packageSource : String
  modulePath : List String
  name : String
  start : Nat
  isPublic : Bool
  deriving Inhabited, BEq

inductive ResourceCondition where
  | literal (value : Bool)
  | binding (name : String)
  deriving BEq

structure ResourceBranch where
  index : Nat
  condition : ResourceCondition
  yes : Bool
  deriving BEq

structure RealizationCall where
  owner : ResourceOwner
  branches : List ResourceBranch
  index : Nat
  span : Span
  lexemes : List ExactLexeme

structure SourceChecks where
  headers : Std.HashMap Nat ExactHeader := {}
  calls : Std.HashMap Nat RealizationCall := {}
  deriving Inhabited

def SourceChecks.isEmpty (s : SourceChecks) := s.headers.isEmpty && s.calls.isEmpty

private def expectIdentifier (f : File) (c : Cursor) (name : String) : Except String Token := do
  let t ← f.next c
  let .word found := t.kind | throw "expected a physical source identifier"
  unless found == name do throw "identifier differs from the physical source"
  return t

private def expectExact (f : File) (c : Cursor) : ExactLexeme → Except String Cursor
  | .ident name => return (← expectIdentifier f c name).after
  | .punctuation ch => do
    let t ← f.next c
    unless (match t.kind with | .symbol a => a == ch | _ => false) do
      throw "exact declaration punctuation differs from the source"
    return t.after
  | .reference parts span => do
    let head :: tail := parts | throw "empty exact model path"
    let first ← expectIdentifier f c head
    let mut last := first
    for name in tail do
      let sep ← f.next last.after
      let .separator := sep.kind | throw "expected qualified exact model path"
      last ← expectIdentifier f sep.after name
    unless through first last == span do throw "exact model path span differs from the source"
    return last.after
  | .separator => do
    let t ← f.next c
    let .separator := t.kind | throw "expected qualified call separator"
    return t.after
  | .arrow => do
    let t ← f.next c
    requireSymbol t '-'
    let gt ← f.next t.after
    requireSymbol gt '>'
    unless t.span.end == gt.span.start do throw "expected a destination arrow"
    return gt.after
  | .closeList ch allowComma => do
    let next ← f.next c
    let close ← match next.kind with
      | .symbol ',' => if allowComma then f.next next.after else throw "unexpected comma in empty list"
      | _ => pure next
    requireSymbol close ch
    return close.after
  | .dimension value => do
    let t ← f.next c
    let .symbol digit := t.kind | throw "expected a decimal affine dimension"
    unless digit.isDigit do throw "expected a decimal affine dimension"
    let stop := String.Pos.Raw.nextWhile f.text Char.isDigit t.after.pos
    let start : String.Pos.Raw := ⟨t.span.start - f.base⟩
    if stop.byteIdx - start.byteIdx > Limits.algebraCoefficientDigits then throw "affine dimension exceeds digit limit"
    unless (start.extract f.text stop).toNat? == some value do throw "exact affine dimension differs from the source"
    return t.after.ascii (stop.byteIdx - t.after.pos.byteIdx)

private def isExactHeader (f : File) (indexed : Token) : Except String Bool := do
  let kind ← f.next indexed.after
  match kind.kind with
  | .word "carrier" | .word "meadow" => return true
  | .word "affine" | .word "morphism" =>
    let name ← f.next kind.after
    let op ← f.next name.after
    return match op.kind with | .symbol '=' => true | _ => false
  | _ => return false

/-- Skip complete nested groups while finding the terminator of a statement
or signature. Strings and comments have already been consumed by the lexer. -/
private def delimiter (f : File) (stop : Char) : Nat → Cursor → List Char → Nat → Except String Token
  | 0, _, _, _ => .error "missing resource delimiter"
  | fuel + 1, cursor, closes, room => do
    let t ← f.next cursor
    match t.kind with
    | .eof => throw "unterminated resource source"
    | .symbol ch =>
      if closes.isEmpty && ch == stop then return t
      let closing := match ch with | '{' => some '}' | '(' => some ')' | '[' => some ']' | _ => none
      if let some close := closing then
        let room + 1 := room | throw "resource delimiter nesting limit"
        return ← delimiter f stop fuel t.after (close :: closes) room
      if ch == '}' || ch == ')' || ch == ']' then
        let expected :: rest := closes | throw "unexpected resource delimiter"
        unless expected == ch do throw "mismatched resource delimiter"
        return ← delimiter f stop fuel t.after rest (room + 1)
    | _ => pure ()
    delimiter f stop fuel t.after closes room

private def untilSymbol (f : File) (stop : Char) (c : Cursor) :=
  delimiter f stop (f.remaining c) c [] Limits.sourceNesting

private def realizationForm (f : File) (head : Token) : Except String Bool := do
  let .word word := head.kind | return false
  let next ← f.next head.after
  if word == "let" then
    let op ← f.next next.after
    return match op.kind with | .symbol '=' => true | _ => false
  match next.kind with
  | .separator => return true
  | .symbol '(' =>
    let close ← untilSymbol f ')' next.after
    let op ← f.next close.after
    return match op.kind with | .symbol '-' => true | _ => false
  | _ => return false

/-- Compare each realization at its physical statement index. Other resource
statements contribute to the index, including compound contractions. Pure
value blocks contain their own language and are skipped as balanced groups. -/
private def resourceBlock (f : File) (owner : ResourceOwner) : Nat → Cursor → List ResourceBranch → Nat →
    SourceChecks → Except String (Token × SourceChecks)
  | 0, _, _, _, _ => .error "resource scan exceeded its file extent"
  | fuel + 1, c, branches, index, checks => do
    let head ← f.next c
    match head.kind with
    | .eof => throw "unterminated resource function"
    | .symbol '}' => return (head, checks)
    | .word "value" =>
      unless branches.isEmpty do throw "unexpected value return inside a resource branch"
      let start ← f.next head.after
      requireSymbol start '{'
      let body ← untilSymbol f '}' start.after
      let close ← f.next body.after
      requireSymbol close '}'
      return (close, checks)
    | .word "if" =>
      unless branches.length < Limits.sourceNesting do throw "resource branch nesting limit"
      let test ← f.next head.after
      let .word name := test.kind | throw "expected resource branch condition"
      let condition := match name with
        | "true" => ResourceCondition.literal true | "false" => .literal false | name => .binding name
      let openYes ← f.next test.after
      requireSymbol openYes '{'
      let (yes, checks) ← resourceBlock f owner fuel openYes.after (⟨index, condition, true⟩ :: branches) 0 checks
      let otherwise ← expectIdentifier f yes.after "else"
      let openNo ← f.next otherwise.after
      requireSymbol openNo '{'
      let (no, checks) ← resourceBlock f owner fuel openNo.after (⟨index, condition, false⟩ :: branches) 0 checks
      resourceBlock f owner fuel no.after branches (index + 1) checks
    | .word "contract" | .word "contract_tree" =>
      let start ← untilSymbol f '{' head.after
      let endBlock ← untilSymbol f '}' start.after
      resourceBlock f owner fuel endBlock.after branches (index + 1) checks
    | _ =>
      if ← realizationForm f head then
        let some site := checks.calls[head.span.start]? | throw "physical realization missing from request"
        unless site.owner == owner && site.branches == branches && site.index == index do
          throw "realization belongs to another function or statement position"
        let mut cursor := c
        for lexeme in site.lexemes do cursor ← expectExact f cursor lexeme
        let last ← f.next cursor
        requireSymbol last ';'
        unless through head last == site.span do throw "realization statement span differs from source"
        return ← resourceBlock f owner fuel last.after branches (index + 1)
          {checks with calls := checks.calls.erase head.span.start}
      let last ← untilSymbol f ';' head.after
      resourceBlock f owner fuel last.after branches (index + 1) checks

/-- Scan a file in its lexical module, collecting external modules in source
order. A declaration inside a function body cannot change the module path. -/
private def scanExact (f : File) (pkg : String) : Nat → Cursor → Scope → List String →
    Array (List String) → SourceChecks → Except String (Array (List String) × SourceChecks)
  | 0, _, _, _, _, _ => .error "exact declaration scan exceeded its file extent"
  | fuel + 1, c, scope, reversedPath, external, checks => do
    let t ← f.next c
    if let .eof := t.kind then
      unless scope.between && scope.modules == 0 do throw "unclosed source delimiter"
      return (external, checks)
    let atDeclaration := scope.place == .declaration || scope.place == .afterPub
    if atDeclaration then
      if let .word "mod" := t.kind then
        let name ← f.next t.after
        let .word child := name.kind | throw "expected module name"
        let delimiter ← f.next name.after
        let path := child :: reversedPath
        match delimiter.kind with
        | .symbol ';' =>
          return ← scanExact f pkg fuel delimiter.after {scope with place := .declaration}
            reversedPath (external.push path.reverse) checks
        | .symbol '{' =>
          return ← scanExact f pkg fuel delimiter.after {scope with place := .declaration, modules := scope.modules + 1}
            path external checks
        | _ => throw "expected module body or semicolon"
      if let .word "indexed" := t.kind then
        if ← isExactHeader f t then
          let some h := checks.headers[t.span.start]? | throw "physical exact declaration missing from the request"
          unless h.packageSource == pkg && h.modulePath == reversedPath.reverse do
            throw "exact declaration belongs to another physical package or module"
          unless h.isPublic == (scope.place == .afterPub) do throw "exact declaration visibility differs from the source"
          let mut after := t.after
          for lexeme in h.lexemes do after ← expectExact f after lexeme
          let semi ← f.next after
          requireSymbol semi ';'
          unless through t semi == h.span do throw "exact declaration span differs from the source"
          return ← scanExact f pkg fuel semi.after {scope with place := .declaration}
            reversedPath external {checks with headers := checks.headers.erase t.span.start}
      if let .word "resource" := t.kind then
        let fnToken ← expectIdentifier f t.after "fn"
        let name ← f.next fnToken.after
        let .word fnName := name.kind | throw "expected resource function name"
        let owner := ResourceOwner.mk pkg reversedPath.reverse fnName t.span.start (scope.place == .afterPub)
        let start ← untilSymbol f '{' name.after
        let (close, checks) ← resourceBlock f owner (f.remaining start.after) start.after [] 0 checks
        return ← scanExact f pkg fuel close.after {scope with place := .declaration} reversedPath external checks
    let next ← ordinary scope t.kind
    let path := if next.modules < scope.modules then reversedPath.drop 1 else reversedPath
    scanExact f pkg fuel t.after next path external checks

def mayHaveExactHeaders (text : String) : Bool :=
  text.contains "resource" ||
    (text.contains "indexed" && (text.contains "carrier" || text.contains "meadow" || text.contains "Affine" || text.contains "identity"))

def checkExactHeaders (text : String) (base : Nat) (pkg : String) (path : List String)
    (checks : SourceChecks) : Except String (Array (List String) × SourceChecks) :=
  scanExact ⟨text,base⟩ pkg (text.utf8ByteSize + 1) {} {} path.reverse #[] checks

end VastitasKernel.AssemblyText
