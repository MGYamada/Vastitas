import VastitasKernel.SourceText
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

open SourceText

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

structure EditMethod where
  target : List String
  params : List (String × List String × Span)
  requires_ : List String
  result : List ExactLexeme
  span : Span
  body : Span

structure EditDeclaration extends ExactHeader where
  /-- A contribution's opening brace is the last header lexeme. -/
  contribution : Option (String × List EditMethod) := none

structure EditDeclarations where
  headers : Std.HashMap Nat EditDeclaration := {}
  methods : Std.HashMap Nat (String × List String × EditMethod) := {}
  /-- Surface family names in each lexical scope, including imported aliases. -/
  targets : Std.HashSet (String × List String × List String) := {}
  deriving Inhabited

def EditDeclarations.isEmpty (edits : EditDeclarations) : Bool :=
  edits.headers.isEmpty && edits.methods.isEmpty

structure MethodOwner where
  packageSource : String
  modulePath : List String
  contribution : Option String
  target : List String
  deriving DecidableEq

structure MethodSite where
  owner : MethodOwner
  declaration : Span
  fileIndex : Nat
  opening : Span
  closing : Span

structure SourceChecks where
  headers : Std.HashMap Nat ExactHeader := {}
  calls : Std.HashMap Nat RealizationCall := {}
  /-- Set only for the post-authority comparison with original edit declarations. -/
  edits : Option EditDeclarations := none
  allowAssembly : Bool := false
  fileIndex : Nat := 0
  bodies : Std.HashMap Nat MethodSite := {}
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

def pathLexemes (parts : List String) : List ExactLexeme :=
  (parts.map ExactLexeme.ident).intersperse .separator

def listLexemes (items : List (List ExactLexeme)) (close : Char) : List ExactLexeme :=
  (items.intersperse [.punctuation ',']).flatten ++ [.closeList close (!items.isEmpty)]

private def expectSyntax (f : File) (c : Cursor) (syntax_ : List ExactLexeme) :=
  syntax_.foldlM (expectExact f) c

private def sameSpan (f : File) (head : Token) (after : Cursor) (expected : Span) : Bool :=
  {head.span with «end» := f.base + after.pos.byteIdx} == expected

private def checkEditMethod (f : File) (pkg : String) (modulePath : List String) (origin : Option String)
    (state : Cursor × SourceChecks) (m : EditMethod) : Except String (Cursor × SourceChecks) := do
  let (c, checks) := state
  let first ← expectIdentifier f c "fn"
  let mut after ← expectSyntax f first.after (pathLexemes m.target ++ [.punctuation '('])
  for ((name, ty, span), i) in m.params.zipIdx do
    if i != 0 then after ← expectExact f after (.punctuation ',')
    let param ← expectIdentifier f after name
    after ← expectSyntax f param.after ([.punctuation ':'] ++ pathLexemes ty)
    unless sameSpan f param after span do throw "contributed parameter span differs from its source"
  after ← expectExact f after (.closeList ')' (!m.params.isEmpty))
  let requirements := [.ident "requires", .punctuation '('] ++ listLexemes (m.requires_.map fun n => [.ident n]) ')'
  let before := (← f.next after).kind matches .word "requires"
  if before then after ← expectSyntax f after requirements
  after ← expectSyntax f after ([.arrow] ++ m.result)
  if !before && ((← f.next after).kind matches .word "requires") then
    after ← expectSyntax f after requirements
  else if !before && !m.requires_.isEmpty then throw "contributed fn requires clause missing from source"
  let opening ← f.next after
  requireSymbol opening '{'
  let close ← untilSymbol f '}' opening.after
  unless through opening close == m.body && through first close == m.span do
    throw "contributed fn body or declaration span differs from its source"
  if checks.bodies.contains first.span.start then throw "duplicate physical method site"
  let site := MethodSite.mk ⟨pkg, modulePath, origin, m.target⟩ (through first close) checks.fileIndex opening.span close.span
  return (close.after, {checks with bodies := checks.bodies.insert first.span.start site})

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

/-- A family header or contract ends in a semicolon. Its scalar method
signature contains no brace before the opening brace of a concrete body. -/
private def hasMethodBody (f : File) : Nat → Token → Except String Bool
  | 0, _ => throw "unterminated function family declaration"
  | fuel + 1, t => do
    match t.kind with
    | .symbol '{' => return true
    | .symbol ';' => return false
    | .symbol '}' | .eof => throw "incomplete function family declaration"
    | _ => hasMethodBody f fuel (← f.next t.after)

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
      if let some edits := checks.edits then
        if let .word keyword := t.kind then
          if keyword == "assembly" then throw "retired assembly declaration"
          if keyword == "assemble" && (!checks.allowAssembly || scope.modules != 0 || scope.place == .afterPub) then
            throw "assemble is allowed only in the entry module of the root package"
          if keyword == "generic" || keyword == "method" ||
              (keyword == "abstract" && ((← f.next t.after).kind matches .word "method")) then
            throw "edition 2026 requires fn for a function family, method or contract"
          if keyword == "fn" && !edits.targets.isEmpty then
            if let some (owner, modules, method) := edits.methods[t.span.start]? then
              unless owner == pkg && modules == reversedPath.reverse do
                throw "function family method belongs to another physical module"
              let (after, checks) ← checkEditMethod f pkg modules none (c, checks) method
              let edits := {edits with methods := edits.methods.erase t.span.start}
              return ← scanExact f pkg fuel after {scope with place := .declaration} reversedPath external
                {checks with edits := some edits}
            let (target, next) ← path f t.after
            if target.length > 1 || edits.targets.contains (pkg, reversedPath.reverse, target) then
              if ← hasMethodBody f (f.remaining t.after) next then throw "physical function family method missing from the request"
          if ["grant", "delegation", "transfer", "contribution"].contains keyword then
            let some h := edits.headers[t.span.start]? | throw "physical edit declaration missing from the request"
            unless h.packageSource == pkg && h.modulePath == reversedPath.reverse &&
                h.isPublic == (scope.place == .afterPub) do
              throw "edit declaration package, module or visibility differs from the source"
            let headerEnd ← expectSyntax f c h.lexemes
            let (after, checks) ← match h.contribution with
              | none => pure (headerEnd, checks)
              | some (name, methods) => do
                let (after, checks) ← methods.foldlM (checkEditMethod f pkg h.modulePath (some name)) (headerEnd, checks)
                pure (← expectExact f after (.punctuation '}'), checks)
            unless sameSpan f t after h.span do throw "edit declaration span differs from the source"
            return ← scanExact f pkg fuel after {scope with place := .declaration} reversedPath external
              {checks with edits := some {edits with headers := edits.headers.erase t.span.start}}
      else if let .word "indexed" := t.kind then
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
      if checks.edits.isNone && (t.kind matches .word "resource") then
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
