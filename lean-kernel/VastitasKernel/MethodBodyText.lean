import VastitasKernel.SourceText
import VastitasKernel.Keywords
import VastitasKernel.IndexedFunctionSource

set_option autoImplicit false

/-! Check a family method's decoded syntax against its original tokens.
The authority checker has already typed the decoded body. Consume the physical
tokens in order, checking spans, operator precedence and the parentheses erased
by the frontend. The reader holds one lookahead token. -/
namespace VastitasKernel.MethodBodyText
open SourceText Indexed FunctionSource

private structure Stream where
  last : Token
  ahead : Option (String × Token) := none

private abbrev Parser := ReaderT File (EStateM String Stream)

private def look : Parser (String × Token) := do
  let state ← get
  if let some pair := state.ahead then return pair
  let f ← read
  let .ok t := f.next state.last.after | throw "expected another token in family method"
  set {state with ahead := some ("", t)}
  let pair ← match t.kind with
    | .word name => pure (name, t)
    | .separator => pure ("::", t)
    | .symbol ch => do
      if ch.isDigit then
        let stop := String.Pos.Raw.nextWhile f.text Char.isDigit t.after.pos
        if (stop.get? f.text).any (fun ch => ch.isAlpha || ch == '_' || ch == '.') then
          throw "unexpected suffix on a method integer"
        let start : String.Pos.Raw := ⟨t.span.start - f.base⟩
        let after := t.after.ascii (stop.byteIdx - t.after.pos.byteIdx)
        pure (start.extract f.text stop, {t with after, span := {t.span with «end» := f.base + stop.byteIdx}})
      else pure (String.singleton ch, t)
    | _ => throw "unexpected token in family method"
  set {state with ahead := some pair}
  return pair

private def peek : Parser String := do return (← look).1
private def here : Parser Span := do return (← look).2.span

private def takeText (s : String) : Parser Unit := do
  let (found, t) ← look
  unless found == s do throw "family method token differs from its source"
  set (Stream.mk t none)

private def spell (tokens : List String) : Parser Unit :=
  tokens.forM takeText

private def optional (s : String) : Parser Bool := do
  if (← peek) == s then
    takeText s
    return true
  return false

private def sameSpan (first expected : Span) : Parser Unit := do
  unless {first with «end» := (← get).last.span.end} == expected do
    throw "family method node span differs from its source"

private def separated {α : Type} (items : List α) (check : α → Parser Unit)
    (endToken : String) (trailing := true) : Parser Unit := do
  for (item, i) in items.zipIdx do
    if i != 0 then takeText ","
    check item
  if trailing && !items.isEmpty then discard <| optional ","
  takeText endToken

private def identifier (name : String) (allowGeneric := false) : Parser Unit := do
  unless (name.toList.head?.any fun ch => ch.isAlpha || ch == '_') &&
      (!strictKeywords.contains name || (allowGeneric && name == "generic")) do
    throw "invalid identifier in family method"
  takeText name

private def path (parts : List String) : Parser Unit := do
  if parts.isEmpty then throw "empty method path"
  for (part, i) in parts.zipIdx do
    if i != 0 then takeText "::"
    identifier part true

private def reference (p : Source.Path) : Parser Unit := do
  let start ← here
  path p.path
  sameSpan start p.span

private def endpoint (p : Source.Path) : Parser Unit := do
  let start ← here
  let mut depth := 0
  let mut first := true
  for part in p.path do
    if !first then takeText "::"
    if part == "T<>" then
      if first then throw "a Monad endpoint requires a qualified T"
      takeText "T"
      takeText "<"
      depth := depth + 1
      first := true
    else
      identifier part true
      first := false
  if first then throw "missing Hom endpoint"
  for _ in [:depth] do takeText ">"
  sameSpan start p.span

private def decimal (expected : String) : Parser Unit := do
  let digits ← peek
  unless !digits.isEmpty && digits.all Char.isDigit do throw "expected a decimal in family method"
  let trimmed := (digits.dropWhile (· == '0')).toString
  unless (if trimmed.isEmpty then "0" else trimmed) == expected do throw "method integer differs from its source"
  takeText digits

private def rawIndex : RawIndex → Parser Unit
  | .name name => identifier name
  | .base ring => spell ["Base", "(", ring, ")"]

private def twoArgs (name : String) (a b : Parser Unit) : Parser Unit := do
  spell [name, "<"]
  a
  takeText ","
  b
  takeText ">"

private def dataType : Source.DataType → Parser Unit
  | .pure .nat => takeText "Nat"
  | .pure .int => takeText "Int"
  | .pure .bool => takeText "Bool"
  | .pure .unit => takeText "Unit"
  | .pure (.pair elem) => do
    spell ["Pair", "<", (match elem with | .nat => "Nat" | .int => "Int"), ">"]
  | .legacy (.named name) => identifier name
  | .legacy (.point a b) => twoArgs "Point" (rawIndex a) (rawIndex b)
  | .legacy (.morphism a b) => twoArgs "Morphism" (rawIndex a) (rawIndex b)
  | .legacy (.pointed setting base) => twoArgs "Pointed" (identifier setting) (identifier base)
  | .object obj => twoArgs "Object" (reference obj.domain) (reference obj.marker)
  | .finiteHom cat src dst => do
    spell ["Hom", "<"]
    reference cat
    takeText ","
    endpoint src
    takeText ","
    endpoint dst
    takeText ">"
  | .application family args => do
    reference family
    takeText "<"
    separated args (fun | .name p => reference p | .natural n => decimal (toString n)) ">"
  | .legacy (.pair _) | .inferredPackage => throw "unexpected method type annotation"

private def signature : Nat → SignatureSyntax → Parser Unit
  | 0, _ => throw "method function type nesting limit"
  | _, .data t => dataType t
  | fuel + 1, .function params result => do
    takeText "Fn"
    takeText "<"
    if ← optional "(" then separated params.toList (signature fuel) ")"
    else
      let [single] := params.toList | throw "expected grouped function parameters"
      signature fuel single
    takeText ","
    signature fuel result
    takeText ">"

private def fnType : FnType → Parser Unit
  | .data t => dataType t
  | .function s => signature Limits.sourceNesting s

private def parameter (p : Param) : Parser Unit := do
  let start ← here
  identifier p.name
  takeText ":"
  fnType p.type
  sameSpan start p.span

/-- For a binary expression or invocation, leading parentheses belonging to
the first operand start at that operand's claimed span. The recursive match
checks that span against the tokens the operand actually consumed. -/
private def openings : Nat → Option Nat → Parser Nat
  | 0, _ => throw "method grouping nesting limit"
  | fuel + 1, operandStart => do
    let next ← here
    if operandStart.any (· ≤ next.start) then return 0
    unless ← optional "(" do return 0
    return (← openings fuel operandStart) + 1

/-- Parenthesizing the name of a direct call does not make it an invocation. -/
private def remainingGroups : Nat → Parser Nat
  | 0 => return 0
  | n + 1 => do
    if ← optional ")" then remainingGroups n else return n + 1

private def precedence : String → Option Nat
  | "||" => some 1 | "&&" => some 3
  | "==" | "!=" | "<" | "<=" | ">" | ">=" => some 5
  | "+" | "-" => some 9 | "*" | "/" => some 11
  | _ => none

private def operator (op : String) : Parser Unit := do
  let start ← here
  for ch in op.toList do takeText (String.singleton ch)
  unless start.start + op.utf8ByteSize == (← get).last.span.end do throw "spaced method operator"

mutual
  private def expr : Nat → Nat → Expr → Parser Unit
    | 0, _, _ => throw "method expression nesting limit"
    | fuel + 1, minPower, e => do
      let start ← here
      let firstOperand := match e with
        | .binary _ left _ _ | .invoke left _ _ => some left.span.start
        | _ => none
      let mut grouped ← openings Limits.sourceNesting firstOperand
      let required := if grouped > 0 then 0 else minPower
      match e with
      | .integer n _ => decimal n
      | .boolean b _ => takeText (if b then "true" else "false")
      | .unit _ => unless grouped > 0 do throw "expected a unit expression"
      | .variable name _ => identifier name
      | .functionValue p _ => path p.path
      | .call callee args _ =>
        if callee.path == ["generic"] then throw "generic alone is not a callee"
        path callee.path
        grouped ← remainingGroups grouped
        takeText "("
        separated args (expr fuel 0) ")"
      | .finiteLookup table args _ =>
        path ["finite", "lookup"]
        spell ["::", "<"]
        reference table
        takeText ">"
        takeText "("
        separated args (expr fuel 0) ")"
      | .finiteCall callee indices args _ =>
        if callee.path == ["finite","lookup"] || indices.isEmpty then throw "invalid finite method call"
        reference callee
        spell ["::", "<"]
        separated indices reference ">"
        takeText "("
        separated args (expr fuel 0) ")"
      | .invoke callee args _ =>
        if callee matches .variable .. | .functionValue .. then throw "a named method call must retain its path"
        expr fuel 15 callee
        takeText "("
        separated args (expr fuel 0) ")"
      | .lambda params result body _ =>
        spell ["fn", "("]
        separated params parameter ")"
        operator "->"
        fnType result
        block fuel body
      | .lifted .. => throw "a lifted symbol has no source spelling"
      | .unary op operand _ =>
        unless ["!", "-"].contains op && required ≤ 13 do throw "invalid unary operator or grouping"
        operator op
        expr fuel 13 operand
      | .binary op left right _ =>
        let some power := precedence op | throw "unrecognized method operator"
        unless required ≤ power do throw "method operator grouping differs from source"
        expr fuel (if power == 5 then power + 1 else power) left
        operator op
        expr fuel (power + 1) right
      | .branch condition yes no _ =>
        takeText "if"
        expr fuel 0 condition
        block fuel yes
        takeText "else"
        if (← peek) == "if" then
          let .mk [] inner s := no | throw "expected an else-if branch"
          unless (inner matches .branch ..) && inner.span == s do throw "invalid synthetic else-if span"
          expr fuel 0 inner
        else block fuel no
      | .block body _ => block fuel body
      | .pack ty witness fields _ =>
        takeText "pack"
        if ty matches .inferredPackage then
          let [point] := fields | throw "expected a scheme and point"
          spell ["{", "scheme", ":"]
          expr fuel 0 witness
          spell [",", "point", ":"]
          expr fuel 0 point
        else
          dataType ty
          spell ["{", "witness", ":"]
          expr fuel 0 witness
          spell [",", "fields", ":", "["]
          separated fields (expr fuel 0) "]"
        discard <| optional ","
        takeText "}"
      for _ in [:grouped] do takeText ")"
      sameSpan start e.span

  private def block : Nat → Block → Parser Unit
    | 0, _ => throw "method block nesting limit"
    | fuel + 1, .mk statements result span => do
      let start ← here
      takeText "{"
      for s in statements do statement fuel s
      if (← peek) == "}" then
        let .unit s := result | throw "an empty method block returns Unit"
        unless s == (← here) do throw "invalid implicit Unit span"
      else expr fuel 0 result
      takeText "}"
      sameSpan start span

  private def statement : Nat → Stmt → Parser Unit
    | 0, _ => throw "method statement nesting limit"
    | fuel + 1, s => do
      let start ← here
      let span ← match s with
        | .letE name annotation value span => do
          takeText "let"
          identifier name
          if let some ty := annotation then
            takeText ":"
            fnType ty
          takeText "="
          expr fuel 0 value
          pure span
        | .unpack value witness fields span => do
          takeText "unpack"
          expr fuel 0 value
          spell ["as", "{"]
          if ← optional "scheme" then
            let [point] := fields | throw "expected an unpacked point"
            takeText ":"
            identifier witness
            spell [",", "point", ":"]
            identifier point
          else
            spell ["witness", ":"]
            identifier witness
            takeText ","
            spell ["fields", ":", "["]
            separated fields (fun n => identifier n) "]"
          discard <| optional ","
          takeText "}"
          pure span
      takeText ";"
      sameSpan start span
end

private def staticBinder (b : StaticBinder) : Parser Unit := do
  let start ← here
  let span ← match b with
    | .category name schema span => do
      identifier name
      takeText ":"
      reference schema
      pure span
    | .object name owner span | .monadObject name owner span => do
      identifier name
      spell [":", "Obj", "<"]
      identifier owner
      if b matches .monadObject .. then spell ["::", "category"]
      takeText ">"
      pure span
  sameSpan start span

/-- Replay the whole finite-indexed declaration, including binder and schema
spans. The scanner supplied the original fn token in the declaring module. -/
def checkFiniteFunction (file : File) (first : Token) (function : Function) : Except Diagnostic Unit := do
  let check : Parser Unit := do
    takeText "fn"
    identifier function.name
    takeText "<"
    separated function.finiteBinders staticBinder ">"
    takeText "("
    separated function.params parameter ")"
    operator "->"
    fnType function.result
    block Limits.sourceNesting function.body
    sameSpan first.span function.span
  unless first.kind matches .word "fn" do
    throw ⟨"E_FINITE_SOURCE", "expected a finite-indexed function", first.span, []⟩
  match check.run file ⟨first, some ("fn", first)⟩ with
  | .ok _ _ => return ()
  | .error message state =>
    let token := state.ahead.map Prod.snd |>.getD state.last
    throw ⟨"E_FINITE_SOURCE", message, token.span, []⟩

def check (f : File) (opening : Span) (body : Block) : Except Diagnostic Token := do
  let errorAt := fun (span : Span) (message : String) => Diagnostic.mk "E_ASSEMBLY" message span []
  unless f.base ≤ opening.start && opening.end ≤ f.base + f.text.utf8ByteSize do
    throw (errorAt opening "method outside its file")
  let first ← (f.next ⟨⟨opening.start - f.base⟩, opening.line, opening.column⟩).mapError (errorAt opening)
  unless (first.kind matches .symbol '{') && first.span == opening do
    throw (errorAt first.span "missing method opening brace")
  match (block Limits.sourceNesting body).run f ⟨first, some ("{", first)⟩ with
  | .ok _ state => return state.last
  | .error message state =>
    let token := state.ahead.map Prod.snd |>.getD state.last
    throw (errorAt token.span message)

end VastitasKernel.MethodBodyText
