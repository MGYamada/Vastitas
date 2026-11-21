import VastitasKernel.AssemblyText
import VastitasKernel.IndexedSource

set_option autoImplicit false

/-! Physical syntax of presented affine objects, fiber products, localizations
and standard affine spaces, including the definitions of maps between them. The algebra checker consumes the decoded polynomial
tree. Compare that tree before any evaluation or normalization. -/
namespace VastitasKernel.AffineDeclarationText
open SourceText AssemblyText Indexed

private abbrev Parser := ReaderT File (EStateM String Cursor)

private def next : Parser Token := do
  match (← read).next (← get) with
  | .ok t => return t
  | .error msg => throw msg

private def expect (lexeme : ExactLexeme) : Parser Unit := do
  match expectExact (← read) (← get) lexeme with
  | .ok after => set after
  | .error msg => throw msg

private def symbol (ch : Char) := expect (.punctuation ch)
private def word (s : String) := expect (.ident s)
private def reference (p : Source.Path) := expect (.reference p.path p.span)

private def acceptSymbol (ch : Char) : Parser Bool := do
  let t ← next
  if let .symbol c := t.kind then
    if c == ch then
      set t.after
      return true
  return false

private def acceptWord (s : String) : Parser Bool := do
  let t ← next
  if let .word w := t.kind then
    if w == s then
      set t.after
      return true
  return false

private def component : Parser String := do
  let t ← next
  let .word s := t.kind | throw "expected an affine coordinate name"
  if strictKeywords.contains s then throw "keyword in affine coordinate name"
  set t.after
  return s

private def coordinateTail (head : String) : Parser String := do
  let f ← read
  let mut names := [head]
  for _ in [:f.remaining (← get)] do
    let t ← next
    unless t.kind matches .separator do break
    set t.after
    names := (← component) :: names
  return String.intercalate "::" names.reverse

private def natural : Parser Nat := do
  let t ← next
  let .symbol ch := t.kind | throw "expected a polynomial literal"
  unless ch.isDigit do throw "expected a polynomial literal"
  let f ← read
  let start : String.Pos.Raw := ⟨t.span.start - f.base⟩
  let stop := String.Pos.Raw.nextWhile f.text Char.isDigit t.after.pos
  if stop.byteIdx - start.byteIdx > Limits.algebraCoefficientDigits then throw "oversized polynomial literal"
  let some n := (start.extract f.text stop).toNat? | throw "invalid polynomial literal"
  set (t.after.ascii (stop.byteIdx - t.after.pos.byteIdx))
  return n

private def atom (group : Parser Source.PolyExpr) : Parser Source.PolyExpr := do
  if ← acceptSymbol '(' then
    let inner ← group
    symbol ')'
    return inner
  if let .symbol ch := (← next).kind then
    if ch.isDigit then return .natural (← natural)
  let name ← component
  if name == "frac" && (← acceptSymbol '(') then
    let negative ← acceptSymbol '-'
    let n ← natural
    symbol ','
    let d ← natural
    symbol ')'
    return .fraction (if negative then -(Int.ofNat n) else Int.ofNat n) d
  return .coordinate (← coordinateTail name)

private def productOf (unary : Parser Source.PolyExpr) : Parser Source.PolyExpr := do
  let first ← unary
  let mut rest := []
  let f ← read
  for _ in [:f.remaining (← get)] do
    unless ← acceptSymbol '*' do break
    rest := (← unary) :: rest
  return if rest.isEmpty then first else .product (first :: rest.reverse)

private def sumOf (term : Parser Source.PolyExpr) : Parser Source.PolyExpr := do
  let first ← term
  let mut rest := []
  let f ← read
  for _ in [:f.remaining (← get)] do
    if ← acceptSymbol '+' then rest := (← term) :: rest
    else if ← acceptSymbol '-' then rest := .neg (← term) :: rest
    else break
  return if rest.isEmpty then first else .sum (first :: rest.reverse)

/-- Parentheses and prefix minus share the source nesting budget. Exponentiation
binds to an atom, multiplication to unary operands, then sums and differences. -/
private structure PolynomialReader where
  unary : Parser Source.PolyExpr
  expression : Parser Source.PolyExpr

private def reader : Nat → PolynomialReader
  | 0 => ⟨throw "polynomial nesting limit", throw "polynomial nesting limit"⟩
  | n + 1 =>
    let nested := reader n
    let unary : Parser Source.PolyExpr := do
      if ← acceptSymbol '-' then return .neg (← nested.unary)
      let base ← atom nested.expression
      if ← acceptSymbol '^' then return .pow base (← natural)
      return base
    ⟨unary, sumOf (productOf unary)⟩

def samePoly : Nat → Source.PolyExpr → Source.PolyExpr → Bool
  | 0, _, _ => false
  | _ + 1, .natural a, .natural b => a == b
  | _ + 1, .coordinate a, .coordinate b => a == b
  | _ + 1, .fraction a b, .fraction c d => a == c && b == d
  | n + 1, .neg a, .neg b => samePoly n a b
  | n + 1, .pow a i, .pow b j => i == j && samePoly n a b
  | n + 1, .sum as, .sum bs | n + 1, .product as, .product bs => as.isEqv bs (samePoly n)
  | _ + 1, _, _ => false

private theorem list_match_sound {α : Type} (test : α → α → Bool)
    (sound : ∀ a b, test a b = true → a = b) (xs ys : List α)
    (h : xs.isEqv ys test = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp (List.isEqv_cons_cons ▸ h)
      rw [sound _ _ head, ih ys tail]

/-- A successful comparison preserves the whole polynomial, including the order
of factors, summands and the operands of differences. -/
theorem samePoly_sound (fuel : Nat) (parsed expected : Source.PolyExpr)
    (h : samePoly fuel parsed expected = true) : parsed = expected := by
  induction fuel generalizing parsed expected with
  | zero => simp [samePoly] at h
  | succ n ih =>
    cases parsed <;> cases expected <;> simp [samePoly] at h ⊢
    all_goals first
      | exact h
      | exact ih _ _ h
      | exact ⟨ih _ _ h.2, h.1⟩
      | exact list_match_sound _ ih _ _ h

private def polynomial (expected : Source.PolyExpr) : Parser Unit := do
  let cursor ← get
  let parsed ← (reader Limits.algebraNesting).expression
  unless samePoly Limits.algebraNesting parsed expected do
    set cursor
    throw "polynomial differs from its physical affine declaration"

private def separated {α : Type} (items : List α) (check : α → Parser Unit) (close : Char) : Parser Unit := do
  for (x, i) in items.zipIdx do
    if i != 0 then symbol ','
    check x
  expect (.closeList close (!items.isEmpty))

private def matchingName (name : Parser String) (expected : String) : Parser Unit := do
  let start ← get
  unless (← name) == expected do
    set start
    throw "affine coordinate name differs from its source"

private def bindings (items : List (String × Source.PolyExpr)) : Parser Unit := do
  symbol '('
  separated items (fun (name, image) => do
    matchingName (component >>= coordinateTail) name
    expect .arrow
    polynomial image) ')'

private def names (items : List String) : Parser Unit := do
  symbol '['
  separated items (matchingName component) ']'

private def implementation (p : Source.Path) : Parser Unit := do
  symbol '('
  reference p
  symbol ')'
  symbol '='

private def invariant (keyword : String) (subject : Source.Path) (index : Nat) : Parser Unit := do
  word keyword
  symbol '('
  reference subject
  symbol ','
  let start ← get
  unless (← natural) == index do
    set start
    throw "spectral morphism index differs from its source"
  symbol ')'

private def morphism (family : Source.Path) (indices : List Source.Path)
    (definition : Source.MorphismDefinition) : Parser Unit := do
  symbol ':'
  reference family
  symbol '<'
  let first :: rest := indices | throw "expected morphism endpoints"
  reference first
  for index in rest do
    symbol ','
    reference index
  symbol '>'
  symbol '='
  match definition with
  | .pullback images =>
    word "pullback"
    bindings images
  | .identity => word "identity"
  | .structureMap => word "structure"
  | .first => word "first"
  | .second => word "second"
  | .restrict p =>
    word "restrict"
    symbol '('
    reference p
    symbol ')'
  | .tracePower p n => invariant "trace_power" p n
  | .charCoefficient p n => invariant "char_coefficient" p n

private def object (body : Source.Body) : Parser Unit := do
  match body with
  | .affine impl generators relations base maps =>
    implementation impl
    if ← acceptWord "Affine" then
      let some p := base | throw "expected the base of an affine space"
      unless relations.isEmpty && maps.isEmpty do throw "unexpected equations on an affine space"
      symbol '('
      reference p
      symbol ','
      expect (.dimension generators.length)
      symbol ')'
      names generators
    else
      word "spec"
      names generators
      if ← acceptWord "relations" then
        symbol '('
        separated relations polynomial ')'
      else unless relations.isEmpty do throw "missing physical affine relations"
      if let some p := base then
        word "over"
        reference p
        if ← acceptWord "by" then bindings maps
        else unless maps.isEmpty do throw "missing affine base bindings"
      else unless maps.isEmpty do throw "affine bindings need a base"
  | .affineFiber impl left right via =>
    implementation impl
    word "fiber"
    symbol '('
    reference left
    symbol ','
    reference right
    symbol ')'
    if let some (forward, inverse) := via then
      word "via"
      bindings forward
      word "inverse"
      bindings inverse
  | .affineLocalization impl subject element inverse =>
    implementation impl
    word "localize"
    symbol '('
    reference subject
    symbol ','
    polynomial element
    symbol ')'
    word "inverse"
    matchingName component inverse
  | .smoothAffine impl dimension coordinates =>
    implementation impl
    word "Affine"
    symbol '('
    expect (.dimension dimension)
    symbol ')'
    names coordinates
  | _ => throw "expected a presented or smooth affine declaration"

private def declaration (d : Source.Declaration) : Parser Unit := do
  match d.body with
  | .morphism family indices definition =>
    word "morphism"
    word d.name
    morphism family indices definition
  | body =>
    word "affine"
    word d.name
    object body
  symbol ';'

def applies (d : Source.Declaration) : Bool :=
  match d.body with
  | .affine .. | .affineFiber .. | .affineLocalization .. | .smoothAffine .. | .morphism .. => true
  | _ => false

def check (file : File) (first : Token) (d : Source.Declaration) : Except Diagnostic Unit := do
  let error := fun span msg => (⟨"E_AFFINE_SOURCE", msg, span, []⟩ : Diagnostic)
  unless first.kind matches .word "indexed" do throw (error first.span "expected an indexed geometry declaration")
  match ((declaration d).run file).run first.after with
  | .ok _ after =>
    unless sameSpan file first after d.span do throw (error first.span "affine declaration span differs from its source")
  | .error msg at_ =>
    throw (error ((file.next at_).toOption.map (·.span) |>.getD first.span) msg)

end VastitasKernel.AffineDeclarationText
