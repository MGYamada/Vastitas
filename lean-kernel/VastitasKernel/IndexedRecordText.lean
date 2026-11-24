import VastitasKernel.AffineDeclarationText

set_option autoImplicit false

/-! Physical operands of indexed records. Paths include their source spans.
Ordered polynomial terms are checked before elaboration. -/
namespace VastitasKernel.IndexedRecordText
open SourceText AssemblyText Indexed AffineDeclarationText

private def named (name : String) : Parser Unit := word name *> symbol '='
private def field (name : String) : Parser Unit := symbol ',' *> named name
private def coordinate (expected : String) := matchingName (component >>= coordinateTail) expected
private def call (name : String) := word name *> symbol '('

private def sameNatural (expected : Nat) : Parser Unit := do
  let start ← get
  unless (← natural) == expected do
    set start
    throw "integer field differs from its source"

private def factor (entry : Source.Path × Int) : Parser Unit := do
  reference entry.1
  let start ← get
  let actual ← if ← acceptSymbol '^' then do
    let negative ← acceptSymbol '-'
    let n ← natural
    pure (if negative then -(Int.ofNat n) else Int.ofNat n)
  else pure 1
  unless actual == entry.2 do
    set start
    throw "dimension or scale exponent differs from its source"

private def dimension (factors : List (Source.Path × Int)) : Parser Unit := do
  if factors.isEmpty then symbol '1'
  for (f, i) in factors.zipIdx do
    if i != 0 then symbol '*'
    factor f

private def fraction : Parser Source.PolyExpr := do
  call "frac"
  let negative ← acceptSymbol '-'
  let n ← natural
  symbol ','
  let denom ← natural
  symbol ')'
  return .fraction (if negative then -(Int.ofNat n) else Int.ofNat n) denom

private def fractionAhead : Parser Bool := do
  let t ← next
  unless t.kind matches .word "frac" do return false
  return ((← read).next t.after).toOption.any (fun token => token.kind matches .symbol '(')

private def unsignedLiteral : Parser Source.PolyExpr := do
  if ← fractionAhead then fraction else return .natural (← natural)

private def rational (expected : Source.PolyExpr) : Parser Unit := do
  let start ← get
  let negative ← acceptSymbol '-'
  let v ← unsignedLiteral
  unless samePoly Limits.algebraNesting (if negative then .neg v else v) expected do
    set start
    throw "rational literal differs from its source"

/-- The wire stores the product of literal coefficients separately from
ordered scale paths. Their relative positions in the source may interleave. -/
private def monomial (entry : Source.ScaleMonomial) : Parser Unit := do
  let start ← get
  let negative ← acceptSymbol '-'
  let mut coeffs := []
  let mut remaining := entry.factors
  let f ← read
  for _ in [:f.remaining (← get) + 1] do
    let t ← next
    if (match t.kind with | .symbol ch => ch.isDigit | _ => false) || (← fractionAhead) then
      coeffs := (← unsignedLiteral) :: coeffs
    else
      let expected :: rest := remaining | throw "unexpected scale in physical Gram entry"
      factor expected
      remaining := rest
    unless ← acceptSymbol '*' do break
  unless remaining.isEmpty do throw "missing scale in physical Gram entry"
  let coeff : Source.PolyExpr := match coeffs with
    | [] => .natural 1 | [one] => one | _ => .product coeffs.reverse
  unless samePoly Limits.algebraNesting (if negative then .neg coeff else coeff) entry.coefficient do
    set start
    throw "physical Gram coefficient differs from its source"

private def coordinatePath (item : String × Source.Path) : Parser Unit := do
  coordinate item.1
  symbol ':'
  reference item.2

private def physical (entries : Source.PhysicalGram) : Parser Unit := do
  match entries with
  | .euclidean => word "euclidean"
  | .normalized scales => call "normalized" *> separated scales coordinatePath ')'
  | .gram rows =>
    call "gram"
    separated rows (fun row => symbol '(' *> separated row monomial ')') ')'

private def recordText (expected : String) : Parser Unit := do
  let f ← read
  let t ← next
  let start : String.Pos.Raw := ⟨t.span.start - f.base⟩
  unless (t.kind matches .opaque) && start.extract f.text t.after.pos == "\"" ++ expected ++ "\"" do
    throw "recorded text differs from its source"
  set t.after

private def measured (m : Source.SourceMeasured) : Parser Unit := do
  call "measured"
  rational m.value
  field "u"
  rational m.uncertainty
  symbol ')'

private def point (p : Source.SourcePoint) : Parser Unit := do
  symbol '('
  for (name, v) in p.coordinates do
    coordinate name
    symbol '='
    rational v
    symbol ','
  named "value"
  measured p.measured
  symbol ')'

private def projectiveChart (c : Source.SourceChart) : Parser Unit := do
  call "chart"
  reference c.chart
  symbol ','
  matchingName component c.dehomogenized
  symbol ','
  polynomial c.image
  symbol ')'
  word "inverse"
  bindings c.inverse

def grammar : Source.Body → Option (Parser Unit)
  | .quantity factors => some (symbol '=' *> dimension factors)
  | .scale quantity mag => some (symbol '=' *> polynomial mag *> word "of" *> reference quantity)
  | .reading family indices quantities => some do
    application family indices
    symbol '('
    separated quantities coordinatePath ')'
  | .physicalMetric family indices metric reading value entries => some do
    application family indices
    call "interpret"
    reference metric
    field "reading"
    reference reading
    symbol ','
    physical entries
    if let some factors := value then
      field "value"
      dimension factors
    symbol ')'
  | .freeModule family indices basis => some do
    application family indices
    call "basis"
    separated basis (matchingName component) ')'
  | .endomorphism family indices module rows symmetric => some do
    application family indices
    word "rows"
    matrix rows
    word "of"
    reference module
    if symmetric then word "symmetric"
  | .spectrum family indices endomorphism fiber => some do
    application family indices
    call "eigen"
    reference endomorphism
    symbol ','
    matchingName component fiber
    symbol ')'
  | .branch family indices spectrum localize witness exponent => some do
    application family indices
    call "simple"
    reference spectrum
    field "localize"
    polynomial localize
    field "witness"
    polynomial witness
    field "exponent"
    sameNatural exponent
    symbol ')'
  | .transitionAverage family indices branch source target numerator denominator => some do
    application family indices
    call "transition_average"
    reference branch
    field "from"
    matchingName component source
    field "to"
    matchingName component target
    symbol ')'
    symbol '='
    call "ratio"
    polynomial numerator
    symbol ','
    polynomial denominator
    symbol ')'
  | .convention .hbarOne => some (symbol '=' *> word "hbar_one")
  | .model family indices hamiltonian reading convention prepare observe predicts regime => some do
    application family indices
    call "model"
    named "hamiltonian"
    reference hamiltonian
    field "reading"
    reference reading
    field "convention"
    reference convention
    field "prepare"
    matchingName component prepare
    field "observe"
    matchingName component observe
    field "predicts"
    reference predicts
    field "regime"
    call "assume"
    recordText regime
    symbol ')'
    symbol ')'
  | .calibration family indices parameters method ref revision => some do
    application family indices
    call "calibrate"
    for param in parameters do
      coordinate param.coordinate
      symbol '='
      measured param.measured
      symbol ','
    named "method"
    word (match method with | .typeA => "type_a" | .typeB => "type_b")
    field "reference"
    recordText ref
    field "revision"
    recordText revision
    symbol ')'
  | .dataset family indices model calibration coverage points => some do
    application family indices
    call "measure"
    named "model"
    reference model
    field "calibration"
    reference calibration
    field "coverage"
    rational coverage
    field "points"
    symbol '['
    separated points point ']'
    symbol ')'
  | .comparison family indices dataset calibration fingerprint verdict => some do
    application family indices
    call "compare"
    reference dataset
    field "calibration"
    reference calibration
    field "fingerprint"
    recordText fingerprint
    field "verdict"
    word (match verdict with | .consistent => "consistent" | .inconsistent => "inconsistent")
    symbol ')'
  | .glued impl opens forward inverse => some do
    implementation impl
    call "glue"
    separated opens reference ')'
    word "by"
    bindings forward
    word "inverse"
    bindings inverse
  | .cover object opens coefficients => some do
    symbol '='
    call "cover"
    separated (object :: opens) reference ')'
    call "by"
    separated coefficients polynomial ')'
  | .separated glued inverse witness => some do
    symbol '='
    call "separated"
    reference glued
    symbol ')'
    word "by"
    bindings [(inverse, witness)]
  | .manifold glued dim inverse witness => some do
    symbol '='
    call "manifold"
    reference glued
    symbol ','
    sameNatural dim
    symbol ')'
    word "by"
    bindings [(inverse, witness)]
  | .projective glued homogeneous charts => some do
    symbol '='
    call "proj"
    reference glued
    symbol ')'
    names homogeneous
    for c in charts do projectiveChart c
  | _ => none

def check (file : File) (first : Token) (keyword : String) (d : Source.Declaration) : Except Diagnostic Unit :=
  let parser : Parser Unit := do
    let some fields := grammar d.body | throw "no physical record grammar for this indexed declaration"
    fields
  checkAt file first d.span (word keyword *> word d.name *> parser *> symbol ';') "E_MODULE_SOURCE" keyword

end VastitasKernel.IndexedRecordText
