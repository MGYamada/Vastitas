import VastitasKernel.Core

namespace VastitasKernel

private structure Binding where
  name : String
  symbol : Nat
  ty : Ty
  objectRef : Option ObjectRef := none
  deriving Inhabited

private structure Signature where
  id : Nat
  raw : RawFunction
  params : List Binding
  result : Ty
  deriving Inhabited

private abbrev Signatures := Std.HashMap String Signature

private structure Result where
  term : Term
  objectRef : Option ObjectRef := none
  deriving Inhabited

-- Provenance is diagnostic metadata. It never authorizes endpoint equality or
-- changes the nominal identity carried by the independently checked types.
private structure ObjectOrigin where
  bindingName : Option String := none
  span : Span
  reason : String
  deriving Inhabited

private structure CheckerState where
  nextSymbol : Nat := 1
  origins : Std.HashMap ObjectRef ObjectOrigin := {}
  deriving Inhabited

private abbrev Context := List Binding
private abbrev CheckM := StateT CheckerState (Except Diagnostic)

private def fail (span : Span) (code message : String)
    (notes : List DiagnosticNote := []) : CheckM α :=
  throw { code, message, span, notes }

private def fresh : CheckM Nat := do
  let state ← get
  set { state with nextSymbol := state.nextSymbol + 1 }
  pure state.nextSymbol

private def rememberObject (ref : ObjectRef) (span : Span) (reason : String)
    (bindingName : Option String := none) : CheckM Unit :=
  modify fun state => { state with origins := state.origins.insert ref { bindingName, span, reason } }

private def freshObject (base : BaseKind) (span : Span) (reason : String) : CheckM ObjectRef := do
  let ref := ObjectRef.local base (← fresh)
  rememberObject ref span reason
  pure ref

private def nameObject (ref : ObjectRef) (name : String) : CheckM Unit := do
  let state ← get
  if let some origin := state.origins[ref]? then
    if origin.bindingName.isNone then
      set { state with origins := state.origins.insert ref { origin with bindingName := some name } }

private def objectLabel (ctx : Context) (ref : ObjectRef) : CheckM String := do
  if let .base _ := ref then return ref.label
  let origin := (← get).origins[ref]?
  if let some name := origin.bind (·.bindingName) then
    if ctx.any (fun binding => binding.name == name && binding.objectRef == some ref) then
      return name
  if let some binding := ctx.find? (fun binding => binding.objectRef == some ref) then
    return binding.name
  if let some origin := origin then
    if let some name := origin.bindingName then return name
    return s!"{ref.baseKind.settingName} from {origin.reason} at {origin.span.line}:{origin.span.column}"
  pure ref.label

private def typeLabel (ctx : Context) : Ty → CheckM String
  | .point target source => do
      pure s!"Point<{← objectLabel ctx target}, {← objectLabel ctx source}>"
  | .morphism source target => do
      pure s!"Morphism<{← objectLabel ctx source}, {← objectLabel ctx target}>"
  | ty => pure ty.label

private def objectNotes (ctx : Context) (refs : List ObjectRef) : CheckM (List DiagnosticNote) := do
  let mut seen : Std.HashSet ObjectRef := {}
  let mut notes : Array DiagnosticNote := #[]
  for ref in refs do
    unless seen.contains ref do
      seen := seen.insert ref
      -- Canonical bases have no generative identity to disambiguate. Their
      -- canonical label is enough; do not attach an unrelated Base occurrence.
      if let .local .. := ref then
        if let some origin := (← get).origins[ref]? then
          notes := notes.push {
            message := s!"object {← objectLabel ctx ref} was introduced here by {origin.reason}"
            span := origin.span }
  pure notes.toList

private def reserved : List String :=
  ["Affine", "Base", "origin", "id", "compose", "apply", "dimension", "int",
   "QQ", "CInfReal", "Nat", "Int", "Bool", "Unit", "Scheme", "CInfScheme",
   "Point", "Morphism", "Pointed", "fn", "let", "if", "else", "pack", "unpack", "as", "true", "false",
   "return", "while", "for", "loop", "mut"]

private def validName (name : String) : Bool :=
  let chars := name.toList
  match chars with
  | [] => false
  | first :: rest => (first.isAlpha && first.toNat < 128 || first == '_') &&
      rest.all (fun c => (c.isAlphanum && c.toNat < 128) || c == '_')

private def checkName (name : String) (span : Span) : CheckM Unit := do
  unless validName name do fail span "E_NAME" s!"invalid identifier '{name}'"
  if reserved.contains name then fail span "E_NAME" s!"'{name}' is reserved"

private def checkNewBinding (ctx : Context) (name : String) (span : Span) : CheckM Unit := do
  checkName name span
  if ctx.any (fun b => b.name == name) then
    fail span "E_DUPLICATE" s!"binding '{name}' is already in scope; Stage 0 does not allow shadowing"

private def getBinding (ctx : Context) (name : String) (span : Span) : CheckM Binding :=
  match ctx.find? (fun b => b.name == name) with
  | some b => pure b
  | none => fail span "E_UNBOUND" s!"unbound name '{name}'"

private def parseBase (name : String) (span : Span) : CheckM BaseKind :=
  match name with
  | "QQ" => pure .qq
  | "CInfReal" => pure .cinfReal
  | _ => fail span "E_BASE" s!"unsupported coefficient base '{name}'; expected QQ or CInfReal"

private def resolveIndex (ctx : Context) (index : RawIndex) (span : Span) : CheckM ObjectRef := do
  match index with
  | .base ring => pure (.base (← parseBase ring span))
  | .name name =>
    let binding ← getBinding ctx name span
    match binding.objectRef with
    | some r => pure r
    | none => fail span "E_INDEX" s!"'{name}' is not a geometric object usable as a type index"

private def resolveType (ctx : Context) (raw : RawType) (span : Span) : CheckM Ty := do
  let ty ← match raw with
    | .named "Nat" => pure .nat
    | .named "Int" => pure .int
    | .named "Bool" => pure .bool
    | .named "Unit" => pure .unit
    | .named "Scheme" => pure (.object .qq)
    | .named "CInfScheme" => pure (.object .cinfReal)
    | .named name => fail span "E_TYPE" s!"unsupported type '{name}'"
    | .point target source => pure (.point (← resolveIndex ctx target span) (← resolveIndex ctx source span))
    | .morphism source target => pure (.morphism (← resolveIndex ctx source span) (← resolveIndex ctx target span))
    | .pointed setting ring => do
      let base ← parseBase ring span
      unless setting == base.settingName do
        fail span "E_BASE" s!"{setting} is incompatible with base {ring}; expected {base.settingName}"
      pure (.pointed base)
  unless decide ty.WellFormed do
    fail span "E_BASE" s!"incompatible geometric settings or bases in {← typeLabel ctx ty}"
      (← objectNotes ctx ty.refs)
  pure ty

private def expectedResult (ctx : Context) (expected : Option Ty) (r : Result) (span : Span) : CheckM Result := do
  if let some ty := expected then
    unless r.term.ty == ty do
      fail span "E_TYPE" s!"expected {← typeLabel ctx ty}, found {← typeLabel ctx r.term.ty}"
        (← objectNotes ctx (ty.refs ++ r.term.ty.refs))
  pure r

private def objectOf (ctx : Context) (r : Result) (span : Span) : CheckM ObjectRef :=
  match r.objectRef with
  | some obj => pure obj
  | none => do
      fail span "E_TYPE" s!"expected a geometric object, found {← typeLabel ctx r.term.ty}"
        (← objectNotes ctx r.term.ty.refs)

private def liftRule (ctx : Context) (rule : Except String Ty) (span : Span)
    (details : String) (refs : List ObjectRef) : CheckM Ty :=
  match rule with
  | .ok ty => pure ty
  | .error e => do fail span "E_ENDPOINT" s!"{e}: {details}" (← objectNotes ctx refs)

private def checkEscape (ctx : Context) (r : Result) (span : Span) : CheckM Unit := do
  let allowed := ctx.flatMap fun binding => binding.objectRef.toList ++ binding.ty.refs
  match checkScope allowed r.term.ty with
  | .ok () => pure ()
  | .error ref =>
    let hint := match r.term.ty with
      | .point .. => "return its object and point together with pack"
      | _ => "keep the morphism's endpoint objects in the enclosing scope"
    fail span "E_ESCAPE" s!"{← typeLabel ctx r.term.ty} refers to local object {← objectLabel ctx ref}; {hint}"
      (← objectNotes ctx [ref])

private def arity (name : String) (args : List RawExpr) (n : Nat) (span : Span) : CheckM Unit := do
  unless args.length == n do
    let noun := if n == 1 then "argument" else "arguments"
    fail span "E_ARITY" s!"{name} expects {n} {noun}, found {args.length}"

private def rawRing (e : RawExpr) : CheckM BaseKind :=
  match e with
  | .variable name s => parseBase name s
  | _ => fail e.span "E_BASE" "coefficient base must be the static name QQ or CInfReal"

private def isInteger (t : Ty) : Bool := t == .nat || t == .int

private def literalLike : RawExpr → Bool
  | .integer .. => true
  | .unary "-" (.integer ..) _ => true
  | _ => false

private def blockLiteralLike : RawBlock → Bool
  | .mk _ result _ => literalLike result

mutual
  private def checkExpr : Nat → Signatures → Context → RawExpr → Option Ty → CheckM Result
    | 0, _, _, e, _ => fail e.span "E_LIMIT" "program exceeds Stage 0 checking depth limit"
    | fuel + 1, signatures, ctx, e, expected => do
      let span := e.span
      let result ← match e with
      | .integer value _ => do
        unless !value.isEmpty && value.toList.all (fun c => c >= '0' && c <= '9') do
          fail span "E_LITERAL" "integer IR literal must contain only decimal digits"
        let ty := match expected with | some .nat => Ty.nat | _ => Ty.int
        let some n := value.toNat? | fail span "E_LITERAL" "invalid decimal integer"
        pure { term := .literal ty (toString n) }
      | .boolean value _ => pure { term := .boolean value }
      | .unit _ => pure { term := .unit }
      | .variable name _ => do
        let b ← getBinding ctx name span
        pure { term := .var b.symbol b.ty, objectRef := b.objectRef }
      | .unary op operand _ => do
        let ty ← match op with
          | "-" => pure Ty.int
          | "!" => pure Ty.bool
          | _ => fail span "E_OPERATOR" s!"unsupported unary operator '{op}'"
        let arg ← checkExpr fuel signatures ctx operand (some ty)
        pure { term := .unary op arg.term ty }
      | .binary op left right _ => do
        if op == "&&" || op == "||" then
          let a ← checkExpr fuel signatures ctx left (some .bool)
          let b ← checkExpr fuel signatures ctx right (some .bool)
          pure { term := .binary op a.term b.term .bool }
        else
          unless ["+", "-", "*", "==", "!=", "<", "<=", ">", ">="].contains op do
            fail span "E_OPERATOR" s!"unsupported binary operator '{op}'"
          let arithmetic := ["+", "-", "*"].contains op
          let hint := if arithmetic then expected.filter isInteger else none
          let (a, b) ← if literalLike left && !literalLike right && hint.isNone then do
            let b ← checkExpr fuel signatures ctx right none
            let a ← checkExpr fuel signatures ctx left (some b.term.ty)
            pure (a, b)
          else do
            let a ← checkExpr fuel signatures ctx left hint
            let b ← checkExpr fuel signatures ctx right (some a.term.ty)
            pure (a, b)
          if op == "==" || op == "!=" then
            unless isInteger a.term.ty || a.term.ty == .bool || a.term.ty == .unit do
              fail span "E_OPERATOR" "equality is available only for scalar values; geometric identities are abstract"
          else
            unless isInteger a.term.ty do
              fail span "E_OPERATOR" s!"operator '{op}' requires Nat or Int, found {a.term.ty.label}"
          let ty := if arithmetic then a.term.ty else .bool
          pure { term := .binary op a.term b.term ty }
      | .ite condition yes no _ => do
        let condition ← checkExpr fuel signatures ctx condition (some .bool)
        let (yes, no) ← if expected.isNone && blockLiteralLike yes && !blockLiteralLike no then do
          let no ← checkBlock fuel signatures ctx no none
          let yes ← checkBlock fuel signatures ctx yes (some no.term.ty)
          pure (yes, no)
        else do
          let yes ← checkBlock fuel signatures ctx yes expected
          let no ← checkBlock fuel signatures ctx no (some yes.term.ty)
          pure (yes, no)
        let objectRef ← match yes.term.ty with
          | .object base =>
            if yes.objectRef == no.objectRef then pure yes.objectRef
            else pure (some (← freshObject base span "if merge of distinct objects"))
          | _ => pure none
        pure { term := .branch condition.term yes.term no.term yes.term.ty, objectRef }
      | .block body _ => checkBlock fuel signatures ctx body expected
      | .pack scheme point _ => do
        let scheme ← checkExpr fuel signatures ctx scheme none
        let obj ← objectOf ctx scheme span
        let point ← checkExpr fuel signatures ctx point none
        let _ ← liftRule ctx (checkPack obj point.term.ty) span
          s!"object {← objectLabel ctx obj}, point {← typeLabel ctx point.term.ty}" (obj :: point.term.ty.refs)
        pure { term := .pack obj.baseKind scheme.term point.term }
      | .call name args _ => checkCall fuel signatures ctx name args span
      expectedResult ctx expected result span

  private def checkCall : Nat → Signatures → Context → String → List RawExpr → Span → CheckM Result
    | 0, _, _, _, _, span => fail span "E_LIMIT" "program exceeds Stage 0 checking depth limit"
    | fuel + 1, signatures, ctx, name, args, span => do
      match name with
      | "int" =>
        arity name args 1 span
        let value ← checkExpr fuel signatures ctx args[0]! (some .nat)
        pure { term := .builtin "int" none [value.term] .int }
      | "Affine" =>
        arity name args 2 span
        let base ← rawRing args[0]!
        let dimension ← checkExpr fuel signatures ctx args[1]! (some .nat)
        let ref ← freshObject base span "Affine"
        pure { term := .builtin "Affine" (some base) [dimension.term] (.object base), objectRef := some ref }
      | "Base" =>
        arity name args 1 span
        let base ← rawRing args[0]!
        let ref := ObjectRef.base base
        rememberObject ref span "Base"
        pure { term := .builtin "Base" (some base) [] (.object base), objectRef := some ref }
      | "origin" | "id" | "dimension" =>
        arity name args 1 span
        let object ← checkExpr fuel signatures ctx args[0]! none
        let ref ← objectOf ctx object span
        let ty := if name == "origin" then Ty.point ref (.base ref.baseKind)
          else if name == "id" then .morphism ref ref else .nat
        pure { term := .builtin name none [object.term] ty }
      | "compose" | "apply" =>
        arity name args 2 span
        let a ← checkExpr fuel signatures ctx args[0]! none
        let b ← checkExpr fuel signatures ctx args[1]! none
        let ty ← liftRule ctx (if name == "compose" then checkCompose a.term.ty b.term.ty else checkApply a.term.ty b.term.ty)
          span s!"{← typeLabel ctx a.term.ty} and {← typeLabel ctx b.term.ty}" (a.term.ty.refs ++ b.term.ty.refs)
        pure { term := .builtin name none [a.term, b.term] ty }
      | _ =>
        let some signature := signatures[name]?
          | fail span "E_UNBOUND" s!"unknown function '{name}'"
        arity name args signature.params.length span
        let (terms, substitutions) ← checkArguments fuel signatures ctx signature.params args [] span
        let ty := signature.result.rename substitutions
        let objectRef ← match ty with
          | .object base => pure (some (← freshObject base span s!"function call '{name}'"))
          | _ => pure none
        pure { term := .call signature.id terms ty, objectRef }

  private def checkArguments : Nat → Signatures → Context → List Binding → List RawExpr →
      List (ObjectRef × ObjectRef) → Span → CheckM (List Term × List (ObjectRef × ObjectRef))
    | 0, _, _, _, _, _, span => fail span "E_LIMIT" "too many function arguments"
    | _ + 1, _, _, [], [], substitutions, _ => pure ([], substitutions)
    | fuel + 1, signatures, ctx, param :: params, arg :: args, substitutions, span => do
      let value ← checkExpr fuel signatures ctx arg (some (param.ty.rename substitutions))
      let substitutions ← match param.objectRef with
        | some original => do
          let target ← objectOf ctx value arg.span
          pure ((original, target) :: substitutions)
        | none => pure substitutions
      let (rest, substitutions) ← checkArguments fuel signatures ctx params args substitutions span
      pure (value.term :: rest, substitutions)
    | _, _, _, _, _, _, span => fail span "E_ARITY" "argument count differs from function signature"

  private def checkBlock : Nat → Signatures → Context → RawBlock → Option Ty → CheckM Result
    | 0, _, _, .mk _ _ span, _ => fail span "E_LIMIT" "program exceeds Stage 0 checking depth limit"
    | fuel + 1, signatures, ctx, .mk statements result span, expected => do
      let checked ← checkStatements fuel signatures ctx statements result expected
      checkEscape ctx checked span
      pure checked

  private def checkStatements : Nat → Signatures → Context → List RawStmt → RawExpr → Option Ty → CheckM Result
    | 0, _, _, _, result, _ => fail result.span "E_LIMIT" "too many statements in a block"
    | fuel + 1, signatures, ctx, [], result, expected => checkExpr fuel signatures ctx result expected
    | fuel + 1, signatures, ctx, .letE name annotation value span :: rest, result, expected => do
      checkNewBinding ctx name span
      if signatures.contains name then
        fail span "E_DUPLICATE" s!"binding '{name}' conflicts with a function name"
      let annotation ← annotation.mapM (fun ty => resolveType ctx ty span)
      let value ← checkExpr fuel signatures ctx value annotation
      let symbol ← fresh
      if let some ref := value.objectRef then nameObject ref name
      let binding : Binding := { name, symbol, ty := value.term.ty, objectRef := value.objectRef }
      let body ← checkStatements fuel signatures (binding :: ctx) rest result expected
      pure { term := .letE symbol value.term body.term, objectRef := body.objectRef }
    | fuel + 1, signatures, ctx, .unpack value scheme point span :: rest, result, expected => do
      checkNewBinding ctx scheme span
      checkNewBinding ctx point span
      if signatures.contains scheme || signatures.contains point then
        fail span "E_DUPLICATE" "unpack binding conflicts with a function name"
      if scheme == point then fail span "E_DUPLICATE" "unpack needs two distinct binding names"
      let value ← checkExpr fuel signatures ctx value none
      let .pointed base := value.term.ty
        | fail span "E_TYPE" s!"unpack requires Pointed, found {← typeLabel ctx value.term.ty}"
            (← objectNotes ctx value.term.ty.refs)
      let objectSymbol ← fresh
      let pointSymbol ← fresh
      let obj := ObjectRef.local base objectSymbol
      rememberObject obj span "unpack" (some scheme)
      let objectBinding : Binding := { name := scheme, symbol := objectSymbol, ty := .object base, objectRef := some obj }
      let pointBinding : Binding := { name := point, symbol := pointSymbol, ty := unpackedPointType base objectSymbol }
      let body ← checkStatements fuel signatures (pointBinding :: objectBinding :: ctx) rest result expected
      pure { term := .unpack objectSymbol pointSymbol value.term body.term, objectRef := body.objectRef }
end

private def prepareSignature (raw : RawFunction) : CheckM Signature := do
  checkName raw.name raw.span
  let id ← fresh
  let mut params : List Binding := []
  for param in raw.params do
    checkNewBinding params param.name param.span
    let ty ← resolveType params param.ty param.span
    let symbol ← fresh
    let objectRef := match ty with | .object base => some (.local base symbol) | _ => none
    if let some ref := objectRef then rememberObject ref param.span "parameter" (some param.name)
    params := params ++ [{ name := param.name, symbol, ty, objectRef }]
  let result ← resolveType params raw.returnType raw.span
  if raw.name == "main" && (!params.isEmpty || result != .int) then
    fail raw.span "E_MAIN" "entry point must have signature fn main() -> Int"
  pure { id, raw, params, result }

private def checkFunction (signatures : Signatures) (signature : Signature) : CheckM CheckedFunction := do
  let body ← checkBlock 4096 signatures signature.params signature.raw.body (some signature.result)
  if body.term.generatedLetCount > generatedLetLimit then
    fail signature.raw.span "E_LIMIT" s!"function exceeds the generated-let budget of {generatedLetLimit}; let costs 1 and unpack costs 3"
  pure {
    id := signature.id
    name := signature.raw.name
    params := signature.params.map (fun p => (p.symbol, p.ty))
    returnType := signature.result
    body := body.term
    span := signature.raw.span }

private def calls : Term → List Nat
  | .call id args _ => id :: args.flatMap calls
  | .builtin _ _ args _ => args.flatMap calls
  | .unary _ arg _ => calls arg
  | .binary _ left right _ => calls left ++ calls right
  | .branch condition yes no _ => calls condition ++ calls yes ++ calls no
  | .pack _ scheme point => calls scheme ++ calls point
  | .letE _ value body | .unpack _ _ value body => calls value ++ calls body
  | _ => []

/-- A residual Kahn graph has an outgoing dependency at every remaining vertex.
Following those edges eventually repeats a vertex; only the repeated suffix is
the cycle, excluding callers that merely depend on it. -/
private def dependencyCycle (dependencies : Array (Array Nat)) (waiting : Array Nat)
    (start : Nat) : CheckM (List Nat) := do
  let mut positions : Std.HashMap Nat Nat := {}
  let mut path : Array Nat := #[]
  let mut current := start
  for _ in [:dependencies.size + 1] do
    if let some offset := positions[current]? then
      return path.toList.drop offset ++ [current]
    positions := positions.insert current path.size
    path := path.push current
    let some next := dependencies[current]!.find? (fun i => waiting[i]! > 0)
      | fail {} "E_INTERNAL_GRAPH" "remaining function has no unresolved dependency"
    current := next
  fail {} "E_INTERNAL_GRAPH" "failed to find a cycle in the remaining call graph"

private def sortFunctions (functions : List CheckedFunction) : CheckM (List CheckedFunction) := do
  let functions := functions.toArray
  let mut positions : Std.HashMap Nat Nat := {}
  for i in [:functions.size] do
    positions := positions.insert functions[i]!.id i
  let mut dependencies : Array (Array Nat) := Array.replicate functions.size #[]
  let mut dependents : Array (Array Nat) := Array.replicate functions.size #[]
  let mut waiting := Array.replicate functions.size 0
  for i in [:functions.size] do
    let mut seen : Std.HashSet Nat := {}
    for id in calls functions[i]!.body do
      let some dependency := positions[id]?
        | fail functions[i]!.span "E_INTERNAL_GRAPH" s!"unknown checked function ID {id}"
      unless seen.contains dependency do
        seen := seen.insert dependency
        dependencies := dependencies.modify i (·.push dependency)
        dependents := dependents.modify dependency (·.push i)
    waiting := waiting.set! i dependencies[i]!.size
  -- All queue insertions follow source/edge order, never hash-map iteration.
  let mut ready : Array Nat := #[]
  for i in [:functions.size] do
    if waiting[i]! == 0 then ready := ready.push i
  let mut cursor := 0
  let mut sorted : Array CheckedFunction := #[]
  while cursor < ready.size do
    let i := ready[cursor]!
    cursor := cursor + 1
    sorted := sorted.push functions[i]!
    for dependent in dependents[i]! do
      waiting := waiting.modify dependent (· - 1)
      if waiting[dependent]! == 0 then ready := ready.push dependent
  if sorted.size != functions.size then
    let some start := (List.range functions.size).find? (fun i => waiting[i]! > 0)
      | fail {} "E_INTERNAL_GRAPH" "missing unresolved function"
    let cycle ← dependencyCycle dependencies waiting start
    let representative := functions[cycle.headD start]!
    let names := cycle.map (fun i => functions[i]!.name)
    fail representative.span "E_RECURSION"
      s!"recursive call cycle {String.intercalate " → " names} is not supported in Stage 0"
  pure sorted.toList

private def checkModuleImpl (raw : RawModule) (requireMain : Bool) : CheckM CheckedModule := do
  unless raw.version == 1 do fail {} "E_PROTOCOL" "unsupported IR protocol version; expected 1"
  let mut names : Std.HashSet String := {}
  for f in raw.functions do
    if names.contains f.name then fail f.span "E_DUPLICATE" s!"duplicate function '{f.name}'"
    names := names.insert f.name
  for f in raw.functions do
    for p in f.params do
      if names.contains p.name then
        fail p.span "E_DUPLICATE" s!"parameter '{p.name}' conflicts with a function name"
  let signatureList ← raw.functions.mapM prepareSignature
  let signatures : Signatures := signatureList.foldl (fun table s => table.insert s.raw.name s) {}
  let checked ← signatureList.mapM (checkFunction signatures)
  let sorted ← sortFunctions checked
  let mainId := (sorted.find? (fun f => f.name == "main")).map (·.id)
  if requireMain && mainId.isNone then fail {} "E_MAIN" "build requires fn main() -> Int"
  pure { functions := sorted, mainId }

def checkModule (raw : RawModule) (requireMain : Bool := false) : Except Diagnostic CertifiedModule := do
  let checked := (← (checkModuleImpl raw requireMain).run {}).1
  certifyModule checked

end VastitasKernel
