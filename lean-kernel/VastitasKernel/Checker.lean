import VastitasKernel.Core
import VastitasKernel.Dependency
import VastitasKernel.TypeAudit

namespace VastitasKernel
namespace Checker.Internal

structure Binding where
  name : String
  symbol : Nat
  ty : Ty
  objectRef : Option ObjectRef := none
  deriving Inhabited

structure Signature where
  id : Nat
  raw : RawFunction
  params : List Binding
  result : Ty
  deriving Inhabited

abbrev Signatures := Std.HashMap String Signature

structure Result where
  term : Term
  deriving Inhabited

def Result.objectRef (result : Result) : Option ObjectRef := result.term.resultType.objectRef

def Binding.resultType (binding : Binding) : ResultType := ⟨binding.ty, binding.objectRef⟩

def Binding.checked (binding : Binding) : CheckedParam := ⟨binding.symbol, binding.resultType⟩

-- Provenance is diagnostic metadata. It never authorizes endpoint equality or
-- changes the nominal identity carried by the independently checked types.
structure ObjectOrigin where
  bindingName : Option String := none
  span : Span
  reason : String
  deriving Inhabited

structure CheckerState where
  nextSymbol : Nat := 1
  origins : Std.HashMap ObjectRef ObjectOrigin := {}
  deriving Inhabited

abbrev Context := List Binding
abbrev CheckM := StateT CheckerState (Except Diagnostic)

def fail (span : Span) (code message : String)
    (notes : List DiagnosticNote := []) : CheckM α :=
  throw { code, message, span, notes }

abbrev checkingBudgetExceeded (span : Span) : CheckM α :=
  fail span "E_LIMIT" "function exceeds the checking budget of 4096 units (statements, nesting, and call arguments)"

def fresh : CheckM Nat := do
  let state ← get
  set { state with nextSymbol := state.nextSymbol + 1 }
  pure state.nextSymbol

def rememberObject (ref : ObjectRef) (span : Span) (reason : String)
    (bindingName : Option String := none) : CheckM Unit :=
  modify fun state => { state with origins := state.origins.insert ref { bindingName, span, reason } }

def freshObject (base : BaseKind) (span : Span) (reason : String) : CheckM ObjectRef := do
  let ref := ObjectRef.local base (← fresh)
  rememberObject ref span reason
  pure ref

def nameObject (ref : ObjectRef) (name : String) : CheckM Unit := do
  let state ← get
  if let some origin := state.origins[ref]? then
    if origin.bindingName.isNone then
      set { state with origins := state.origins.insert ref { origin with bindingName := some name } }

def objectLabel (ctx : Context) (ref : ObjectRef) : CheckM String := do
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

def typeLabel (ctx : Context) : Ty → CheckM String
  | .point target source => do
      pure s!"Point<{← objectLabel ctx target}, {← objectLabel ctx source}>"
  | .morphism source target => do
      pure s!"Morphism<{← objectLabel ctx source}, {← objectLabel ctx target}>"
  | ty => pure ty.label

def objectNotes (ctx : Context) (refs : List ObjectRef) : CheckM (List DiagnosticNote) := do
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

def reserved : List String :=
  ["Affine", "Base", "origin", "id", "compose", "apply", "dimension", "int",
   "QQ", "CInfReal", "Nat", "Int", "Bool", "Unit", "Scheme", "CInfScheme",
   "Point", "Morphism", "Pointed", "Fn", "fn", "let", "if", "else", "pack", "unpack", "as", "true", "false",
   "return", "while", "for", "loop", "mut"]

def validName (name : String) : Bool :=
  let chars := name.toList
  match chars with
  | [] => false
  | first :: rest => (first.isAlpha && first.toNat < 128 || first == '_') &&
      rest.all (fun c => (c.isAlphanum && c.toNat < 128) || c == '_')

def checkName (name : String) (span : Span) : CheckM Unit := do
  unless validName name do fail span "E_NAME" s!"invalid identifier '{name}'"
  if reserved.contains name then fail span "E_RESERVED" s!"'{name}' is reserved"

def checkNewBinding (ctx : Context) (name : String) (span : Span) : CheckM Unit := do
  checkName name span
  if ctx.any (fun b => b.name == name) then
    fail span "E_DUPLICATE" s!"binding '{name}' is already in scope; shadowing is not allowed"

def getBinding (ctx : Context) (name : String) (span : Span) : CheckM Binding :=
  match ctx.find? (fun b => b.name == name) with
  | some b => pure b
  | none => fail span "E_NAME" s!"unbound name '{name}'"

def parseBase (name : String) (span : Span) : CheckM BaseKind :=
  match name with
  | "QQ" => pure .qq
  | "CInfReal" => pure .cinfReal
  | _ => fail span "E_BASE" s!"unsupported coefficient base '{name}'; expected QQ or CInfReal"

def resolveIndex (ctx : Context) (index : RawIndex) (span : Span) : CheckM ObjectRef := do
  match index with
  | .base ring => pure (.base (← parseBase ring span))
  | .name name =>
    let binding ← getBinding ctx name span
    match binding.objectRef with
    | some r => pure r
    | none => fail span "E_INDEX" s!"'{name}' is not a geometric object usable as a type index"

def resolveType (ctx : Context) (raw : RawType) (span : Span) : CheckM Ty := do
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

def expectedResult (ctx : Context) (expected : Option Ty) (r : Result) (span : Span) : CheckM Result := do
  if let some ty := expected then
    unless r.term.ty == ty do
      fail span "E_TYPE" s!"expected {← typeLabel ctx ty}, found {← typeLabel ctx r.term.ty}"
        (← objectNotes ctx (ty.refs ++ r.term.ty.refs))
  pure r

def objectOf (ctx : Context) (r : Result) (span : Span) : CheckM ObjectRef :=
  match r.objectRef with
  | some obj => pure obj
  | none => do
      fail span "E_TYPE" s!"expected a geometric object, found {← typeLabel ctx r.term.ty}"
        (← objectNotes ctx r.term.ty.refs)

def liftRule (ctx : Context) (rule : Except String Ty) (span : Span)
    (details : String) (refs : List ObjectRef) : CheckM Ty :=
  match rule with
  | .ok ty => pure ty
  | .error e => do fail span "E_ENDPOINT" s!"{e}: {details}" (← objectNotes ctx refs)

def checkEscape (ctx : Context) (r : Result) (span : Span) : CheckM Unit := do
  let allowed := ctx.flatMap fun binding => binding.objectRef.toList ++ binding.ty.refs
  match checkScope allowed r.term.ty with
  | .ok () => pure ()
  | .error ref =>
    let hint := match r.term.ty with
      | .point .. => "return its object and point together with pack"
      | _ => "keep the morphism's endpoint objects in the enclosing scope"
    fail span "E_ESCAPE" s!"{← typeLabel ctx r.term.ty} refers to local object {← objectLabel ctx ref}; {hint}"
      (← objectNotes ctx [ref])

def arity (name : String) (args : List RawExpr) (n : Nat) (span : Span) : CheckM Unit := do
  unless args.length == n do
    let noun := if n == 1 then "argument" else "arguments"
    fail span "E_ARITY" s!"{name} expects {n} {noun}, found {args.length}"

def rawRing (e : RawExpr) : CheckM BaseKind :=
  match e with
  | .variable name s => parseBase name s
  | _ => fail e.span "E_BASE" "coefficient base must be the static name QQ or CInfReal"

def isInteger (t : Ty) : Bool := t == .nat || t == .int

def literalLike : RawExpr → Bool
  | .integer .. => true
  | .unary "-" (.integer ..) _ => true
  | _ => false

def blockLiteralLike : RawBlock → Bool
  | .mk _ result _ => literalLike result

mutual
  def checkExpr : Nat → Signatures → Context → RawExpr → Option Ty → CheckM Result
    | 0, _, _, e, _ => checkingBudgetExceeded e.span
    | fuel + 1, signatures, ctx, e, expected => do
      let span := e.span
      let result ← match e with
      | .integer value _ => do
        unless !value.isEmpty && value.toList.all (fun c => c >= '0' && c <= '9') do
          fail span "E_LITERAL" "integer IR literal must contain only decimal digits"
        let ty := match expected with | some .nat => Ty.nat | _ => Ty.int
        let some n := value.toNat? | fail span "E_LITERAL" "invalid decimal integer"
        pure { term := .literal ty n }
      | .boolean value _ => pure { term := .boolean value }
      | .unit _ => pure { term := .unit }
      | .variable name _ => do
        let b ← getBinding ctx name span
        pure { term := .var b.symbol b.resultType }
      | .unary op operand _ => do
        let (operation, ty) ← match op with
          | "-" => pure (UnaryOp.neg, Ty.int)
          | "!" => pure (UnaryOp.not, Ty.bool)
          | _ => fail span "E_OPERATOR" s!"unsupported unary operator '{op}'"
        let arg ← checkExpr fuel signatures ctx operand (some ty)
        pure { term := .unary operation arg.term ty }
      | .binary rawOp left right _ => do
        let some op := BinaryOp.ofString? rawOp
          | fail span "E_OPERATOR" s!"unsupported binary operator '{rawOp}'"
        if op == .and || op == .or then
          let a ← checkExpr fuel signatures ctx left (some .bool)
          let b ← checkExpr fuel signatures ctx right (some .bool)
          pure { term := .binary op a.term b.term .bool }
        else
          let arithmetic := [BinaryOp.add, .sub, .mul].contains op
          let hint := if arithmetic then expected.filter isInteger else none
          let (a, b) ← if literalLike left && !literalLike right && hint.isNone then do
            let b ← checkExpr fuel signatures ctx right none
            let a ← checkExpr fuel signatures ctx left (some b.term.ty)
            pure (a, b)
          else do
            let a ← checkExpr fuel signatures ctx left hint
            let b ← checkExpr fuel signatures ctx right (some a.term.ty)
            pure (a, b)
          if op == .eq || op == .ne then
            unless isInteger a.term.ty || a.term.ty == .bool || a.term.ty == .unit do
              fail span "E_OPERATOR" "equality is available only for scalar values; geometric identities are abstract"
          else
            unless isInteger a.term.ty do
              fail span "E_OPERATOR" s!"operator '{rawOp}' requires Nat or Int, found {a.term.ty.label}"
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
        pure { term := .branch condition.term yes.term no.term ⟨yes.term.ty, objectRef⟩ }
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

  def checkCall : Nat → Signatures → Context → String → List RawExpr → Span → CheckM Result
    | 0, _, _, _, _, span => checkingBudgetExceeded span
    | fuel + 1, signatures, ctx, name, args, span => do
      match name with
      | "int" =>
        arity name args 1 span
        let value ← checkExpr fuel signatures ctx args[0]! (some .nat)
        pure { term := .builtin .int [value.term] ⟨.int, none⟩ }
      | "Affine" =>
        arity name args 2 span
        let base ← rawRing args[0]!
        let dimension ← checkExpr fuel signatures ctx args[1]! (some .nat)
        let ref ← freshObject base span "Affine"
        pure { term := .builtin (.affine base) [dimension.term] ⟨.object base, some ref⟩ }
      | "Base" =>
        arity name args 1 span
        let base ← rawRing args[0]!
        let ref := ObjectRef.base base
        rememberObject ref span "Base"
        pure { term := .builtin (.base base) [] ⟨.object base, some ref⟩ }
      | "origin" | "id" | "dimension" =>
        arity name args 1 span
        let object ← checkExpr fuel signatures ctx args[0]! none
        let ref ← objectOf ctx object span
        let ty := if name == "origin" then Ty.point ref (.base ref.baseKind)
          else if name == "id" then .morphism ref ref else .nat
        let op := if name == "origin" then BuiltinOp.origin
          else if name == "id" then .identity else .dimension
        pure { term := .builtin op [object.term] ⟨ty, none⟩ }
      | "compose" | "apply" =>
        arity name args 2 span
        let a ← checkExpr fuel signatures ctx args[0]! none
        let b ← checkExpr fuel signatures ctx args[1]! none
        let ty ← liftRule ctx (if name == "compose" then checkCompose a.term.ty b.term.ty else checkApply a.term.ty b.term.ty)
          span s!"{← typeLabel ctx a.term.ty} and {← typeLabel ctx b.term.ty}" (a.term.ty.refs ++ b.term.ty.refs)
        let op := if name == "compose" then BuiltinOp.compose else .apply
        pure { term := .builtin op [a.term, b.term] ⟨ty, none⟩ }
      | _ =>
        let some signature := signatures[name]?
          | fail span "E_NAME" s!"unknown function '{name}'"
        arity name args signature.params.length span
        let (terms, substitutions) ← checkArguments fuel signatures ctx signature.params args [] span
        let ty := signature.result.rename substitutions
        let objectRef ← match ty with
          | .object base => pure (some (← freshObject base span s!"function call '{name}'"))
          | _ => pure none
        pure { term := .call signature.id terms substitutions ⟨ty, objectRef⟩ }

  def checkArguments : Nat → Signatures → Context → List Binding → List RawExpr →
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

  def checkBlock : Nat → Signatures → Context → RawBlock → Option Ty → CheckM Result
    | 0, _, _, .mk _ _ span, _ => checkingBudgetExceeded span
    | fuel + 1, signatures, ctx, .mk statements result span, expected => do
      let checked ← checkStatements fuel signatures ctx statements result expected
      checkEscape ctx checked span
      pure checked

  def checkStatements : Nat → Signatures → Context → List RawStmt → RawExpr → Option Ty → CheckM Result
    | 0, _, _, _, result, _ => checkingBudgetExceeded result.span
    | fuel + 1, signatures, ctx, [], result, expected => checkExpr fuel signatures ctx result expected
    | fuel + 1, signatures, ctx, .letE name annotation value span :: rest, result, expected => do
      checkNewBinding ctx name span
      if signatures.contains name then
        fail span "E_SHADOW" s!"binding '{name}' conflicts with a function name"
      let annotation ← annotation.mapM (fun ty => resolveType ctx ty span)
      let value ← checkExpr fuel signatures ctx value annotation
      let symbol ← fresh
      if let some ref := value.objectRef then nameObject ref name
      let binding : Binding := { name, symbol, ty := value.term.ty, objectRef := value.objectRef }
      let body ← checkStatements fuel signatures (binding :: ctx) rest result expected
      pure { term := .letE symbol value.term body.term }
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
      pure { term := .unpack objectSymbol pointSymbol value.term body.term }
end

/-- Resolve parameter annotations in declaration order, retaining the complete
preceding context for dependent indices. Kept separate for correspondence proofs. -/
def prepareParameters (params : List Binding) : List RawParam → CheckM (List Binding)
  | [] => pure params
  | param :: rest => do
    checkNewBinding params param.name param.span
    let ty ← resolveType params param.ty param.span
    let symbol ← fresh
    let objectRef := match ty with | .object base => some (.local base symbol) | _ => none
    if let some ref := objectRef then rememberObject ref param.span "parameter" (some param.name)
    prepareParameters (params ++ [{ name := param.name, symbol, ty, objectRef }]) rest

def prepareSignature (raw : RawFunction) : CheckM Signature := do
  checkName raw.name raw.span
  let id ← fresh
  let params ← prepareParameters [] raw.params
  let result ← resolveType params raw.returnType raw.span
  if raw.name == "main" && (!params.isEmpty || result != .int) then
    fail raw.span "E_MAIN" "entry point must have signature fn main() -> Int"
  pure { id, raw, params, result }

def checkFunction (signatures : Signatures) (signature : Signature) : CheckM CheckedFunction := do
  let body ← checkBlock 4096 signatures signature.params signature.raw.body (some signature.result)
  if body.term.generatedLetCount > generatedLetLimit then
    fail signature.raw.span "E_LIMIT" s!"function exceeds the generated-let budget of {generatedLetLimit}; let costs 1 and unpack costs 3"
  pure {
    id := signature.id
    name := signature.raw.name
    params := signature.params.map Binding.checked
    returnType := signature.result
    body := body.term
    span := signature.raw.span }

def calls : Term → List Nat := Term.callIds

/-- A residual Kahn graph has an outgoing dependency at every remaining vertex.
Following those edges eventually repeats a vertex; only the repeated suffix is
the cycle, excluding callers that merely depend on it. -/
def dependencyCycle (dependencies : Array (Array Nat)) (waiting : Array Nat)
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

def sortFunctionIndices (functions : List CheckedFunction) : CheckM (List Nat) := do
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
  let mut sorted : Array Nat := #[]
  while cursor < ready.size do
    let i := ready[cursor]!
    cursor := cursor + 1
    sorted := sorted.push i
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
      s!"recursive call cycle {String.intercalate " → " names} is not supported"
  pure sorted.toList

/-- Reordering can only select declarations from the original checked list.
The independently proved source correspondence does not need to trust the
imperative queue implementation for this provenance invariant. -/
def selectFunctions (functions : Array CheckedFunction) : List Nat → CheckM (List CheckedFunction)
  | [] => pure []
  | index :: rest => do
    let some function := functions[index]?
      | fail {} "E_INTERNAL_GRAPH" "dependency order contains an invalid function index"
    pure (function :: (← selectFunctions functions rest))

def sortFunctions (functions : List CheckedFunction) : CheckM (List CheckedFunction) := do
  let order ← sortFunctionIndices functions
  let sorted ← selectFunctions functions.toArray order
  unless sorted.length == functions.length do
    fail {} "E_INTERNAL_GRAPH" "dependency order changed the function count"
  pure sorted

def checkModuleImpl (raw : RawModule) (requireMain : Bool) : CheckM CheckedModule := do
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

end Checker.Internal

def checkModule (raw : RawModule) (requireMain : Bool := false) : Except Diagnostic CertifiedModule := do
  let checked := (← (Checker.Internal.checkModuleImpl raw requireMain).run {}).1
  unless Dependency.auditModule checked do
    throw { code := "E_INTERNAL_GRAPH", message := "checked IR failed dependency-order audit" }
  unless Typing.auditModule checked do
    throw { code := "E_INTERNAL_TYPE", message := "checked IR failed declarative typing audit" }
  certifyModule checked

end VastitasKernel
