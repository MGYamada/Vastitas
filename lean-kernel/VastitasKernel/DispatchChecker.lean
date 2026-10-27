import VastitasKernel.Program
import VastitasKernel.Dispatch
import VastitasKernel.Checker

/-! Stage 1 is a typed lowering adapter. The Stage 0 elaborator and its proofs
remain unchanged; every ordinary and monomorphized body is checked by that core
after generic calls have been resolved by the finite dispatch checker. -/
namespace VastitasKernel.DispatchChecker
open Checker.Internal

def privatePrefix := "__vastitas_"

def sourceReserved : List String :=
  ["generic", "method", "domain", "requires", "Any", "Number"]

def checkSourceName (name : String) (span : Span) : CheckM Unit := do
  checkName name span
  if name.startsWith privatePrefix || sourceReserved.contains name then
    fail span "E_RESERVED" s!"'{name}' is reserved for the compiler or static dispatch"

def checkReference (name : String) (span : Span) : CheckM Unit := do
  if name.startsWith privatePrefix then
    fail span "E_RESERVED" s!"'{privatePrefix}' is reserved for compiler-generated names"

def validateIndex (index : RawIndex) (span : Span) : CheckM Unit :=
  match index with
  | .name name => checkReference name span
  | .base _ => pure ()

def validateType (ty : RawType) (span : Span) : CheckM Unit := do
  match ty with
  | .named name => checkReference name span
  | .point target source | .morphism target source =>
    validateIndex target span
    validateIndex source span
  | .pointed _ _ => pure ()

def checkBinder (globals : Std.HashSet String) (name : String) (span : Span) : CheckM Unit := do
  checkSourceName name span
  if globals.contains name then
    fail span "E_SHADOW" s!"binding '{name}' conflicts with a function or generic name"

mutual
  def validateExpr : Nat → Std.HashSet String → RawExpr → CheckM Unit
    | 0, _, expr => fail expr.span "E_LIMIT" "source validation exceeds the supported nesting limit"
    | fuel + 1, globals, expr => do
      match expr with
      | .integer .. | .boolean .. | .unit .. => pure ()
      | .variable name span => checkReference name span
      | .call name args span =>
        checkReference name span
        args.forM (validateExpr fuel globals)
      | .unary _ value _ => validateExpr fuel globals value
      | .binary _ left right _ | .pack left right _ =>
        validateExpr fuel globals left
        validateExpr fuel globals right
      | .ite condition yes no _ =>
        validateExpr fuel globals condition
        validateBlock fuel globals yes
        validateBlock fuel globals no
      | .block body _ => validateBlock fuel globals body
  def validateBlock : Nat → Std.HashSet String → RawBlock → CheckM Unit
    | 0, _, .mk _ _ span => fail span "E_LIMIT" "source validation exceeds the supported nesting limit"
    | fuel + 1, globals, .mk statements result _ => do
      for statement in statements do
        match statement with
        | .letE name annotation value span =>
          checkBinder globals name span
          annotation.forM (fun ty => validateType ty span)
          validateExpr fuel globals value
        | .unpack value scheme point span =>
          checkBinder globals scheme span
          checkBinder globals point span
          validateExpr fuel globals value
      validateExpr fuel globals result
end

def scalar (raw : RawType) (span : Span) : CheckM Nat :=
  match raw with
  | .named name =>
    match Dispatch.parseScalar name with
    | some code => pure code
    | none => fail span "E_TYPE" s!"dispatch domains and method results require Nat, Int, Bool, or Unit; found {name}"
  | _ => fail span "E_TYPE" "dispatch domains and method results require a concrete scalar type"

def selector (raw : RawType) (span : Span) : CheckM Nat :=
  match raw with
  | .named name =>
    match Dispatch.parseSelector name with
    | some code => pure code
    | none => fail span "E_TYPE" s!"unsupported dispatch selector '{name}'"
  | _ => fail span "E_TYPE" "method selectors require a scalar, Number, or Any"

def keyLabel (key : Dispatch.Key) : String :=
  "(" ++ String.intercalate ", " (key.map Dispatch.nominalName) ++ ")"

def monoName (method : Nat) (key : Dispatch.Key) : String :=
  s!"{privatePrefix}m{method}_" ++ String.intercalate "_" (key.map toString)

/-- The executable dispatch acceptance equation is retained as erased evidence.
It connects every selected table to the oracle's finite-selection theorem. -/
structure Family where
  raw : RawGeneric
  domain : List Dispatch.Key
  methods : List Dispatch.Method
  checked : Dispatch.Checked
  accepted : Dispatch.check raw.params.length domain methods = .ok checked

abbrev Families := Std.HashMap String Family

private def requirementLabel (requirements : List Dispatch.Capability) : String :=
  if requirements.contains .hasOrder then "HasOrder"
  else if requirements.contains .hasEq then "HasEq" else ""

private def signatureLabel (name : String) (method : Dispatch.NormalizedMethod) : String :=
  name ++ keyLabel method.selectors ++
    (if method.requirements.isEmpty then "" else s!" requires ({requirementLabel method.requirements})")

private def diagnosticCandidate (program : RawProgram) (id : Nat) : Option (RawMethod × Dispatch.NormalizedMethod) := do
  let raw ← program.methods[id]?
  let selectors ← raw.params.mapM fun param => match param.ty with
    | .named name => Dispatch.parseSelector name
    | _ => none
  let requirements ← raw.requirements.mapM Dispatch.parseCapability
  pure (raw, { id, selectors, requirements := Dispatch.normalizeCapabilities requirements })

private def ambiguityNotes (program : RawProgram) (generic : RawGeneric) (ids : List Nat) : List DiagnosticNote := Id.run do
  let candidates := ids.filterMap (diagnosticCandidate program)
  let mut notes := []
  for (raw, candidate) in candidates do
    let mut message := s!"candidate method `{signatureLabel generic.name candidate}` declared here"
    for (_, other) in candidates do
      if candidate.id != other.id then
        let narrower := Dispatch.nominalBelow Dispatch.publicHierarchy candidate.selectors other.selectors
        let reverse := Dispatch.nominalBelow Dispatch.publicHierarchy other.selectors candidate.selectors
        let missing := other.requirements.filter (!candidate.requirements.contains ·)
        let extra := candidate.requirements.filter (!other.requirements.contains ·)
        if narrower && !reverse then message := message ++ "; has narrower selectors"
        if !narrower then message := message ++ "; selectors are not narrower in every argument"
        if !extra.isEmpty then message := message ++ s!"; has stronger requirements ({requirementLabel extra})"
        if !missing.isEmpty then message := message ++ s!"; does not require {requirementLabel missing}"
    notes := notes ++ [{ message, span := raw.span }]
  if let some (_, first) := candidates.head? then
    let mut meet := some first
    for (_, candidate) in candidates.tail do
      meet := meet.bind fun current => do
        let selectors ← (current.selectors.zip candidate.selectors).mapM fun (a, b) =>
          if Dispatch.publicHierarchy.subtype a b then some a
          else if Dispatch.publicHierarchy.subtype b a then some b else none
        pure { current with
          selectors := selectors
          requirements := Dispatch.normalizeCapabilities (current.requirements ++ candidate.requirements) }
    if let some resolving := meet then
      notes := notes ++ [{
        span := generic.span
        message := s!"help: declare `{signatureLabel generic.name resolving}` to resolve this key; recheck the entire family after editing" }]
  return notes

def dispatchDiagnostic (program : RawProgram) (generic : RawGeneric) (error : Dispatch.Error) : Diagnostic :=
  let code := match error.code with
    | "E_DISPATCH_ARITY" => "E_ARITY"
    | "E_DISPATCH_SELECTOR" => "E_TYPE"
    | "E_DISPATCH_CAPABILITY" | "E_DISPATCH_UNREALIZABLE" => "E_CAPABILITY"
    | "E_DISPATCH_DUPLICATE_ID" | "E_DISPATCH_DUPLICATE" => "E_DUPLICATE"
    | "E_DISPATCH_LIMIT" => "E_LIMIT"
    | other => other
  let notes := if error.code == "E_DISPATCH_AMBIGUOUS" then ambiguityNotes program generic error.methods
    else error.methods.filterMap fun id =>
      (program.methods[id]?).map fun method =>
        { message := s!"candidate method for generic '{generic.name}' declared here", span := method.span : DiagnosticNote }
  { code, span := generic.span
    message := s!"generic '{generic.name}': {error.message}" ++
      (error.key.map (fun key => s!" at key {keyLabel key}")).getD ""
    notes }

def prepareFamilies (program : RawProgram) : CheckM (List Family) := do
  let mut result := []
  for generic in program.generics do
    let domain ← generic.domain.mapM (fun key => key.mapM (fun ty => scalar ty generic.span))
    let mut seen : Std.HashSet Dispatch.Key := {}
    for key in domain do
      if seen.contains key then fail generic.span "E_DUPLICATE" s!"duplicate domain key {keyLabel key}"
      seen := seen.insert key
    let mut methods := []
    for (id, method) in program.methods.zipIdx.map (fun pair => (pair.2, pair.1)) do
      if method.name == generic.name then
        let selectors ← method.params.mapM fun param => selector param.ty param.span
        let _ ← scalar method.returnType method.span
        methods := methods ++ [{ id, selectors, requirements := method.requirements }]
    match accepted : Dispatch.check generic.params.length domain methods with
    | .error error => throw (dispatchDiagnostic program generic error)
    | .ok checked => result := result ++ [{ raw := generic, domain, methods, checked, accepted }]
  pure result

def validateProgram (program : RawProgram) : CheckM Unit := do
  unless program.version == 2 do fail {} "E_PROTOCOL" "unsupported IR protocol version; expected 2"
  let mut globals : Std.HashSet String := {}
  for function in program.functions do
    checkSourceName function.name function.span
    if globals.contains function.name then fail function.span "E_DUPLICATE" s!"duplicate function '{function.name}'"
    globals := globals.insert function.name
  let mut genericNames : Std.HashSet String := {}
  for generic in program.generics do
    checkSourceName generic.name generic.span
    if generic.name == "main" then fail generic.span "E_MAIN" "main must be an ordinary fn main() -> Int"
    if globals.contains generic.name then fail generic.span "E_DUPLICATE" s!"duplicate function or generic '{generic.name}'"
    globals := globals.insert generic.name
    genericNames := genericNames.insert generic.name
  for generic in program.generics do
    let mut params : Std.HashSet String := {}
    for param in generic.params do
      checkBinder globals param.name param.span
      if params.contains param.name then fail param.span "E_DUPLICATE" s!"duplicate generic parameter '{param.name}'"
      params := params.insert param.name
  for function in program.functions do
    for param in function.params do
      checkBinder globals param.name param.span
      validateType param.ty param.span
    validateType function.returnType function.span
    validateBlock 512 globals function.body
  for method in program.methods do
    checkSourceName method.name method.span
    unless genericNames.contains method.name do
      fail method.span "E_NAME" s!"method refers to undeclared generic '{method.name}'"
    for param in method.params do
      checkBinder globals param.name param.span
    validateBlock 512 globals method.body

def instantiate (program : RawProgram) (families : List Family) : CheckM (List RawFunction) := do
  let mut functions : Array RawFunction := #[]
  for family in families do
    for (id, key) in family.checked.applicablePairs do
      let some method := program.methods[id]?
        | fail family.raw.span "E_INTERNAL_DISPATCH" "dispatch table contains an unknown method identity"
      let params := (method.params.zip key).map fun (param, code) =>
        { param with ty := .named (Dispatch.nominalName code) }
      functions := functions.push {
        name := monoName id key
        params
        returnType := method.returnType
        body := method.body
        span := method.span }
  pure functions.toList

def instantiationNotes (program : RawProgram) (families : List Family) : Std.HashMap String DiagnosticNote := Id.run do
  let mut notes := {}
  for family in families do
    for (id, key) in family.checked.applicablePairs do
      if let some method := program.methods[id]? then
        notes := notes.insert (monoName id key) {
          message := s!"while checking method '{method.name}' for concrete key {keyLabel key}"
          span := method.span }
  return notes

def withInstantiationNote (note : Option DiagnosticNote) (action : CheckM α) : CheckM α := do
  try action catch diagnostic => throw { diagnostic with notes := diagnostic.notes ++ note.toList }

/-- A successful lookup carries the actual checked row equation. -/
structure Target (family : Family) (key : Dispatch.Key) where
  method : Nat
  admitted : key ∈ family.domain
  selected : family.checked.winner key = some method

def selectTarget (family : Family) (key : Dispatch.Key) (span : Span) : CheckM (Target family key) := do
  if admitted : key ∈ family.domain then
    match selected : family.checked.winner key with
    | none => fail span "E_INTERNAL_DISPATCH" "validated dispatch domain has no selected method"
    | some method => pure { method, admitted, selected }
  else
    fail span "E_DISPATCH_DOMAIN" s!"generic '{family.raw.name}' does not admit call key {keyLabel key}"

def scalarKey (value : Result) (span : Span) : CheckM Nat :=
  match value.term.ty with
  | .nat => pure 0 | .int => pure 1 | .bool => pure 2 | .unit => pure 3
  | ty => fail span "E_TYPE" s!"generic dispatch requires concrete scalar arguments; found {ty.label}"

mutual
  def lowerExpr : Nat → Families → Signatures → Context → RawExpr → CheckM RawExpr
    | 0, _, _, _, expr => checkingBudgetExceeded expr.span
    | fuel + 1, families, signatures, ctx, expr => do
      match expr with
      | .integer .. | .boolean .. | .unit .. | .variable .. => pure expr
      | .unary op value span => pure (.unary op (← lowerExpr fuel families signatures ctx value) span)
      | .binary op left right span =>
        pure (.binary op (← lowerExpr fuel families signatures ctx left) (← lowerExpr fuel families signatures ctx right) span)
      | .pack scheme point span =>
        pure (.pack (← lowerExpr fuel families signatures ctx scheme) (← lowerExpr fuel families signatures ctx point) span)
      | .ite condition yes no span =>
        pure (.ite (← lowerExpr fuel families signatures ctx condition)
          (← lowerBlock fuel families signatures ctx yes) (← lowerBlock fuel families signatures ctx no) span)
      | .block body span => pure (.block (← lowerBlock fuel families signatures ctx body) span)
      | .call name args span =>
        let args ← args.mapM (lowerExpr fuel families signatures ctx)
        match families[name]? with
        | none => pure (.call name args span)
        | some family =>
          arity name args family.raw.params.length span
          -- Dispatch never infers from the expected return type or a chosen
          -- method parameter. In particular, a bare integer defaults to Int.
          let key ← args.mapM fun arg => do
            scalarKey (← checkExpr 4096 signatures ctx arg none) arg.span
          let target ← selectTarget family key span
          pure (.call (monoName target.method key) args span)
  def lowerBlock : Nat → Families → Signatures → Context → RawBlock → CheckM RawBlock
    | 0, _, _, _, .mk _ _ span => checkingBudgetExceeded span
    | fuel + 1, families, signatures, ctx, .mk statements result span => do
      let (statements, ctx) ← lowerStatements fuel families signatures ctx statements span
      pure (.mk statements (← lowerExpr fuel families signatures ctx result) span)
  def lowerStatements : Nat → Families → Signatures → Context → List RawStmt → Span → CheckM (List RawStmt × Context)
    | 0, _, _, _, _, span => checkingBudgetExceeded span
    | _ + 1, _, _, ctx, [], _ => pure ([], ctx)
    | fuel + 1, families, signatures, ctx, .letE name annotation raw span :: rest, blockSpan => do
      checkNewBinding ctx name span
      let raw ← lowerExpr fuel families signatures ctx raw
      let expected ← annotation.mapM (fun ty => resolveType ctx ty span)
      let value ← checkExpr 4096 signatures ctx raw expected
      let symbol ← fresh
      if let some ref := value.objectRef then nameObject ref name
      let binding : Binding := { name, symbol, ty := value.term.ty, objectRef := value.objectRef }
      let (rest, ctx) ← lowerStatements fuel families signatures (binding :: ctx) rest blockSpan
      pure (.letE name annotation raw span :: rest, ctx)
    | fuel + 1, families, signatures, ctx, .unpack raw scheme point span :: rest, blockSpan => do
      checkNewBinding ctx scheme span
      checkNewBinding ctx point span
      if scheme == point then fail span "E_DUPLICATE" "unpack needs two distinct binding names"
      let raw ← lowerExpr fuel families signatures ctx raw
      let value ← checkExpr 4096 signatures ctx raw none
      let .pointed base := value.term.ty
        | fail span "E_TYPE" s!"unpack requires Pointed, found {value.term.ty.label}"
      let objectSymbol ← fresh
      let pointSymbol ← fresh
      let obj := ObjectRef.local base objectSymbol
      rememberObject obj span "unpack" (some scheme)
      let objectBinding : Binding := { name := scheme, symbol := objectSymbol, ty := .object base, objectRef := some obj }
      let pointBinding : Binding := { name := point, symbol := pointSymbol, ty := unpackedPointType base objectSymbol }
      let (rest, ctx) ← lowerStatements fuel families signatures (pointBinding :: objectBinding :: ctx) rest blockSpan
      pure (.unpack raw scheme point span :: rest, ctx)
end

def lowerProgramImpl (program : RawProgram) : CheckM RawModule := do
  validateProgram program
  if program.generics.isEmpty then
    return { version := 1, file := program.file, functions := program.functions }
  let families ← prepareFamilies program
  let instances ← instantiate program families
  let notes := instantiationNotes program families
  let functions := program.functions ++ instances
  let signatureList ← functions.mapM prepareSignature
  let signatures : Signatures := signatureList.foldl (fun table signature => table.insert signature.raw.name signature) {}
  let families : Families := families.foldl (fun table family => table.insert family.raw.name family) {}
  let functions ← signatureList.mapM fun signature =>
    withInstantiationNote notes[signature.raw.name]? do
      let body ← lowerBlock 4096 families signatures signature.params signature.raw.body
      let raw := { signature.raw with body }
      -- Check each monomorphized body before discarding its diagnostic context.
      -- The full lowered module is still checked independently afterward.
      if notes.contains raw.name then
        let _ ← checkFunction signatures { signature with raw }
      pure raw
  pure { version := 1, file := program.file, functions }

def lowerProgram (program : RawProgram) : Except Diagnostic RawModule := do
  pure (← (lowerProgramImpl program).run {}).1

/-- Private names never become the user-facing cycle's method names. -/
def describeDiagnostic (program : RawProgram) (diagnostic : Diagnostic) : Diagnostic := Id.run do
  let render (token : String) : String := Id.run do
    if !token.startsWith s!"{privatePrefix}m" then return token
    let parts := (token.drop (privatePrefix.length + 1)).toString.splitOn "_"
    let idText := parts.head!
    let some id := idText.toNat? | return token
    let some method := program.methods[id]? | return token
    let codes := parts.tail!
    let codes := if codes == [""] then [] else codes
    let some key := codes.mapM String.toNat? | return token
    if key.length != method.params.length || key.any (· > 3) || monoName id key != token then
      return token
    return s!"{method.name}{keyLabel key}"
  let mut message := ""
  let mut token := ""
  for char in diagnostic.message.toList do
    if char.isAlphanum || char == '_' then
      token := token.push char
    else
      message := (message ++ render token).push char
      token := ""
  return { diagnostic with message := message ++ render token }

end VastitasKernel.DispatchChecker

namespace VastitasKernel

/-- Public protocol-2 checking always ends at the proved core checker, including
its independent full typing/freshness and dependency-order audits. -/
def checkProgram (program : RawProgram) (requireMain : Bool := false) : Except Diagnostic CertifiedModule := do
  let raw ← DispatchChecker.lowerProgram program
  match checkModule raw requireMain with
  | .ok certified => pure certified
  | .error diagnostic => throw (DispatchChecker.describeDiagnostic program diagnostic)

end VastitasKernel
