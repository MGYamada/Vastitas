import VastitasKernel.FunctionLift

namespace VastitasKernel.Surface
open Checker.Internal
open DispatchChecker

structure Target where
  name : String
  ty : TypeExpr
  abstractTarget : Bool := false
  deriving Repr, BEq, Inhabited

structure Value where
  raw : RawExpr
  target : Option Target := none
  deriving Inhabited

structure Instance where
  key : String
  name : String
  target : Option Target
  deriving Inhabited

/-- Recorded concrete higher-order selections are independently audited against
backend declarations. Abstract signature probes never enter this ledger. -/
structure StaticCall where
  target : String
  signature : TypeExpr
  bindings : List (TypeExpr × Target) := []
  deriving Inhabited

structure Lowered where
  module : RawModule
  definitions : List Function
  calls : List StaticCall
  deriving Inhabited

def StaticCallsValid (lowered : Lowered) : Prop :=
  ∀ call ∈ lowered.calls,
    (∃ definition ∈ lowered.definitions, definition.name = call.target ∧ definition.type = call.signature) ∧
    ∀ binding ∈ call.bindings, binding.1 = binding.2.ty ∧
      ∃ definition ∈ lowered.definitions, definition.name = binding.2.name ∧ definition.type = binding.2.ty

instance (lowered : Lowered) : Decidable (StaticCallsValid lowered) := by
  unfold StaticCallsValid
  infer_instance

structure State where
  definitions : List Function
  families : Families
  globals : List String
  signatures : Signatures := {}
  instances : List Instance := []
  active : List String := []
  functions : Array RawFunction := #[]
  calls : List StaticCall := []
  nextInstance : Nat := 0
  audit : Bool := false
  deriving Inhabited

abbrev M := StateT State CheckM
abbrev Functions := List (String × Target)

def core (action : CheckM α) : M α := fun state => do
  let value ← action
  pure (value, state)

def error (span : Span) (code message : String) : M α := core (fail span code message)

def data (value : Value) (span : Span) : M RawExpr := do
  if let some target := value.target then
    error span "E_TYPE" s!"expected a data value, found {target.ty.label}"
  else pure value.raw

def definition (name : String) (span : Span) : M Function := do
  match (← get).definitions.find? (·.name == name) with
  | some f => pure f
  | none => error span "E_NAME" s!"unknown function '{name}'"

def sameType (expected actual : TypeExpr) (span : Span) : M Unit := do
  unless expected == actual do
    error span "E_TYPE" s!"expected {expected.label}, found {actual.label}"

def requireTarget (value : Value) (span : Span) : M Target := do
  let some target := value.target
    | error span "E_TYPE" "application requires a Fn value"
  pure target

def bindName (ctx : Context) (functions : Functions) (name : String) (span : Span) : M Unit := do
  core (checkSourceName name span)
  if (← get).globals.contains name then
    error span "E_SHADOW" s!"binding '{name}' conflicts with a function or generic name"
  if functions.any (·.1 == name) then
    error span "E_DUPLICATE" s!"binding '{name}' is already in scope; shadowing is not allowed"
  core (checkNewBinding ctx name span)

def validateType (ty : TypeExpr) (span : Span) : CheckM Unit := do
  match ty with
  | .data raw => DispatchChecker.validateType raw span
  | .function .. =>
    unless ty.callableData do
      fail span "E_TYPE" "Fn signatures support only Nat, Int, Bool, Unit and Fn types"

def validateFunction (f : Function) (globals : List String) : CheckM Unit := do
  let mut names := []
  for param in f.params do
    checkSourceName param.name param.span
    if globals.contains param.name then fail param.span "E_SHADOW" s!"binding '{param.name}' conflicts with a function or generic name"
    if names.contains param.name then fail param.span "E_DUPLICATE" s!"duplicate parameter '{param.name}'"
    names := param.name :: names
    validateType param.ty param.span
  validateType f.result f.span
  if (f.params.any (·.ty.isFunction) || f.result.isFunction) && !f.type.callableData then
    fail f.span "E_TYPE" "higher-order function signatures support only scalars and Fn types"
  if f.name == "main" && (!f.params.isEmpty || !(f.result == .data (.named "Int"))) then
    fail f.span "E_MAIN" "entry point must have signature fn main() -> Int"

private def rawBlock (value : Value) (span : Span) : RawBlock :=
  match value.raw with
  | .block body _ => body
  | raw => .mk [] raw span

/-- Preserve scalar computations even when their resulting function value is erased. -/
def effects (values : List RawExpr) (result : RawExpr) (span : Span) : M RawExpr := do
  let mut statements := []
  for value in values do
    match value with
    | .unit _ => pure ()
    | _ =>
      let id ← core fresh
      statements := statements ++ [.letE s!"__vastitas_effect{id}" none value span]
  if statements.isEmpty then pure result else pure (.block (.mk statements result span) span)

private def probe (ty : TypeExpr) (name : String) (span : Span) : M Value := do
  match ty with
  | .function .. => pure { raw := .unit span, target := some { name, ty, abstractTarget := true } }
  | .data (.named "Bool") => pure { raw := .boolean false span }
  | .data (.named "Unit") => pure { raw := .unit span }
  | .data raw =>
    let id ← core fresh
    let name := s!"__vastitas_probe{id}"
    pure { raw := .block (.mk [.letE name (some raw) (.integer "0" span) span] (.variable name span) span) span }

mutual
  def lowerExpr : Nat → Context → Functions → Expr → M Value
    | 0, _, _, expr => core (checkingBudgetExceeded expr.span)
    | fuel + 1, ctx, functions, expr => do
      match expr with
      | .integer value span => pure { raw := .integer value span }
      | .boolean value span => pure { raw := .boolean value span }
      | .unit span => pure { raw := .unit span }
      | .variable name span =>
        core (checkReference name span)
        if let some (_, target) := functions.find? (·.1 == name) then
          return { raw := .unit span, target := some target }
        if let some f := (← get).definitions.find? (·.name == name) then
          unless f.type.callableData do error span "E_TYPE" "function values require scalar/Fn signatures"
          return { raw := .unit span, target := some { name, ty := f.type } }
        if (← get).families.contains name then error span "E_TYPE" "a generic is not a Fn value; use an explicit ordinary-function wrapper"
        pure { raw := .variable name span }
      | .lambda _ _ _ span => error span "E_INTERNAL_FUNCTION" "lambda was not lifted"
      | .reference name span =>
        let f ← definition name span
        unless f.type.callableData do error span "E_TYPE" "lambda signatures require scalar/Fn types"
        pure { raw := .unit span, target := some { name, ty := f.type } }
      | .call name args span =>
        core (checkReference name span)
        let values ← args.mapM (lowerExpr fuel ctx functions)
        if let some (_, target) := functions.find? (·.1 == name) then
          return ← invokeTarget fuel ctx target values span
        if ctx.any (·.name == name) then error span "E_TYPE" "application requires a Fn value"
        if let some family := (← get).families[name]? then
          let key ← values.mapM fun value => do
            let raw ← data value span
            let result ← core (checkExpr 4096 (← get).signatures ctx raw none)
            core (scalarKey result span)
          let target ← core (selectTarget family key span)
          let f ← definition (monoName target.method key) span
          return ← invokeTarget fuel ctx { name := f.name, ty := f.type } values span
        if let some f := (← get).definitions.find? (·.name == name) then
          return ← invokeTarget fuel ctx { name, ty := f.type } values span
        pure { raw := .call name (← values.mapM (fun value => data value span)) span }
      | .invoke callee args span =>
        let callee ← lowerExpr fuel ctx functions callee
        let target ← requireTarget callee span
        let values ← args.mapM (lowerExpr fuel ctx functions)
        let value ← invokeTarget fuel ctx target values span
        pure { value with raw := ← effects [callee.raw] value.raw span }
      | .unary op operand span =>
        let operand ← lowerExpr fuel ctx functions operand
        pure { raw := .unary op (← data operand span) span }
      | .binary op left right span =>
        let left ← lowerExpr fuel ctx functions left
        let right ← lowerExpr fuel ctx functions right
        pure { raw := .binary op (← data left span) (← data right span) span }
      | .pack scheme point span =>
        let scheme ← lowerExpr fuel ctx functions scheme
        let point ← lowerExpr fuel ctx functions point
        pure { raw := .pack (← data scheme span) (← data point span) span }
      | .block body _ => lowerBlock fuel ctx functions body
      | .ite condition yes no span =>
        let condition ← lowerExpr fuel ctx functions condition
        let condition ← data condition span
        let _ ← core (checkExpr 4096 (← get).signatures ctx condition (some .bool))
        let yes ← lowerBlock fuel ctx functions yes
        let no ← lowerBlock fuel ctx functions no
        let target ← match yes.target, no.target with
          | none, none => pure none
          | some a, some b => do
            sameType a.ty b.ty span
            if a.name == b.name then pure (some a)
            else if (← get).audit && (a.abstractTarget || b.abstractTarget) then
              pure (some { a with abstractTarget := true, name := s!"__vastitas_branch{span.start}" })
            else error span "E_STATIC_CALL" "function-valued branches must resolve to the same static target"
          | _, _ => error span "E_TYPE" "both branches must have the same data or Fn type"
        pure { raw := .ite condition (rawBlock yes span) (rawBlock no span) span, target }
  def lowerBlock : Nat → Context → Functions → Block → M Value
    | 0, _, _, .mk _ _ span => core (checkingBudgetExceeded span)
    | fuel + 1, ctx, functions, .mk statements result span => do
      let (statements, ctx, functions) ← lowerStatements fuel ctx functions statements span
      let value ← lowerExpr fuel ctx functions result
      pure { value with raw := .block (.mk statements value.raw span) span }
  def lowerStatements : Nat → Context → Functions → List Stmt → Span → M (List RawStmt × Context × Functions)
    | 0, _, _, _, span => core (checkingBudgetExceeded span)
    | _ + 1, ctx, functions, [], _ => pure ([], ctx, functions)
    | fuel + 1, ctx, functions, .letE name annotation expr span :: rest, blockSpan => do
      bindName ctx functions name span
      let value ← lowerExpr fuel ctx functions expr
      for ty in annotation do core (validateType ty span)
      let expected ← match value.target, annotation with
        | some target, some ty => do sameType ty target.ty span; pure (some VastitasKernel.Ty.unit)
        | some _, none => pure (some VastitasKernel.Ty.unit)
        | none, some (.function ..) => error span "E_TYPE" "expected a Fn value"
        | none, some (.data raw) => some <$> core (resolveType ctx raw span)
        | none, none => pure none
      let checked ← core (checkExpr 4096 (← get).signatures ctx value.raw expected)
      let symbol ← core fresh
      if let some ref := checked.objectRef then core (nameObject ref name)
      let binding : Checker.Internal.Binding := { name, symbol, ty := checked.term.ty, objectRef := checked.objectRef }
      let functions := match value.target with | some target => (name, target) :: functions | none => functions
      let (tail, ctx, functions) ← lowerStatements fuel (binding :: ctx) functions rest blockSpan
      let annotation := match value.target with | some _ => some (.named "Unit") | none => annotation.map TypeExpr.core
      pure (.letE name annotation value.raw span :: tail, ctx, functions)
    | fuel + 1, ctx, functions, .unpack expr scheme point span :: rest, blockSpan => do
      bindName ctx functions scheme span
      bindName ctx functions point span
      if scheme == point then error span "E_DUPLICATE" "unpack needs two distinct binding names"
      let value ← lowerExpr fuel ctx functions expr
      let raw ← data value span
      let checked ← core (checkExpr 4096 (← get).signatures ctx raw none)
      let .pointed base := checked.term.ty | error span "E_TYPE" "unpack requires Pointed"
      let objectSymbol ← core fresh
      let pointSymbol ← core fresh
      let obj := ObjectRef.local base objectSymbol
      core (rememberObject obj span "unpack" (some scheme))
      let objectBinding : Checker.Internal.Binding := { name := scheme, symbol := objectSymbol, ty := .object base, objectRef := some obj }
      let pointBinding : Checker.Internal.Binding := { name := point, symbol := pointSymbol, ty := unpackedPointType base objectSymbol }
      let (tail, ctx, functions) ← lowerStatements fuel (pointBinding :: objectBinding :: ctx) functions rest blockSpan
      pure (.unpack raw scheme point span :: tail, ctx, functions)
  def invokeTarget : Nat → Context → Target → List Value → Span → M Value
    | 0, _, _, _, span => core (checkingBudgetExceeded span)
    | fuel + 1, ctx, target, values, span => do
      let .function paramTypes result := target.ty | error span "E_TYPE" "application requires a Fn value"
      let params := paramTypes.toList
      unless params.length == values.length do error span "E_ARITY" s!"{target.ty.label} expects {params.length} arguments, found {values.length}"
      let mut targets := []
      let mut bindings := []
      let mut args := []
      let mut erased := []
      for (param, value) in params.zip values do
        if param.isFunction then
          let actual ← requireTarget value span
          sameType param actual.ty span
          -- Signature probes must also check the computations whose resulting
          -- function values are erased, including conditions and nested calls.
          let _ ← core (checkExpr 4096 (← get).signatures ctx value.raw (some .unit))
          targets := targets ++ [actual]
          bindings := bindings ++ [(param, actual)]
          erased := erased ++ [value.raw]
        else args := args ++ [← data value span]
      if target.abstractTarget then
        unless (← get).audit do error span "E_STATIC_CALL" "call target is not statically known"
        -- A signature-only type probe checks data arguments with their declared
        -- types. No probe definition is ever placed in the executable module.
        for (param, value) in params.zip values do
          unless param.isFunction do
            let expected ← core (resolveType ctx param.core span)
            let _ ← core (checkExpr 4096 (← get).signatures ctx value.raw (some expected))
            pure ()
        return ← probe result s!"{target.name}_result{span.start}" span
      let f ← definition target.name span
      sameType f.type target.ty span
      let compiled ← specialize fuel f targets span
      modify fun state => { state with calls := { target := f.name, signature := target.ty, bindings } :: state.calls }
      pure { raw := ← effects erased (.call compiled.name args span) span, target := compiled.target }
  def specialize : Nat → Function → List Target → Span → M Instance
    | 0, _, _, span => core (checkingBudgetExceeded span)
    | fuel + 1, f, targets, span => do
      let key := f.name ++ ":" ++ String.intercalate "|" (targets.map (·.name))
      if let some compiled := (← get).instances.find? (·.key == key) then return compiled
      if (← get).active.contains key then
        let lambda := f.name.startsWith "__vastitas_l"
        let label := if lambda then s!"lambda at {f.span.line}:{f.span.column}" else f.name
        let diagnostic : Diagnostic := {
          code := "E_RECURSION"
          message := s!"recursive specialization cycle involving '{label}' is not supported"
          span
          notes := if lambda then [{ span := f.span, message := "lambda defined here" }] else [] }
        core (throw diagnostic)
      let higher := f.params.any (·.ty.isFunction) || f.result.isFunction || f.name.startsWith "__vastitas_l"
      let id := (← get).nextInstance
      if higher && id >= 4096 then error span "E_LIMIT" "higher-order specialization exceeds the 4096-instance limit"
      let name := if higher then s!"__vastitas_h{id}" else f.name
      modify fun state => { state with active := key :: state.active, nextInstance := id + if higher then 1 else 0 }
      let params := f.params.filterMap fun param =>
        if param.ty.isFunction then none else some { name := param.name, ty := param.ty.core, span := param.span : RawParam }
      let raw : RawFunction := { name, params, returnType := f.result.core, body := .mk [] (.unit f.span) f.span, span := f.span }
      let signature ← core (prepareSignature raw)
      modify fun state => { state with signatures := state.signatures.insert name signature }
      let functions := ((f.params.filter (·.ty.isFunction)).map (·.name)).zip targets
      let value ← lowerBlock fuel signature.params functions f.body
      match f.result, value.target with
      | .function .., some actual => sameType f.result actual.ty f.span
      | .function .., none => error f.span "E_TYPE" s!"expected {f.result.label}, found data value"
      | .data _, some _ => error f.span "E_TYPE" "a data-returning function cannot return a Fn value"
      | _, _ => pure ()
      let raw := { raw with body := rawBlock value f.span }
      let _ ← core (checkFunction (← get).signatures { signature with raw })
      let compiled : Instance := { key, name, target := value.target }
      modify fun state => { state with
        functions := state.functions.push raw
        instances := compiled :: state.instances
        active := state.active.filter (· != key) }
      pure compiled
end

-- Body-less headers are used only to reuse declaration and finite-family
-- validation. The actual bodies are checked below, never these placeholders.
def headers (p : Program) : RawProgram := {
  version := p.version, file := p.file, generics := p.generics
  functions := p.functions.map fun f => {
    name := f.name, params := f.params.map fun param => { name := param.name, ty := param.ty.core, span := param.span }
    returnType := f.result.core, body := .mk [] (.unit f.span) f.span, span := f.span }
  methods := p.methods.map fun m => {
    name := m.name, params := m.params.map fun param => { name := param.name, ty := param.ty.core, span := param.span }
    returnType := m.result.core, body := .mk [] (.unit m.span) m.span, span := m.span, requirements := m.requirements } }

def prepare (p : Program) : CheckM (List Function × Families) := do
  let (p, lambdas) ← liftProgram p
  let raw := headers p
  DispatchChecker.validateProgram raw
  let globals := p.functions.map (·.name) ++ p.generics.map (·.name)
  for f in p.functions ++ lambdas do validateFunction f globals
  for m in p.methods do
    for param in m.params do
      if param.ty.isFunction then fail param.span "E_TYPE" "function values are not dispatch selectors"
    if m.result.isFunction then fail m.span "E_TYPE" "method results require concrete scalars"
  let families ← prepareFamilies raw
  let mut functions := (p.functions ++ lambdas).toArray
  for family in families do
    for (id, key) in family.checked.applicablePairs do
      let some method := p.methods[id]? | fail {} "E_INTERNAL_DISPATCH" "missing method"
      let params := (method.params.zip key).map fun (param, code) => { param with ty := .data (.named (Dispatch.nominalName code)) }
      functions := functions.push { method.toFunction with name := monoName id key, params }
  pure (functions.toList, families.foldl (fun table f => table.insert f.raw.name f) {})

def lowerPass (p : Program) (definitions : List Function) (families : Families) (audit : Bool) : CheckM Lowered := do
  let action : M Unit := do
    for f in definitions do
      if audit || !(f.params.any (·.ty.isFunction)) then
        let targets := f.params.filterMap fun param => if param.ty.isFunction then
          some { name := s!"__vastitas_probe_{f.name}_{param.name}", ty := param.ty, abstractTarget := true : Target } else none
        let _ ← specialize 4096 f targets f.span
        pure ()
  let (_, state) ← action.run {
    definitions, families
    globals := p.functions.map (·.name) ++ p.generics.map (·.name)
    audit }
  pure {
    module := { version := 1, file := p.file, functions := state.functions.toList }
    definitions := state.definitions, calls := state.calls }

def lowerFunctions (p : Program) : Except Diagnostic Lowered := do
  let action : CheckM Lowered := do
    let (definitions, families) ← prepare p
    let audit ← lowerPass p definitions families true
    -- Full core validation of signature probes is a type-checking pass only.
    -- No probe artifacts are reused by the separate executable specialization.
    let _ ← checkModule audit.module false
    lowerPass p definitions families false
  pure (← action.run {}).1

end VastitasKernel.Surface

namespace VastitasKernel

def checkSurfaceProgram (p : Surface.Program) (requireMain : Bool := false) : Except Diagnostic CertifiedModule := do
  if !Surface.CaptureFree p then throw (Surface.captureDiagnostic p)
  if let some legacy := p.legacyExact then
    return ← checkProgram legacy requireMain
  let lowered ← Surface.lowerFunctions p
  if !Surface.StaticCallsValid lowered then
    throw { code := "E_INTERNAL_FUNCTION", message := "static target signature audit failed" }
  checkModule lowered.module requireMain

end VastitasKernel
