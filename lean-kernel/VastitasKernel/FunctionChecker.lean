import VastitasKernel.FunctionLift
import Std.Data.HashMap.Lemmas

namespace VastitasKernel.Surface
open Checker.Internal
open DispatchChecker

structure Target where
  name : TargetName
  ty : TypeExpr
  deriving Repr, BEq, Inhabited

structure Value extends LoweredExpr where
  target : Option Target := none
  deriving Inhabited

structure Instance where
  key : InstanceKey
  name : EmittedName
  target : Option Target
  deriving Inhabited

/-- Recorded concrete higher-order selections are independently audited against
backend declarations. Abstract signature probes never enter this ledger. -/
structure StaticCall where
  target : FunctionName
  signature : TypeExpr
  bindings : List (TypeExpr × Target) := []
  deriving Inhabited

structure Lowered where
  module : RawModule
  definitions : List Definition
  calls : List StaticCall
  deriving Inhabited

def StaticCallsValid (lowered : Lowered) : Prop :=
  ∀ call ∈ lowered.calls,
    (∃ definition ∈ lowered.definitions, definition.id = call.target ∧ definition.type = call.signature) ∧
    ∀ binding ∈ call.bindings, binding.1 = binding.2.ty ∧
      ∃ definition ∈ lowered.definitions, TargetName.concrete definition.id = binding.2.name ∧ definition.type = binding.2.ty

instance (lowered : Lowered) : Decidable (StaticCallsValid lowered) := by
  unfold StaticCallsValid
  infer_instance

/-- Lookup preserves the original first-declaration behavior, even for callers
of `lowerPass` that have not run duplicate-name validation. -/
def definitionLookup (definitions : List Definition) : Std.HashMap FunctionName Definition :=
  definitions.foldr (fun definition index => index.insert definition.id definition) {}

theorem definitionLookup_matches_list (definitions : List Definition) (name : FunctionName) :
    (definitionLookup definitions)[name]? = definitions.find? (·.id == name) := by
  induction definitions with
  | nil => simp [definitionLookup]
  | cons head tail ih =>
    change ((definitionLookup tail).insert head.id head)[name]? = _
    rw [Std.HashMap.getElem?_insert, ih]
    cases h : head.id == name <;> simp [h]

/-- Existence auditing must retain every definition with the requested identity.
Unlike lookup, a first/last match can lose a valid signature on duplicate input. -/
def definitionBuckets (definitions : List Definition) : Std.HashMap FunctionName (List Definition) :=
  definitions.foldr (fun definition index =>
    index.insert definition.id (definition :: index[definition.id]?.getD [])) {}

theorem definitionBuckets_matches_list (definitions : List Definition) (name : FunctionName) :
    (definitionBuckets definitions)[name]?.getD [] = definitions.filter (·.id == name) := by
  induction definitions with
  | nil => simp [definitionBuckets]
  | cons head tail ih =>
    change ((definitionBuckets tail).insert head.id
      (head :: (definitionBuckets tail)[head.id]?.getD []))[name]?.getD [] = _
    rw [Std.HashMap.getElem?_insert]
    by_cases h : head.id = name
    · subst name
      simp [ih]
    · simp [ih, beq_eq_false_iff_ne.mpr h]

/-- Constructed in the backend from the actual definitions. The bucket equality
is erased at runtime; no frontend index or uniqueness assumption is trusted. -/
structure DefinitionIndex (definitions : List Definition) where
  entries : Std.HashMap FunctionName (List Definition)
  lookup_eq : ∀ name, entries[name]?.getD [] = definitions.filter (·.id == name)

def definitionIndex (definitions : List Definition) : DefinitionIndex definitions :=
  ⟨definitionBuckets definitions, definitionBuckets_matches_list definitions⟩

def staticTargetValid (index : DefinitionIndex definitions) (name : FunctionName)
    (signature : TypeExpr) : Bool :=
  (index.entries[name]?.getD []).any (fun definition => decide (definition.type = signature))

def staticBindingValid (index : DefinitionIndex definitions) (binding : TypeExpr × Target) : Bool :=
  decide (binding.1 = binding.2.ty) && match binding.2.name with
    | .probe _ => false
    | .concrete name => staticTargetValid index name binding.2.ty

def staticCallsValid (lowered : Lowered) : Bool :=
  let index := definitionIndex lowered.definitions
  lowered.calls.all fun call =>
    staticTargetValid index call.target call.signature && call.bindings.all (staticBindingValid index)

theorem staticTargetValid_iff (index : DefinitionIndex definitions) :
    staticTargetValid index name signature = true ↔
      ∃ definition ∈ definitions, definition.id = name ∧ definition.type = signature := by
  simp only [staticTargetValid, index.lookup_eq, List.any_eq_true, List.mem_filter,
    beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨definition, ⟨member, same⟩, signature⟩
    exact ⟨definition, member, same, signature⟩
  · rintro ⟨definition, member, same, signature⟩
    exact ⟨definition, ⟨member, same⟩, signature⟩

theorem staticTargetValid_sound (index : DefinitionIndex definitions)
    (valid : staticTargetValid index name signature = true) :
    ∃ definition ∈ definitions, definition.id = name ∧ definition.type = signature :=
  (staticTargetValid_iff index).mp valid

theorem staticBindingValid_sound (index : DefinitionIndex definitions)
    (valid : staticBindingValid index binding = true) :
    binding.1 = binding.2.ty ∧ ∃ definition ∈ definitions,
      TargetName.concrete definition.id = binding.2.name ∧ definition.type = binding.2.ty := by
  unfold staticBindingValid at valid
  obtain ⟨same, target⟩ := Bool.and_eq_true_iff.mp valid
  refine ⟨of_decide_eq_true same, ?_⟩
  cases name : binding.2.name with
  | probe id => simp [name] at target
  | concrete function =>
    obtain ⟨definition, member, equal, signature⟩ :=
      staticTargetValid_sound index (by simpa [name] using target)
    exact ⟨definition, member, by rw [equal], signature⟩

theorem staticCallsValid_sound (lowered : Lowered)
    (valid : staticCallsValid lowered = true) : StaticCallsValid lowered := by
  intro call member
  obtain ⟨target, bindings⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp valid call member)
  refine ⟨staticTargetValid_sound _ target, ?_⟩
  intro binding member
  exact staticBindingValid_sound _ (List.all_eq_true.mp bindings binding member)

theorem staticBindingValid_iff (index : DefinitionIndex definitions) :
    staticBindingValid index binding = true ↔
      binding.1 = binding.2.ty ∧ ∃ definition ∈ definitions,
        TargetName.concrete definition.id = binding.2.name ∧ definition.type = binding.2.ty := by
  constructor
  · exact staticBindingValid_sound index
  · rintro ⟨same, definition, member, name, signature⟩
    simp only [staticBindingValid, same, decide_true, Bool.true_and]
    rw [← name]
    exact (staticTargetValid_iff index).mpr ⟨definition, member, rfl, signature⟩

/-- Exact equivalence, including duplicate identities with different signatures.
The audit never substitutes one arbitrarily chosen declaration for existence. -/
theorem staticCallsValid_iff (lowered : Lowered) :
    staticCallsValid lowered = true ↔ StaticCallsValid lowered := by
  simp only [staticCallsValid, StaticCallsValid, List.all_eq_true, Bool.and_eq_true_iff,
    staticTargetValid_iff, staticBindingValid_iff]

structure State where
  definitions : List Definition
  byName : Std.HashMap FunctionName Definition
  families : Families
  globals : Std.HashSet String
  signatures : Signatures := {}
  instances : Std.HashMap InstanceKey Instance := {}
  active : List InstanceKey := []
  activeSet : Std.HashSet InstanceKey := {}
  functions : Array RawFunction := #[]
  calls : List StaticCall := []
  nextInstance : Nat := 0
  nextProbe : Nat := 0
  audit : Bool := false
  deriving Inhabited

/-- A suspended call retains its local continuation, but receives the updated
specialization and core states when its dependency finishes. Body fuel is never
threaded through this scheduler. -/
inductive Work (α : Type) where
  | done (value : α) (state : State) (checker : CheckerState)
  | failed (diagnostic : Diagnostic)
  | request (function : Definition) (targets : List Target) (span : Span)
      (state : State) (checker : CheckerState)
      (resume : Instance → State → CheckerState → Work α)

abbrev M (α : Type) := State → CheckerState → Work α

def Work.bind (work : Work α) (next : α → M β) : Work β :=
  match work with
  | .done value state checker => next value state checker
  | .failed diagnostic => .failed diagnostic
  | .request f targets span state checker resume =>
    .request f targets span state checker fun compiled state checker =>
      (resume compiled state checker).bind next

def Work.withMethodNote (work : Work α) (f : Definition) : Work α :=
  match work with
  | .done value state checker => .done value state checker
  | .failed diagnostic =>
    let notes : List DiagnosticNote := match f.id with
      | .method _ key => [{
        span := f.span
        message := s!"while checking method '{f.name}' for concrete key {keyLabel key}" }]
      | _ => []
    .failed { diagnostic with notes := diagnostic.notes ++ notes }
  | .request callee targets span state checker resume =>
    .request callee targets span state checker fun compiled state checker =>
      (resume compiled state checker).withMethodNote f

instance : Monad M where
  pure value state checker := .done value state checker
  bind action next state checker := (action state checker).bind next

instance : MonadStateOf State M where
  get state checker := .done state state checker
  set state _ checker := .done () state checker
  modifyGet f state checker := let (value, state) := f state; .done value state checker

abbrev Functions := List (String × Target)

def core (action : CheckM α) : M α := fun state checker =>
  match action.run checker with
  | .ok (value, checker) => .done value state checker
  | .error diagnostic => .failed diagnostic

def instanceKey (f : Definition) (targets : List Target) : InstanceKey :=
  { function := f.id, arguments := targets.map (·.name) }

def requestInstance (f : Definition) (targets : List Target) (span : Span) : M Instance :=
  fun state checker => .request f targets span state checker fun compiled state checker =>
    .done compiled state checker

def error (span : Span) (code message : String) : M α := core (fail span code message)

def data (value : Value) (span : Span) : M RawExpr := do
  if let some target := value.target then
    error span "E_TYPE" s!"expected a data value, found {target.ty.label}"
  else pure value.raw

def definition (name : FunctionName) (span : Span) : M Definition := do
  match (← get).byName[name]? with
  | some f => pure f
  | none => error span "E_NAME" s!"unknown function '{name.render}'"

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
  unless ty.withinDepth Limits.typeNesting do
    fail span "E_LIMIT" s!"declared type nesting exceeds {Limits.typeNesting}"
  match ty with
  | .data raw => DispatchChecker.validateType raw span
  | .function .. =>
    unless ty.callableData do
      fail span "E_TYPE" "Fn signatures support only Nat, Int, Bool, Unit and Fn types"

def validateFunction (f : Function) (globals : Std.HashSet String) : CheckM Unit := do
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

private def freshProbe (ty : TypeExpr) : M Target := do
  let id := (← get).nextProbe
  modify fun state => { state with nextProbe := id + 1 }
  pure { name := .probe id, ty }

private def probe (ty : TypeExpr) (span : Span) : M Value := do
  match ty with
  | .function .. => pure { raw := .unit span, target := some (← freshProbe ty) }
  | .data (.named "Bool") => pure { raw := .boolean false span }
  | .data (.named "Unit") => pure { raw := .unit span, known := some ⟨.unit, none⟩ }
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
      | .boolean value span => pure { raw := .boolean value span, known := some ⟨.bool, none⟩ }
      | .unit span => pure { raw := .unit span, known := some ⟨.unit, none⟩ }
      | .variable name span =>
        core (checkReference name span)
        if let some (_, target) := functions.find? (·.1 == name) then
          return { raw := .unit span, target := some target }
        if let some f := (← get).byName[FunctionName.source name]? then
          unless f.type.callableData do error span "E_TYPE" "function values require scalar/Fn signatures"
          return { raw := .unit span, target := some { name := .concrete f.id, ty := f.type } }
        if (← get).families.contains name then error span "E_TYPE" "a generic is not a Fn value; use an explicit ordinary-function wrapper"
        pure { toLoweredExpr := LoweredExpr.atom (.variable name span) ctx }
      | .lambda _ _ _ span => error span "E_INTERNAL_FUNCTION" "lambda was not lifted"
      | .reference name span =>
        let f ← definition name span
        unless f.type.callableData do error span "E_TYPE" "lambda signatures require scalar/Fn types"
        pure { raw := .unit span, target := some { name := .concrete f.id, ty := f.type } }
      | .call name args span =>
        core (checkReference name span)
        let values ← args.mapM (lowerExpr fuel ctx functions)
        if let some (_, target) := functions.find? (·.1 == name) then
          return ← invokeTarget fuel ctx target values span
        if ctx.any (·.name == name) then error span "E_TYPE" "application requires a Fn value"
        if let some family := (← get).families[name]? then
          core (arity name (values.map (·.raw)) family.raw.params.length span)
          let values ← values.mapM fun value => do
            let _ ← data value span
            let info ← core (value.toLoweredExpr.infer (← get).signatures ctx)
            return { value with known := some info }
          let key ← values.mapM fun value => do
            core (scalarKey (← core (value.toLoweredExpr.infer (← get).signatures ctx)) span)
          let target ← core (selectTarget family key span)
          let f ← definition (.method target.method key) span
          return ← invokeTarget fuel ctx { name := .concrete f.id, ty := f.type } values span
        if let some f := (← get).byName[FunctionName.source name]? then
          return ← invokeTarget fuel ctx { name := .concrete f.id, ty := f.type } values span
        let _ ← values.mapM (fun value => data value span)
        return { toLoweredExpr := ← core (lowerCall (← get).signatures ctx name (values.map (·.toLoweredExpr)) span) }
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
        let _ ← data condition span
        let _ ← core (condition.toLoweredExpr.infer (← get).signatures ctx (some .bool))
        let yes ← lowerBlock fuel ctx functions yes
        let no ← lowerBlock fuel ctx functions no
        let target ← match yes.target, no.target with
          | none, none => pure none
          | some a, some b => do
            sameType a.ty b.ty span
            if a.name == b.name then pure (some a)
            else if (← get).audit && (a.name.isProbe || b.name.isProbe) then
              some <$> freshProbe a.ty
            else error span "E_STATIC_CALL" "function-valued branches must resolve to the same static target"
          | _, _ => error span "E_TYPE" "both branches must have the same data or Fn type"
        pure { raw := .ite condition.raw (rawBlock yes span) (rawBlock no span) span, target }
  def lowerBlock : Nat → Context → Functions → Block → M Value
    | 0, _, _, .mk _ _ span => core (checkingBudgetExceeded span)
    | fuel + 1, ctx, functions, .mk statements result span => do
      let (statements, inner, functions) ← lowerStatements fuel ctx functions statements span
      let value ← lowerExpr fuel inner functions result
      let data ← core (lowerBlockResult ctx statements value.toLoweredExpr span)
      pure { value with toLoweredExpr := data }
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
      let checked ← core (value.toLoweredExpr.infer (← get).signatures ctx expected)
      let symbol ← core fresh
      if let some ref := checked.objectRef then core (nameObject ref name)
      let binding : Checker.Internal.Binding := { name, symbol, ty := checked.ty, objectRef := checked.objectRef }
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
      let checked ← core (value.toLoweredExpr.infer (← get).signatures ctx)
      let .pointed base := checked.ty | error span "E_TYPE" "unpack requires Pointed"
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
    | _ + 1, ctx, target, values, span => do
      let .function paramTypes result := target.ty | error span "E_TYPE" "application requires a Fn value"
      let params := paramTypes.toList
      unless params.length == values.length do error span "E_ARITY" s!"{target.ty.label} expects {params.length} arguments, found {values.length}"
      let mut targets := []
      let mut bindings := []
      let mut erased := []
      for (param, value) in params.zip values do
        if param.isFunction then
          let actual ← requireTarget value span
          sameType param actual.ty span
          -- Signature probes must also check the computations whose resulting
          -- function values are erased, including conditions and nested calls.
          let _ ← core (value.toLoweredExpr.infer (← get).signatures ctx (some .unit))
          targets := targets ++ [actual]
          bindings := bindings ++ [(param, actual)]
          erased := erased ++ [value.raw]
        else
          let _ ← data value span
          pure ()
      if target.name.isProbe then
        unless (← get).audit do error span "E_STATIC_CALL" "call target is not statically known"
        -- A signature-only type probe checks data arguments with their declared
        -- types. No probe definition is ever placed in the executable module.
        for (param, value) in params.zip values do
          unless param.isFunction do
            let expected ← core (resolveType ctx param.core span)
            let _ ← core (value.toLoweredExpr.infer (← get).signatures ctx (some expected))
            pure ()
        return ← probe result span
      let .concrete name := target.name | error span "E_INTERNAL_FUNCTION" "probe escaped the audit pass"
      let f ← definition name span
      sameType f.type target.ty span
      let compiled ← requestInstance f targets span
      modify fun state => { state with calls := { target := f.id, signature := target.ty, bindings } :: state.calls }
      let dataValues := (params.zip values).filterMap fun (param, value) =>
        if param.isFunction then none else some value.toLoweredExpr
      let value ← core (lowerCall (← get).signatures ctx compiled.name.render dataValues span)
      pure { toLoweredExpr := { value with raw := ← effects erased value.raw span }, target := compiled.target }
end

/-- One new instance owns a full body budget, independently of the caller. -/
def compileInstance (f : Definition) (targets : List Target) (span : Span) : M Instance := do
  let key := instanceKey f targets
  if let some compiled := (← get).instances[key]? then return compiled
  if (← get).activeSet.contains key then
    let state ← get
    let cycle := state.active.reverse.dropWhile (· != key) ++ [key]
    let labels := cycle.map fun k =>
      (state.byName[k.function]?).map (·.label) |>.getD k.function.render
    let diagnostic : Diagnostic := {
      code := "E_RECURSION"
      message := s!"recursive call cycle {String.intercalate " → " (labels.map (fun name => "`" ++ name ++ "`"))} is not supported"
      span := f.span
      notes := if f.id.isLambda then [{ span := f.span, message := "lambda defined here" }] else [] }
    core (throw diagnostic)
  let higher := f.params.any (·.ty.isFunction) || f.result.isFunction || f.id.isLambda
  let id := (← get).nextInstance
  if higher && id >= Limits.specializations then error span "E_LIMIT" s!"higher-order specialization exceeds the {Limits.specializations}-instance limit"
  let name := if higher then EmittedName.specialized id else .original f.id
  modify fun state => { state with active := key :: state.active, activeSet := state.activeSet.insert key, nextInstance := id + if higher then 1 else 0 }
  let params := f.params.filterMap fun param =>
    if param.ty.isFunction then none else some { name := param.name, ty := param.ty.core, span := param.span : RawParam }
  let raw : RawFunction := { name := name.render, params, returnType := f.result.core, body := .mk [] (.unit f.span) f.span, span := f.span }
  let signature ← core (prepareSignature raw)
  modify fun state => { state with signatures := state.signatures.insert name.render signature }
  let functions := ((f.params.filter (·.ty.isFunction)).map (·.name)).zip targets
  let value ← lowerBlock Limits.bodyChecking signature.params functions f.body
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
    instances := state.instances.insert key compiled
    active := state.active.tail
    activeSet := state.activeSet.erase key }
  pure compiled

/-- Tail-recursive worklist interpreter. A request either resumes from a cached
instance or places that instance's body before the suspended caller. -/
def runWork : Nat → Work α → Except Diagnostic (α × State × CheckerState)
  | 0, _ => .error { code := "E_LIMIT", message := "specialization worklist budget exceeded" }
  | _ + 1, .done value state checker => .ok (value, state, checker)
  | _ + 1, .failed diagnostic => .error diagnostic
  | fuel + 1, .request f targets span state checker resume =>
    match state.instances[instanceKey f targets]? with
    | some compiled => runWork fuel (resume compiled state checker)
    | none => runWork fuel (((compileInstance f targets span state checker).withMethodNote f).bind
        (fun compiled state checker => resume compiled state checker))

-- Body-less headers are used only to reuse declaration and finite-family
-- validation. The actual bodies are checked below, never these placeholders.
def headers (p : Program) : RawProgram := {
  version := p.version, file := p.file, generics := p.generics
  abstractTypes := p.abstractTypes, subtypes := p.subtypes, abstractMethods := p.abstractMethods
  functions := p.functions.map fun f => {
    name := f.name, params := f.params.map fun param => { name := param.name, ty := param.ty.core, span := param.span }
    returnType := f.result.core, body := .mk [] (.unit f.span) f.span, span := f.span }
  methods := p.methods.map fun m => {
    name := m.name, params := m.params.map fun param => { name := param.name, ty := param.ty.core, span := param.span }
    returnType := m.result.core, body := .mk [] (.unit m.span) m.span, span := m.span, requirements := m.requirements } }

def prepare (p : Program) : CheckM (List Definition × Families) := do
  let (p, lambdas) ← liftProgram p
  let raw := headers p
  DispatchChecker.validateProgram raw
  let globals := Std.HashSet.ofList (p.functions.map (·.name) ++ p.generics.map (·.name) ++ p.abstractTypes.map (·.name))
  for f in p.functions ++ lambdas.map (·.toFunction) do validateFunction f globals
  for m in p.methods do
    for param in m.params do
      if param.ty.isFunction then fail param.span "E_TYPE" "function values are not dispatch selectors"
    if m.result.isFunction then fail m.span "E_TYPE" "method results require concrete scalars or homogeneous numeric pairs"
  let families ← prepareFamilies raw
  let mut functions := ((p.functions.map fun f => { toFunction := f, id := .source f.name : Definition }) ++ lambdas).toArray
  for family in families do
    for (id, key) in family.checked.applicablePairs do
      let some method := p.methods[id]? | fail {} "E_INTERNAL_DISPATCH" "missing method"
      let params := (method.params.zip key).map fun (param, code) => { param with ty := .data (.named (Dispatch.nominalName code)) }
      functions := functions.push { toFunction := { method.toFunction with params }, id := .method id key }
  pure (functions.toList, families.foldl (fun table f => table.insert f.raw.name f) {})

mutual
  def expressionRequests : Expr → Nat
    | .call _ args _ => 1 + (args.map expressionRequests).sum
    | .invoke callee args _ => 1 + expressionRequests callee + (args.map expressionRequests).sum
    | .lambda _ _ body _ | .block body _ => blockRequests body
    | .unary _ value _ => expressionRequests value
    | .binary _ left right _ | .pack left right _ => expressionRequests left + expressionRequests right
    | .ite condition yes no _ => expressionRequests condition + blockRequests yes + blockRequests no
    | _ => 0
  def blockRequests : Block → Nat
    | .mk statements result _ => (statements.map statementRequests).sum + expressionRequests result
  def statementRequests : Stmt → Nat
    | .letE _ _ value _ | .unpack value _ _ _ => expressionRequests value
end

def lowerPass (p : Program) (definitions : List Definition) (families : Families) (audit : Bool) : CheckM Lowered := do
  let action : M Unit := do
    for f in definitions do
      if audit || !(f.params.any (·.ty.isFunction)) then
        let targets ← (f.params.filter (·.ty.isFunction)).mapM fun param => freshProbe param.ty
        let _ ← requestInstance f targets f.span
        pure ()
  -- Every ordinary definition has at most one instance; higher-order instances
  -- are capped at 4096. Each instance can request no more calls than its source
  -- syntax size. This administrative bound does not consume any body's fuel.
  let workBudget := (definitions.length + Limits.specializations + 1) *
    (definitions.foldl (fun total f => total + blockRequests f.body + 1) 1)
  let checker ← get
  let (_, state, checker) ← runWork workBudget (action {
    definitions, families
    byName := definitionLookup definitions
    globals := Std.HashSet.ofList (p.functions.map (·.name) ++ p.generics.map (·.name) ++ p.abstractTypes.map (·.name))
    audit } checker)
  set checker
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
  if !Surface.LambdaShadowFree p then
    throw (p.lambdaShadowDiagnostic.getD { code := "E_SHADOW", message := "lambda shadows an enclosing binding" })
  let lowered ← Surface.lowerFunctions p
  if !Surface.staticCallsValid lowered then
    throw { code := "E_INTERNAL_FUNCTION", message := "static target signature audit failed" }
  checkModule lowered.module requireMain

/-- Compatibility entry point for raw first-order clients. The adapter does
not select a different lowering algorithm. -/
def checkProgram (p : RawProgram) (requireMain : Bool := false) : Except Diagnostic CertifiedModule :=
  checkSurfaceProgram (Surface.Program.ofRaw p) requireMain

end VastitasKernel
