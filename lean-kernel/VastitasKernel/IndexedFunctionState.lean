import VastitasKernel.IndexedFunctionLift
import VastitasKernel.IndexedSourceProgram

namespace VastitasKernel.Indexed.FunctionSource.Compiler

inductive TargetName where
  | concrete (definition : Nat)
  | probe (id : Nat)
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Hashable

structure Target where
  name : TargetName
  signature : Surface.TypeExpr
  deriving Repr, Inhabited

structure Value where
  term : Core.Term
  target : Option Target := none
  deriving Inhabited

structure Binding where
  source : Source.Binding
  target : Option Target := none
  deriving Inhabited

abbrev Context := List Binding

def Context.data (ctx : Context) : Source.TypeContext := ctx.map (·.source)

structure Prepared where
  definition : Definition
  context : Source.TypeContext
  parameters : List Core.Parameter
  result : Core.DataType
  deriving Inhabited

/-- The finite dispatcher supplies actual checked families and a reconstructed
source-method/key table. Plain Fn programs use the empty dispatcher. -/
structure DispatchInput where
  families : Std.HashMap DeclId DispatchChecker.Family := {}
  definitions : Std.HashMap (Nat × Dispatch.Key) Nat := {}
  deriving Inhabited

structure Input where
  source : Program
  body : Source.Bodies.Input
  prepared : Array Prepared
  named : Std.HashMap DeclId Nat
  sourceCount : Nat
  dispatch : DispatchInput := {}
  excluded : Std.HashSet Nat := {}

/-- Unapplied contribution instances (and their lambdas) are audit-only. -/
def Input.executable (input : Input) (definition : Definition) : Bool :=
  !input.excluded.contains definition.id && !input.excluded.contains definition.origin

structure Key where
  definition : Nat
  targets : List TargetName
  deriving Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Hashable

structure Instance where
  key : Key
  id : Nat
  target : Option Target
  deriving Inhabited

structure CallReference where
  scope : Namespace.Scope
  path : Source.Path
  target : Namespace.Target
  definition : Nat
  deriving Inhabited

structure StaticUse where
  target : Target
  expected : Surface.TypeExpr
  deriving Inhabited

structure EmittedCall where
  key : Key
  id : Nat
  deriving Inhabited

structure DispatchCall where
  scope : Namespace.Scope
  path : Source.Path
  target : Namespace.Target
  key : Dispatch.Key
  method : Nat
  definition : Nat
  deriving Inhabited

structure State where
  body : Source.Bodies.State := {}
  instances : Std.HashMap Key Instance := {}
  active : List Key := []
  activeSet : Std.HashSet Key := {}
  functions : Array Core.Function := #[]
  origins : Array Key := #[]
  emittedCalls : List EmittedCall := []
  calls : List CallReference := []
  staticUses : List StaticUse := []
  dispatchCalls : List DispatchCall := []
  nextProbe : Nat := 0
  specializations : Nat := 0
  audit : Bool := false
  deriving Inhabited

/-- Suspending on a callee keeps body fuel separate from dependency traversal.
The executable and signature-probe passes have disjoint states. -/
inductive Work (α : Type) where
  | done (value : α) (state : State)
  | failed (diagnostic : Diagnostic)
  | request (definition : Nat) (targets : List Target) (span : Span)
      (state : State) (resume : Instance → State → Work α)

abbrev M (α : Type) := State → Work α

def Work.bind (work : Work α) (next : α → M β) : Work β :=
  match work with
  | .done value state => next value state
  | .failed diagnostic => .failed diagnostic
  | .request definition targets span state resume =>
    .request definition targets span state fun compiled state => (resume compiled state).bind next

instance : Monad M where
  pure value state := .done value state
  bind action next state := (action state).bind next

instance : MonadStateOf State M where
  get state := .done state state
  set state _ := .done () state
  modifyGet f state := let (value, state) := f state; .done value state

def body (action : Source.Bodies.M α) : M α := fun state =>
  match action.run state.body with
  | .error diagnostic => .failed diagnostic
  | .ok (value, inner) => .done value { state with body := inner }

def error (span : Span) (code message : String) : M α :=
  fun _ => .failed { code, message, span }

def checkingBudgetExceeded (span : Span) : M α := body (Source.Bodies.checkingBudgetExceeded span)

def result (action : Namespace.Result α) : M α := fun state =>
  match action with | .ok value => .done value state | .error diagnostic => .failed diagnostic

def fresh : M Nat := body Source.Bodies.fresh

def request (definition : Nat) (targets : List Target) (span : Span) : M Instance := fun state =>
  .request definition targets span state fun compiled state => .done compiled state

def key (definition : Nat) (targets : List Target) : Key := ⟨definition, targets.map (·.name)⟩

def prepared (input : Input) (id : Nat) (span : Span) : M Prepared :=
  match input.prepared[id]? with
  | some definition => pure definition
  | none => error span "E_INTERNAL_FUNCTION" "unknown static function definition"

def data (value : Value) (span : Span) : M Core.Term := do
  if value.target.isSome then error span "E_TYPE" "expected a data value, found a Fn value"
  return value.term

def target (value : Value) (span : Span) : M Target := do
  let some target := value.target | error span "E_TYPE" "application requires a Fn value"
  return target

def sameSignature (expected actual : Surface.TypeExpr) (span : Span) : M Unit := do
  unless expected == actual do error span "E_TYPE" "Fn signatures must match exactly"

def recordTarget (target : Target) (expected : Surface.TypeExpr) : M Unit :=
  modify fun state => { state with staticUses := ⟨target, expected⟩ :: state.staticUses }

def concrete (input : Input) (id : Nat) (span : Span) : M Target := do
  let definition ← prepared input id span
  unless definition.definition.isLambda || id < input.sourceCount do
    error span "E_TYPE" "generic methods are not Fn values"
  let some signature := definition.definition.function.callable
    | error span "E_TYPE" "Fn values require scalar/Fn signatures; indexed and Pair functions are direct-call only"
  let target := Target.mk (.concrete id) signature
  recordTarget target signature
  return target

def probe (signature : Surface.TypeExpr) : M Target := do
  let id := (← get).nextProbe
  modify fun state => { state with nextProbe := id + 1 }
  return ⟨.probe id, signature⟩

def resolve (input : Input) (scope : Namespace.Scope) (path : Source.Path) : M Nat := do
  let target ← result (Namespace.resolve input.body.index scope path.path path.span)
  if target.kind == .module then error path.span "E_NAME" "a module is not a value"
  unless target.kind == .function do error path.span "E_TYPE" "expected an ordinary function; generic families are not Fn values"
  let some id := input.named[target.owner]? | error path.span "E_NAME" "function has no source definition"
  modify fun state => { state with calls := ⟨scope, path, target, id⟩ :: state.calls }
  return id

def expect (input : Input) (expected : Option Core.DataType) (value : Value) (span : Span) : M Value := do
  if expected.isSome then
    let _ ← data value span
    let _ ← body (Source.Bodies.expect input.body expected value.term span)
  return value

def annotation (input : Input) (scope : Namespace.Scope) (ctx : Context)
    (type : FnType) (span : Span) : M (Option Core.DataType) :=
  match type with
  | .data type => some <$> body (Source.Bodies.type input.body scope ctx.data type span)
  | .function signature => do
    unless (FnType.function signature).Valid do error span "E_TYPE" "Fn signatures require scalar/recursive-Fn types"
    return none

def checkAnnotation (type : FnType) (value : Value) (span : Span) : M Unit := do
  match type, value.target with
  | .function signature, some actual => sameSignature signature actual.signature span
  | .function _, none => error span "E_TYPE" "expected a Fn value"
  | .data _, some _ => error span "E_TYPE" "expected a data value"
  | .data _, none => pure ()

def prepareDefinition (input : Source.Bodies.Input) (definition : Definition) : Source.Bodies.M Prepared := do
  let function := definition.function
  if function.higher && function.callable.isNone then
    Source.Bodies.fail function.span "E_TYPE" "higher-order function signatures require scalar/Fn types"
  let mut context : Source.TypeContext := []
  let mut parameters := []
  for parameter in function.params do
    Source.Bodies.bindName input definition.bodyScope context parameter.name parameter.span
    let type ← match parameter.type with
      | .data type => Source.Bodies.type input definition.bodyScope context type parameter.span
      | .function signature => do
        unless (FnType.function signature).Valid do
          Source.Bodies.fail parameter.span "E_TYPE" "Fn signatures require scalar/recursive-Fn types"
        pure (Core.DataType.pure .unit)
    let symbol ← Source.Bodies.fresh
    let reference := match type with | .object type => some (.local type symbol) | _ => none
    if let some reference := reference then
      Source.Bodies.rememberObject reference parameter.span "parameter" (some parameter.name)
    let binding : Source.Binding := ⟨parameter.name, ⟨symbol, ⟨type, reference⟩⟩, parameter.span⟩
    context := context ++ [binding]
    if let .data _ := parameter.type then parameters := parameters ++ [binding.parameter]
  let result ← match function.result with
    | .data type => Source.Bodies.type input definition.bodyScope context type function.span
    | .function signature => do
      unless (FnType.function signature).Valid do Source.Bodies.fail function.span "E_TYPE" "invalid Fn result"
      pure (Core.DataType.pure .unit)
  return ⟨definition, context, parameters, result⟩

/-- Shared final call construction evaluates every argument exactly once.
The dependent substitution was checked while elaborating the actual arguments. -/
def emitCall (input : Input) (id : Nat) (targets : List Target) (values : List Value)
    (substitution : List (ObjectRef × ObjectRef)) (span : Span) : M Value := do
  let definition ← prepared input id span
  let parameters := definition.definition.function.params
  unless parameters.length == values.length do error span "E_ARITY" "wrong checked call argument count"
  let mut bindings := []
  let mut arguments := []
  for (parameter, value) in parameters.zip values do
    let symbol ← fresh
    bindings := bindings ++ [(symbol, value.term)]
    if let .data _ := parameter.type then
      arguments := arguments ++ [Core.Term.variable symbol value.term.result]
  let compiled ← request id targets span
  modify fun state => { state with emittedCalls := ⟨key id targets, compiled.id⟩ :: state.emittedCalls }
  let type := definition.result.rename substitution
  let reference ← match type with
    | .object type => some <$> body (Source.Bodies.freshObject type span s!"function call '{definition.definition.owner.name}'")
    | _ => pure none
  let term := Core.Term.call compiled.id arguments substitution ⟨type, reference⟩
  return ⟨bindings.foldr (fun (symbol, value) rest => .letE symbol value rest) term, compiled.target⟩

end VastitasKernel.Indexed.FunctionSource.Compiler
