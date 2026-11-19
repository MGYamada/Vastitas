import VastitasKernel.FiniteFunctionTemplate
import VastitasKernel.IndexedFunctionLift
import VastitasKernel.IndexedSourceBodies

namespace VastitasKernel.Indexed.FunctionSource.Compiler

inductive TargetName where
  | concrete (definition : Nat)
  | probe (id : Nat)
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Hashable

structure Key where
  definition : Nat
  targets : List TargetName
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Hashable

/-- A family value remembers the authorized lookup, not just its spelling.
It is valid only in this independently assembled program. -/
structure FamilyRef where
  caller : Key
  scope : Namespace.Scope
  path : Source.Path
  target : Namespace.Target
  deriving Repr, Inhabited, DecidableEq

structure DispatchSelection where
  scope : Namespace.Scope
  path : Source.Path
  target : Namespace.Target
  key : Dispatch.Key
  method : Nat
  definition : Nat
  deriving Repr, Inhabited, DecidableEq

structure Target where
  name : TargetName
  signature : Signature
  selected : Option DispatchSelection := none
  deriving Repr, Inhabited, DecidableEq

structure Value where
  term : Core.Term
  target : Option Target := none
  family : Option FamilyRef := none
  deriving Inhabited

structure Binding where
  source : Source.Binding
  target : Option Target := none
  family : Option FamilyRef := none
  deriving Inhabited

abbrev Context := List Binding

def Context.data (ctx : Context) : Source.TypeContext := ctx.map (·.source)

abbrev FiniteInstanceKey := DeclId × List StaticIndex

structure Prepared where
  definition : Definition
  context : Source.TypeContext
  parameters : List Core.Parameter
  result : Core.DataType
  paramTypes : List Signature
  resultType : Signature
  /-- Index in the static-argument list, and the audit-only formal that stands
  for the result of invoking that probe. An empty Hom has no sample tag. -/
  probeOutputs : List (Nat × Core.Parameter) := []
  finiteKey : List StaticIndex := []
  finiteBody : Option Core.Term := none
  deriving Inhabited

def Signature.dataHint : Signature → Option Core.DataType
  | .data ty => some ty
  | .function .. => none

def Prepared.dataABI (entry : Prepared) : Bool :=
  entry.paramTypes.filterMap Signature.dataHint == entry.parameters.map (·.result.type) &&
    (Signature.dataHint entry.resultType).getD (.pure .unit) == entry.result

def Prepared.callable (entry : Prepared) : Option Signature := do
  guard (entry.definition.function.finiteBinders.isEmpty && entry.dataABI &&
    entry.paramTypes.all (·.allData callableCoreData) && entry.resultType.allData callableCoreData)
  return .function entry.paramTypes entry.resultType

private def homResult : Signature → Option Core.DataType
  | .function _ result => homResult result
  | .data (.finite (.hom c x y)) => some (.finite (.hom c x y))
  | .data _ => none

def Prepared.probeParameters (p : Prepared) (audit : Bool) (k : Key) : List Core.Parameter :=
  if audit then p.probeOutputs.filterMap fun (i, arg) =>
    match k.targets[i]? with | some (.probe _) => some arg | _ => none
  else []

def Prepared.parametersFor (p : Prepared) (audit : Bool) (k : Key) : List Core.Parameter :=
  if audit then p.parameters ++ p.probeParameters true k else p.parameters

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
  templates : Std.HashMap DeclId (Function × FiniteTemplate) := {}
  finiteInstances : Std.HashMap FiniteInstanceKey Nat := {}
  discovering : Bool := false
  forwardMethods : Std.HashMap (DeclId × List Bool) ForwardMethod := {}

/-- Unapplied contribution instances (and their lambdas) are audit-only. -/
def Input.executable (input : Input) (definition : Definition) : Bool :=
  !input.excluded.contains definition.id && !input.excluded.contains definition.origin

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
  caller : Option Key
  target : Target
  expected : Signature
  deriving Inhabited

/-- The concrete represented method and the producer in each callable slot
of a selected finite forwarding method. -/
structure ForwardUse where
  caller : Key
  family : DeclId
  indices : List StaticIndex
  definition : Nat
  method : Span
  site : Span
  firstBinding : Nat
  targets : List (Option Target)
  deriving Inhabited

structure EmittedCall where
  key : Key
  id : Nat
  origin : Key
  caller : Key
  deriving Inhabited

/-- Audit-only alpha-renaming of a cached all-probe instance. The requested
targets and returned Fn remain in the caller's probe context. -/
structure ProbeReuse where
  definition : Nat
  id : Nat
  requested : List Target
  canonical : List Target
  result : Option Target
  returned : Option Target
  deriving Inhabited

structure DispatchCall extends DispatchSelection where
  caller : Key
  emittedId : Nat
  /-- A transported callable may be invoked outside the scope that resolved it. -/
  callerScope : Namespace.Scope
  deriving Inhabited

structure State where
  body : Source.Bodies.State := {}
  instances : Std.HashMap Key Instance := {}
  probeTemplates : Std.HashMap Key (List Target) := {}
  probeInstances : Std.HashMap Key Instance := {}
  probeReuses : List ProbeReuse := []
  active : List Key := []
  activeSet : Std.HashSet Key := {}
  functions : Array Core.Function := #[]
  origins : Array Key := #[]
  emittedCalls : List EmittedCall := []
  calls : List CallReference := []
  staticUses : List StaticUse := []
  dispatchCalls : List DispatchCall := []
  familyRefs : List FamilyRef := []
  /-- The Core symbol of each `let` whose value is a Fn value, which Core
  erases to `Unit`, with the Fn signature. `show!` displays no Fn value
  (#836). -/
  functionLets : List (Nat × String) := []
  nextProbe : Nat := 0
  specializations : Nat := 0
  elaborationWork : Nat := 0
  finiteCalls : Array FiniteInstanceKey := #[]
  forwardUses : List ForwardUse := []
  discoveryIds : Std.HashMap FiniteInstanceKey Nat := {}
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

def TargetName.isProbe : TargetName → Bool
  | .probe _ => true
  | .concrete _ => false

/-- First-occurrence positions preserve the complete equality pattern, not
just the signatures or number of Fn parameters. Used only for all-probe keys. -/
def probePattern (names : List TargetName) : List Nat := names.map names.idxOf

def probeKey (definition : Nat) (targets : List Target) : Key :=
  ⟨definition, (probePattern (targets.map (·.name))).map TargetName.probe⟩

def fnParameters (entry : Prepared) : List Signature :=
  entry.paramTypes.filter (·.isFunction)

def prepared (input : Input) (id : Nat) (span : Span) : M Prepared :=
  match input.prepared[id]? with
  | some definition => pure definition
  | none => error span "E_INTERNAL_FUNCTION" "unknown static function definition"

def probeVariable (input : Input) (ty : Core.DataType) (span : Span) : M Core.Term := do
  let state ← get
  let some caller := state.active.head? | error span "E_INTERNAL_FUNCTION" "missing probe caller"
  let entry ← prepared input caller.definition span
  let some formal := (entry.probeParameters state.audit caller).find? (fun p => p.result.type == ty)
    | error span "E_INTERNAL_FUNCTION" "missing formal for the nominal probe result"
  return .variable formal.symbol formal.result

def data (value : Value) (span : Span) : M Core.Term := do
  if value.target.isSome || value.family.isSome then error span "E_TYPE" "expected a data value, found a Fn value"
  return value.term

def target (value : Value) (span : Span) : M Target := do
  let some target := value.target | error span "E_TYPE" "application requires a Fn value"
  return target

def sameSignature (expected actual : Signature) (span : Span) : M Unit := do
  unless expected == actual do error span "E_TYPE" "Fn signatures must match exactly"

def recordTarget (target : Target) (expected : Signature) : M Unit :=
  modify fun state => { state with staticUses := ⟨state.active.head?, target, expected⟩ :: state.staticUses }

def concrete (input : Input) (id : Nat) (span : Span) : M Target := do
  let definition ← prepared input id span
  unless definition.definition.isLambda || id < input.sourceCount do
    error span "E_TYPE" "generic methods are not Fn values"
  let some signature := definition.callable
    | error span "E_TYPE" "Fn values require scalars, finite Hom or Fn in the signature"
  let target := Target.mk (.concrete id) signature none
  recordTarget target signature
  return target

def probe (signature : Signature) : M Target := do
  let id := (← get).nextProbe
  modify fun state => { state with nextProbe := id + 1 }
  return ⟨.probe id, signature, none⟩

/-- Presentation only: what an indexed declaration that a path names as a
value is, for the message that rejects it. -/
def indexedNotValue (declarations : Core.Declarations) (id : DeclId) : String :=
  let primitive := (declarations.primitive? id).map fun
    | .relativeConstant .. | .smoothConstant .. | .spectralInvariant .. =>
      ("a declared map", "; call it without operands")
    | .relativeIso .. => ("an isomorphism", "")
    | .relativeCartesian .. => ("a Cartesian square", "")
    | _ => ("a primitive", "; call it with its operands")
  let (kind, advice) := primitive.getD <| (·, "") <|
    if declarations.packages.any (·.id == id) then "a package declaration" else
    match Indexed.lookup declarations.indexed id with
    | some .marker => "a marker"
    | some (.finiteCarrier _) => "a finite carrier"
    | some (.finiteTable ..) => "a finite table"
    | some .monadSchema => "a finite Monad schema"
    | some (.finiteMonad ..) => "a finite Monad instance"
    | some (.kleisliSchema .category _) => "a finite Kleisli category schema"
    | some (.kleisliSchema .triple _) => "a finite Kleisli triple schema"
    | some (.finiteKleisli .category ..) => "a finite Kleisli category view"
    | some (.finiteKleisli .triple ..) => "a finite Kleisli triple view"
    | some .isoSchema => "a finite isomorphism schema"
    | some (.finiteIso ..) => "a finite isomorphism instance"
    | some .natTransSchema => "a finite natural transformation schema"
    | some (.finiteNatTrans ..) => "a finite natural transformation instance"
    | some .functorSchema => "a finite functor schema"
    | some (.finiteFunctor ..) => "a finite functor instance"
    | some .categorySchema => "a finite category schema"
    | some (.composableTable ..) => "a dependent composition table"
    | some (.finiteCategory ..) => "a finite category instance"
    | some (.implementation ..) => "an implementation"
    | some (.classification ..) => "a classification"
    | some (.global _) => "a global object"
    | some (.affine ..) | some (.smoothAffine ..) => "an object of an `indexed affine` declaration"
    | some (.family _) => "a family"
    | some (.metric ..) => "a metric"
    | some (.metricEvidence ..) => "evidence for a metric"
    | some (.frame ..) => "a frame"
    | some .baseDimension => "a base dimension"
    | some (.quantity _) => "a quantity"
    | some (.reading ..) => "a reading"
    | some (.scale ..) => "a scale"
    | some (.physicalMetric ..) => "a physical metric"
    | some (.freeModule ..) => "a free module"
    | some (.endomorphism ..) => "an endomorphism"
    | some (.spectrum ..) => "a spectrum"
    | some (.branch ..) => "a branch"
    | some (.transitionAverage ..) => "a transition average"
    | some (.convention _) => "a convention"
    | some (.model ..) => "a model"
    | some (.calibration ..) => "a calibration"
    | some (.dataset ..) => "a dataset"
    | some (.comparison ..) => "a comparison"
    | some (.smoothOpen ..) => "a smooth open"
    | some (.glued ..) => "a glued object"
    | some (.cover ..) => "a cover"
    | some (.separated ..) => "a separation claim"
    | some (.manifold ..) => "a manifold claim"
    | some (.projective ..) => "a projective claim"
    | none => "an indexed declaration"
  s!"names {kind}, which is not a value{advice}"

def resolveOrdinary (input : Input) (scope : Namespace.Scope) (path : Source.Path)
    (target : Namespace.Target) : M Nat := do
  if target.kind == .module then error path.span "E_NAME" "a module is not a value"
  if target.kind == .indexedDeclaration then
    error path.span "E_TYPE"
      s!"`{"::".intercalate path.path}` {indexedNotValue input.body.declarations target.owner}"
  unless target.kind == .function do error path.span "E_TYPE" "expected a named function"
  if input.templates.contains target.owner then
    error path.span "E_TYPE" "a finite function requires a direct call with static or inferred indices"
  let some id := input.named[target.owner]? | error path.span "E_NAME" "function has no source definition"
  modify fun state => { state with calls := ⟨scope, path, target, id⟩ :: state.calls }
  return id

def checkOperatorOwner (path : Source.Path) (owner : Option Namespace.Owner) : M Unit := do
  if let some name := Namespace.operatorShort? path.path then
    unless owner == some (Namespace.operatorId name).owner do
      error path.span "E_NAME" s!"{name} conflicts with the canonical operator family; qualify the reference"

def Binding.operatorOwner? (b : Binding) : Option Namespace.Owner :=
  (b.family.map (·.target.owner)).orElse fun _ => b.target.bind (·.selected.map (·.target.owner))

def familyRef (scope : Namespace.Scope) (path : Source.Path) (target : Namespace.Target) : M FamilyRef := do
  let some caller := (← get).active.head?
    | error path.span "E_INTERNAL_FUNCTION" "family reference has no source specialization"
  return ⟨caller, scope, path, target⟩

def resolveValue (input : Input) (scope : Namespace.Scope) (path : Source.Path) : M Value := do
  if let tag :: head :: tail := path.path.reverse then
    let carrierPath : Source.Path := ⟨(head :: tail).reverse, path.span⟩
    if let .ok c := Namespace.resolve input.body.index scope carrierPath.path carrierPath.span then
      if c.kind == .indexedDeclaration then
        let env := input.body.declarations.indexed
        let sort? ← match Indexed.lookup env c.owner with
          | some (.finiteCarrier tags) => do
            unless tags.contains tag do error path.span "E_TYPE" "not a member of the selected finite carrier"
            pure (some (FiniteSort.carrier c.owner))
          | some (.finiteCategory ..) => do
            let some sort := FiniteSort.arrowSort? env c.owner tag
              | error path.span "E_TYPE" "not an arrow of the selected finite category"
            pure (some sort)
          | _ => pure none
        if let some sort := sort? then
          let resolved ← body (Source.Bodies.lookupPath input.body.index scope carrierPath)
          modify fun state => { state with body := { state.body with
            references := ⟨scope, carrierPath, resolved⟩ :: state.body.references } }
          return { term := .finiteTag sort tag }
  let target ← body (Source.Bodies.lookupPath input.body.index scope path)
  checkOperatorOwner path target.owner
  if target.kind == .generic then
    unless input.dispatch.families.contains target.owner do
      error path.span "E_TYPE" "function family has no checked assembly"
    let ref ← familyRef scope path target
    modify fun state => { state with familyRefs := ref :: state.familyRefs }
    return { term := .unit, family := some ref }
  return { term := .unit, target := some (← concrete input (← resolveOrdinary input scope path target) path.span) }

def selectFamily (input : Input) (ref : FamilyRef) (key : Dispatch.Key) (span : Span) : M DispatchSelection := do
  let some family := input.dispatch.families[ref.target.owner]?
    | error span "E_TYPE" "function family has no checked assembly"
  let selected ← result (((DispatchChecker.selectTarget family key span ref.target.owner.qualified).run {}).map Prod.fst)
  let some id := input.dispatch.definitions[(selected.method, key)]?
    | error span "E_INTERNAL_DISPATCH" "winner has no checked source specialization"
  return ⟨ref.scope, ref.path, ref.target, key, selected.method, id⟩

def scalarSignatureKey (signature : Signature) : Option Dispatch.Key := do
  let .function parameters _ := signature | none
  parameters.toList.mapM fun parameter => do
    match parameter with
    | .data (.pure .nat) => Dispatch.parseScalar "Nat"
    | .data (.pure .int) => Dispatch.parseScalar "Int"
    | .data (.pure .bool) => Dispatch.parseScalar "Bool"
    | .data (.pure .unit) => Dispatch.parseScalar "Unit"
    | _ => none

def expect (input : Input) (expected : Option Core.DataType) (value : Value) (span : Span) : M Value := do
  if expected.isSome then
    let _ ← data value span
    let _ ← body (Source.Bodies.expect input.body expected value.term span)
  return value

/-- Resolve every nested annotation in its writing scope. Only the normalized
signature is transported across calls or compared with a selected target. -/
def resolveType (input : Source.Bodies.Input) (scope : Namespace.Scope) (ctx : Source.TypeContext)
    (type : FnType) (span : Span) : Source.Bodies.M Signature := do
  match type with
  | .data ty => return .data (← Source.Bodies.type input scope ctx ty span)
  | .function s =>
    unless type.Valid do Source.Bodies.fail span "E_TYPE" "invalid Fn parameter or result type"
    s.mapDataM fun ty => Source.Bodies.type input scope ctx ty span

def coerceAnnotation (input : Input) (type : Signature) (value : Value) (span : Span) : M Value := do
  if let some ref := value.family then
    unless type.isFunction do error span "E_TYPE" "expected data, found a static function family"
    let signature := type
    let some key := scalarSignatureKey signature | error span "E_TYPE" "family reference requires a scalar Fn argument key"
    let selection ← selectFamily input ref key span
    let definition ← prepared input selection.definition span
    let some actual := definition.callable | error span "E_TYPE" "selected method has no scalar Fn signature"
    -- Resolve only from the argument key, then check the promised result.
    sameSignature signature actual span
    let target : Target := ⟨.concrete selection.definition, actual, some selection⟩
    recordTarget target signature
    return { value with family := none, target := some target }
  match type, value.target with
  | .function .., some actual => sameSignature type actual.signature span
  | .function .., none => error span "E_TYPE" "expected a Fn value"
  | .data _, some _ => error span "E_TYPE" "expected a data value"
  | .data _, none => pure ()
  return value

def prepareDefinition (input : Source.Bodies.Input) (definition : Definition) : Source.Bodies.M Prepared := do
  let function := definition.function
  if function.higher && function.callable.isNone then
    Source.Bodies.fail function.span "E_TYPE" "higher-order signatures require scalars, finite Hom or Fn"
  let mut context : Source.TypeContext := []
  let mut parameters := []
  let mut reversedTypes := []
  for parameter in function.params do
    Source.Bodies.bindName input definition.bodyScope context parameter.name parameter.span
    let resolved ← resolveType input definition.bodyScope context parameter.type parameter.span
    reversedTypes := resolved :: reversedTypes
    let type := (Signature.dataHint resolved).getD (.pure .unit)
    let symbol ← Source.Bodies.fresh
    let reference := match type with | .object type => some (.local type symbol) | _ => none
    if let some reference := reference then
      Source.Bodies.rememberObject reference parameter.span "parameter" (some parameter.name)
    let binding : Source.Binding := ⟨parameter.name, ⟨symbol, ⟨type, reference⟩⟩, parameter.span⟩
    context := context ++ [binding]
    if let .data _ := resolved then parameters := parameters ++ [binding.parameter]
  let resultType ← resolveType input definition.bodyScope context function.result function.span
  let paramTypes := reversedTypes.reverse
  let mut probeOutputs := []
  for (s,i) in (paramTypes.filter (·.isFunction)).zipIdx do
    if let some ty := homResult s then
      probeOutputs := (i, ⟨← Source.Bodies.fresh, ⟨ty,none⟩⟩) :: probeOutputs
  return {
    definition, context, parameters, paramTypes, resultType
    result := (Signature.dataHint resultType).getD (.pure .unit)
    probeOutputs := probeOutputs.reverse }

/-- Shared final call construction evaluates every argument exactly once.
The dependent substitution was checked while elaborating the actual arguments. -/
def emitCall (input : Input) (id : Nat) (targets : List Target) (values : List Value)
    (substitution : List (ObjectRef × ObjectRef)) (span : Span)
    (dispatch : Option DispatchSelection := none) : M Value := do
  let some caller := (← get).active.head?
    | error span "E_INTERNAL_FUNCTION" "emitted call has no active source instance"
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
  for param in definition.probeParameters (← get).audit compiled.key do
    arguments := arguments ++ [← probeVariable input param.result.type span]
  modify fun state => { state with
    emittedCalls := ⟨key id targets, compiled.id, compiled.key, caller⟩ :: state.emittedCalls }
  if let some selection := dispatch then
    let source ← prepared input caller.definition span
    modify fun state => { state with dispatchCalls :=
      { toDispatchSelection := selection, caller, emittedId := compiled.id,
        callerScope := source.definition.bodyScope } :: state.dispatchCalls }
  let type := definition.result.rename substitution
  let reference ← match type with
    | .object type => some <$> body (Source.Bodies.freshObject type span s!"function call '{definition.definition.owner.name}'")
    | _ => pure none
  let term := Core.Term.call compiled.id arguments substitution ⟨type, reference⟩
  return ⟨bindings.foldr (fun (symbol, value) rest => .letE symbol value rest) term, compiled.target, none⟩

end VastitasKernel.Indexed.FunctionSource.Compiler
