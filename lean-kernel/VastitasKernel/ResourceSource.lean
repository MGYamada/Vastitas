import VastitasKernel.StorageFunctions
import VastitasKernel.ResourcePure

/-! Unresolved resource functions in the same package namespace as pure indexed
functions, dispatch and edit authority. No owner, local symbol or callee ID is
accepted from source. Public protocol 8 supplies the strict decoder and native
entry boundary. Dynamic dimensions and general mixed value flow remain separate
from this initial static profile and terminal pure return block. -/
namespace VastitasKernel.ResourceSource
open Storage

inductive Parameter where
  | owned (name : String) (type : Functions.OwnedType) (span : Span)
  | borrowed (name : String) (scalar : Scalar) (rows columns : Nat)
      (access : Access) (initializes : Bool) (span : Span)
  | space (name : String) (implementation : Indexed.Source.Path) (dimension : Nat) (span : Span)
  | basis (name space : String) (span : Span)
  | map (name source target : String) (access : Access) (initializes : Bool) (span : Span)
  | ownedMap (name source target : String) (span : Span)
  | involution (name space : String) (span : Span)
  | dualSpace (name parent : String) (span : Span)
  | conjugateSpace (name parent involution : String) (span : Span)
  | derivedBasis (name parent space : String) (span : Span)
  | metric (name basis involution : String) (orthonormal : Bool) (span : Span)
  | vector (name basis : String) (access : Access) (initializes : Bool) (span : Span)
  deriving Repr, Inhabited

def Parameter.name : Parameter → String
  | .owned name .. | .borrowed name .. | .space name .. | .basis name .. | .map name .. | .ownedMap name .. => name
  | .involution name .. | .dualSpace name .. | .conjugateSpace name .. | .derivedBasis name .. | .metric name .. => name
  | .vector name .. => name

def Parameter.span : Parameter → Span
  | .owned _ _ span | .borrowed _ _ _ _ _ _ span => span
  | .space _ _ _ span | .basis _ _ span | .map _ _ _ _ _ span | .ownedMap _ _ _ span => span
  | .involution _ _ span | .dualSpace _ _ span | .conjugateSpace _ _ _ span |
      .derivedBasis _ _ _ span | .metric _ _ _ _ span => span
  | .vector _ _ _ _ span => span

inductive Action where
  | allocate (owner : String) (scalar : Scalar) (elements : Nat)
  | move (source target : String)
  | drop (owner : String)
  | borrow (name source : String) (layout : Layout) (access : Access)
  | release (loan : String)
  | transpose (loan : String)
  | fill (loan : String) (value : Literal)
  | store (loan : String) (row column : Nat) (value : Literal)
  | expect (loan : String) (row column : Nat) (value : Literal)
  | copy (source target : String)
  deriving Repr, Inhabited

inductive Coefficient where
  | literal (value : Literal)
  | loan (name : String)
  deriving Repr, Inhabited

inductive NumericalOperation where
  | space (name : String) (implementation : Indexed.Source.Path) (dimension : Nat)
  | basis (name space : String)
  | involution (name space : String)
  | dualSpace (name parent : String)
  | conjugateSpace (name parent involution : String)
  | derivedBasis (name parent space : String)
  | metric (name basis involution : String) (gram : Numerical.Gram)
  | transform (name parent : String) (operation : Numerical.Transform String)
  | vector (name loan basis : String)
  | conjugateVector (name parent basis involution : String)
  | evaluate (left right output : String) (operation : Numerical.Evaluation String)
      (mode : GemmMode) (policy : NumericalPolicy) (alpha beta : Option Coefficient)
  | map (name loan source target : String)
  | ownedMap (name owner : String) (layout : Layout) (source target : String)
  | ownedView (name loan owner : String)
  | borrowOwned (name owner : String) (access : Access)
  | gemm (left right output : String) (mode : GemmMode) (policy : NumericalPolicy)
      (alpha beta : Option Coefficient := none)
  deriving Repr, Inhabited

inductive Statement where
  | action (operation : Action) (span : Span)
  | numerical (operation : NumericalOperation) (span : Span)
  | call (callee : Indexed.Source.Path) (arguments results : List String) (span : Span)
  | branch (condition : Bool) (yes no : List Statement) (span : Span)
  deriving Repr, Inhabited

structure Function where
  name : String
  parameters : List Parameter
  results : List (String × Functions.ResultType String)
  body : List Statement
  isPublic : Bool := false
  span : Span := {}
  valueType : Indexed.Core.PureType := .unit
  valueBody : Indexed.FunctionSource.Block := .mk [] (.unit {}) {}
  deriving Repr, Inhabited

structure Module where
  pureModule : Indexed.DispatchSource.Module
  functions : List Function
  deriving Repr, Inhabited

structure Package where
  id : Namespace.PackageId
  dependencies : List Namespace.Dependency
  modules : List Module
  geometryCompat : Option (Indexed.GeometryProfile Indexed.Source.Path) := none
  deriving Repr, Inhabited

structure Program where
  file : String
  root : String
  packages : List Package
  deriving Repr, Inhabited

def Function.header (function : Function) : Namespace.ResourceHeader :=
  ⟨function.name, function.isPublic, function.span⟩

/-- Keep every original declaration, import, contribution, assembly and body.
Only resource headers are reconstructed; no pure placeholder is inserted. -/
def Program.pureProgram (program : Program) : Indexed.DispatchSource.Program := {
  file := program.file, root := program.root, extended := true, editable := true, authority := true,
  packages := program.packages.map fun pkg => {
    id := pkg.id, dependencies := pkg.dependencies, geometryCompat := pkg.geometryCompat,
    modules := pkg.modules.map fun m => { m.pureModule with
      module := { m.pureModule.module with resourceFunctions := m.functions.map Function.header } } } }

def Program.owned (program : Program) : List (Indexed.DeclId × Function) :=
  program.packages.flatMap fun pkg => pkg.modules.flatMap fun m =>
    m.functions.map fun function => (⟨⟨pkg.id, m.pureModule.module.path⟩, function.name⟩, function)

def Program.entry (program : Program) : Option Nat :=
  ((program.owned.zipIdx).find? fun ((owner, _), _) => owner.name == "main" &&
    owner.scope.package.source == program.root && owner.scope.path.isEmpty).map Prod.snd

/-- These are the original pure return blocks, owned by their resource
functions. They never become callable pure namespace declarations. -/
def Program.pureFragments (program : Program) : ResourcePure.Fragments :=
  program.owned.map fun (owner, function) => (owner, {
    name := function.name, params := [], result := .data (.pure function.valueType),
    body := function.valueBody, span := function.span })

def Function.resourceNames (function : Function) : List String :=
  function.parameters.map Parameter.name ++ function.body.flatMap fun statement =>
    match statement with
    | .action (.allocate name ..) _ | .action (.move _ name) _ | .action (.borrow name ..) _ => [name]
    | .numerical (.space name ..) _ | .numerical (.basis name ..) _ | .numerical (.map name ..) _
    | .numerical (.ownedMap name ..) _ | .numerical (.ownedView name ..) _
    | .numerical (.borrowOwned name ..) _ => [name]
    | .call _ _ results _ => results
    | _ => []

inductive BindingKind where | owner | loan | numerical
  deriving Repr, Inhabited

abbrev Frame := List (String × Symbol × BindingKind)

structure Reference where
  caller : Nat
  scope : Namespace.Scope
  path : Indexed.Source.Path
  target : Namespace.Target
  callee : Nat
  deriving Repr, Inhabited

structure NumericalReference where
  caller : Nat
  reference : Indexed.Source.Reference
  deriving Repr, Inhabited

structure State where
  next : Nat := 0
  references : List Reference := []
  numericalReferences : List NumericalReference := []
  unused : Nat := 4096
  deriving Inhabited

abbrev M := StateT State Namespace.Result

def lookup (frame : Frame) (name : String) (span : Span) : Namespace.Result (Symbol × BindingKind) :=
  match frame.find? (·.1 == name) with
  | some binding => pure binding.2
  | none => Namespace.problem span "E_RESOURCE_NAME" "resource name is outside this function or branch scope"

private def bindName (index : Namespace.Indexed) (scope : Namespace.Scope) (frame : Frame)
    (name : String) (kind : BindingKind) (span : Span) : M (Frame × Symbol) := do
  let _ ← Namespace.binder index scope name span
  if frame.any (·.1 == name) then
    throw {code := "E_DUPLICATE", message := "resource binding cannot be reused or shadowed", span}
  let state ← get
  set {state with next := state.next + 1}
  return ((name, state.next, kind) :: frame, state.next)

private def lowerAction (index : Namespace.Indexed) (scope : Namespace.Scope) (frame : Frame)
    (span : Span) (operation : Action) : M (Frame × Storage.Action) := do
  let name (value : String) := Prod.fst <$> lookup frame value span
  match operation with
  | .allocate owner scalar elements =>
    let (frame, owner) ← bindName index scope frame owner .owner span
    return (frame, .allocate owner scalar elements)
  | .move source target =>
    let source ← name source
    let (frame, target) ← bindName index scope frame target .owner span
    return (frame, .move source target)
  | .drop owner => return (frame, .drop (← name owner))
  | .borrow loan source layout access =>
    let (source, kind) ← lookup frame source span
    let (frame, loan) ← bindName index scope frame loan .loan span
    let source ← match kind with
      | .owner => pure (Storage.Source.owner source)
      | .loan => pure (.loan source)
      | .numerical => throw {code := "E_RESOURCE_TYPE", message := "numerical values cannot be borrowed as storage", span}
    return (frame, .borrow loan source layout access)
  | .release loan => return (frame, .release (← name loan))
  | .transpose loan => return (frame, .transpose (← name loan))
  | .fill loan value => return (frame, .fill (← name loan) value)
  | .store loan row column value => return (frame, .store (← name loan) row column value)
  | .expect loan row column value => return (frame, .expect (← name loan) row column value)
  | .copy source target => return (frame, .copy (← name source) (← name target))

private def lowerNumerical (index : Namespace.Indexed) (caller : Nat) (scope : Namespace.Scope)
    (frame : Frame) (span : Span) (operation : NumericalOperation) : M (Frame × Numerical.Operation) := do
  let name (value : String) := Prod.fst <$> lookup frame value span
  let coefficient (value : Option Coefficient) : M (Option Storage.Coefficient) := match value with
    | none => pure none
    | some (.literal value) => pure (some (.literal value))
    | some (.loan loan) => do pure (some (.loan (← name loan)))
  match operation with
  | .space output implementation dimension =>
    let (resolved, references) ← (Indexed.Source.resolveId index scope implementation).run []
    let references := references.map (fun reference => NumericalReference.mk caller reference)
    modify fun state => {state with numericalReferences := state.numericalReferences ++ references}
    let (frame, output) ← bindName index scope frame output .numerical span
    return (frame, .space output resolved dimension)
  | .basis output space =>
    let space ← name space
    let (frame, output) ← bindName index scope frame output .numerical span
    return (frame, .basis output space)
  | .involution output space =>
    let space ← name space
    let (frame, output) ← bindName index scope frame output .numerical span
    return (frame, .involution output space)
  | .dualSpace output parent =>
    let parent ← name parent
    let (frame, output) ← bindName index scope frame output .numerical span
    return (frame, .dualSpace output parent)
  | .conjugateSpace output parent selected =>
    let parent ← name parent
    let selected ← name selected
    let (frame, output) ← bindName index scope frame output .numerical span
    return (frame, .conjugateSpace output parent selected)
  | .derivedBasis output parent space =>
    let parent ← name parent
    let space ← name space
    let (frame, output) ← bindName index scope frame output .numerical span
    return (frame, .derivedBasis output parent space)
  | .metric output basis selected gram =>
    let basis ← name basis
    let selected ← name selected
    let (frame, output) ← bindName index scope frame output .numerical span
    return (frame, .metric output basis selected gram)
  | .transform output parent operation =>
    let parent ← name parent
    let operation ← match operation with
      | .dual source target => pure (Numerical.Transform.dual (← name source) (← name target))
      | .conjugate source target selected => pure (.conjugate (← name source) (← name target) (← name selected))
      | .adjoint source target => pure (.adjoint (← name source) (← name target))
    let (frame, output) ← bindName index scope frame output .numerical span
    return (frame, .transform output parent operation)
  | .map output loan source target =>
    let loan ← name loan
    let source ← name source
    let target ← name target
    let (frame, output) ← bindName index scope frame output .numerical span
    return (frame, .map output loan source target)
  | .vector output loan basis =>
    let loan ← name loan
    let basis ← name basis
    let (frame, output) ← bindName index scope frame output .numerical span
    return (frame, .vector output loan basis)
  | .conjugateVector output parent basis selected =>
    let parent ← name parent
    let basis ← name basis
    let selected ← name selected
    let (frame, output) ← bindName index scope frame output .numerical span
    return (frame, .conjugateVector output parent basis selected)
  | .evaluate left right output operation mode policy alpha beta =>
    let operation ← match operation with
      | .dual => pure Numerical.Evaluation.dual
      | .hermitian selected => pure (.hermitian (← name selected))
    return (frame, .evaluate (← name left) (← name right) (← name output) operation mode policy
      (← coefficient alpha) (← coefficient beta))
  | .ownedMap output owner layout source target =>
    let owner ← name owner
    let source ← name source
    let target ← name target
    let (frame, output) ← bindName index scope frame output .owner span
    return (frame, .ownedMap output owner layout source target)
  | .ownedView output loan owner =>
    let loan ← name loan
    let owner ← name owner
    let (frame, output) ← bindName index scope frame output .numerical span
    return (frame, .ownedView output loan owner)
  | .borrowOwned output owner access =>
    let owner ← name owner
    let (frame, output) ← bindName index scope frame output .loan span
    return (frame, .borrowOwned output owner access)
  | .gemm left right output mode policy alpha beta =>
    return (frame, .gemm (← name left) (← name right) (← name output) mode policy
      (← coefficient alpha) (← coefficient beta))

private def lowerStatements (index : Namespace.Indexed) (owners : List Indexed.DeclId)
    (caller : Nat) (scope : Namespace.Scope) : Nat → Frame → List Statement → M (Frame × List Functions.Statement)
  | _, frame, [] => pure (frame, [])
  | 0, _, _ :: _ => throw {code := "E_LIMIT", message := "resource source exceeds traversal bound"}
  | fuel + 1, frame, first :: rest => do
    let state ← get
    if state.unused == 0 then throw {code := "E_LIMIT", message := "resource source exceeds the global statement budget"}
    set {state with unused := state.unused - 1}
    let (frame, statement) ← match first with
    | .action action span => do
      let (frame, action) ← lowerAction index scope frame span action
      pure (frame, .action action)
    | .numerical operation span => do
      let (frame, operation) ← lowerNumerical index caller scope frame span operation
      pure (frame, .numerical operation)
    | .call path arguments outputs span => do
      if arguments.length > 64 || outputs.length > 64 then
        throw {code := "E_RESOURCE_LIMIT", message := "resource call exceeds 64 arguments or owned results", span}
      let target ← Namespace.resolve index scope path.path path.span
      unless target.kind == .resourceFunction do
        throw {code := "E_TYPE", message := "resource call requires a resource function", span}
      let some callee := owners.idxOf? target.owner
        | throw {code := "E_OWNER", message := "resource target has no original body", span}
      let arguments ← arguments.mapM fun name => Prod.fst <$> lookup frame name span
      let mut frame := frame
      let mut results := []
      for output in outputs do
        let (next, symbol) ← bindName index scope frame output .owner span
        frame := next
        results := results ++ [symbol]
      modify fun state => {state with references := state.references ++ [⟨caller, scope, path, target, callee⟩]}
      pure (frame, .call callee arguments results)
    | .branch condition yes no _ => do
      let (_, yes) ← lowerStatements index owners caller scope fuel frame yes
      let (_, no) ← lowerStatements index owners caller scope fuel frame no
      pure (frame, .branch condition yes no)
    let (frame, rest) ← lowerStatements index owners caller scope fuel frame rest
    return (frame, statement :: rest)

private def lowerFunction (index : Namespace.Indexed) (owners : List Indexed.DeclId)
    (owner : Indexed.DeclId) (function : Function) (id : Nat) : M Functions.Function := do
  if function.parameters.length > 64 || function.results.length > 64 then
    throw {code := "E_RESOURCE_LIMIT", message := "resource contract exceeds 64 inputs or outputs", span := function.span}
  modify fun state => {state with next := 0}
  let mut frame := []
  let mut parameters := []
  for parameter in function.parameters do
    let kind := match parameter with
      | .owned .. | .ownedMap .. => BindingKind.owner
      | .borrowed .. => .loan
      | _ => .numerical
    let (next, symbol) ← bindName index owner.scope frame parameter.name kind parameter.span
    let parameter ← match parameter with
      | .owned _ type _ => pure (Functions.Parameter.owned symbol type)
      | .borrowed _ scalar rows columns access initializes _ => pure (.borrowed symbol scalar rows columns access initializes)
      | .space _ implementation dimension _ => do
        let (resolved, references) ← (Indexed.Source.resolveId index owner.scope implementation).run []
        let references := references.map (fun reference => NumericalReference.mk id reference)
        modify fun state => {state with numericalReferences := state.numericalReferences ++ references}
        pure (.space symbol resolved dimension)
      | .basis _ space span => do
        let (space, _) ← lookup frame space span
        pure (.basis symbol space)
      | .involution _ space span => do
        let (space, _) ← lookup frame space span
        pure (.involution symbol space)
      | .dualSpace _ parent span => do
        let (parent, _) ← lookup frame parent span
        pure (.dualSpace symbol parent)
      | .conjugateSpace _ parent selected span => do
        let (parent, _) ← lookup frame parent span
        let (selected, _) ← lookup frame selected span
        pure (.conjugateSpace symbol parent selected)
      | .derivedBasis _ parent space span => do
        let (parent, _) ← lookup frame parent span
        let (space, _) ← lookup frame space span
        pure (.derivedBasis symbol parent space)
      | .metric _ basis selected orthonormal span => do
        let (basis, _) ← lookup frame basis span
        let (selected, _) ← lookup frame selected span
        pure (.metric symbol basis selected orthonormal)
      | .map _ source target access initializes span => do
        let (source, _) ← lookup frame source span
        let (target, _) ← lookup frame target span
        pure (.map symbol source target access initializes)
      | .vector _ basis access initializes span => do
        let (basis, _) ← lookup frame basis span
        pure (.vector symbol basis access initializes)
      | .ownedMap _ source target span => do
        let (source, _) ← lookup frame source span
        let (target, _) ← lookup frame target span
        pure (.ownedMap symbol source target)
    parameters := parameters ++ [parameter]
    frame := next
  let (resultFrame, body) ← lowerStatements index owners id owner.scope 4096 frame function.body
  let results ← function.results.mapM fun (name, type) => do
    let (symbol, _) ← lookup resultFrame name function.span
    let type ← match type with
      | .owned type => pure (Functions.ResultType.owned type)
      | .ownedMap source target => do
        -- Result dependencies are public inputs, never callee-local identities.
        let (source, _) ← lookup frame source function.span
        let (target, _) ← lookup frame target function.span
        pure (.ownedMap source target)
    return (symbol, type)
  return ⟨id, parameters, results, body⟩

structure Lowered where
  functions : List Functions.Function
  owners : List Indexed.DeclId
  references : List Reference
  numericalReferences : List NumericalReference
  deriving Inhabited

def lower (program : Program) : Namespace.Result Lowered := do
  if program.owned.length > 4096 then Namespace.problem {} "E_RESOURCE_LIMIT" "more than 4096 resource functions"
  let owners := program.owned.map Prod.fst
  let index := program.pureProgram.source.headers.indexed
  let (functions, state) ← (program.owned.zipIdx.mapM fun ((owner, function), id) =>
    lowerFunction index owners owner function id).run {}
  return ⟨functions, owners, state.references, state.numericalReferences⟩

def Reference.Valid (program : Program) (reference : Reference) : Prop :=
  (program.owned[reference.caller]?).map (fun entry => entry.1.scope) = some reference.scope ∧
  reference.target.kind = .resourceFunction ∧
  (Namespace.resolve program.pureProgram.source.headers.indexed reference.scope reference.path.path reference.path.span).toOption = some reference.target ∧
  (program.owned[reference.callee]?).map Prod.fst = some reference.target.owner

instance (program : Program) (reference : Reference) : Decidable (reference.Valid program) :=
  inferInstanceAs (Decidable (_ ∧ _))

def NumericalReference.Valid (program : Program) (reference : NumericalReference) : Prop :=
  (program.owned[reference.caller]?).map (fun entry => entry.1.scope) = some reference.reference.scope ∧
  reference.reference.Valid program.pureProgram.source.headers.indexed

instance (program : Program) (reference : NumericalReference) : Decidable (reference.Valid program) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Lowered.Valid (program : Program) (lowered : Lowered) : Prop :=
  lowered.owners = program.owned.map Prod.fst ∧
  lowered.functions.map Functions.Function.id = List.range program.owned.length ∧
  (∀ reference ∈ lowered.references, reference.Valid program) ∧
  ∀ reference ∈ lowered.numericalReferences, reference.Valid program

instance (program : Program) (lowered : Lowered) : Decidable (lowered.Valid program) := by
  unfold Lowered.Valid
  infer_instance

/-- Refuse a second, caller-supplied resource header table before constructing
one from original module bodies. It must not authorize an unresolved import. -/
private def sourceRemaining : Nat → Nat → List Statement → Option Nat
  | _, unused, [] => some unused
  | 0, _, _ :: _ | _ + 1, 0, _ :: _ => none
  | depth + 1, unused + 1, first :: rest => do
    let after ← match first with
      | .branch _ yes no _ => sourceRemaining depth (← sourceRemaining depth unused yes) no
      | .call _ arguments results _ =>
        if arguments.length ≤ 64 && results.length ≤ 64 then some unused else none
      | _ => some unused
    sourceRemaining depth after rest

def envelope (program : Program) : Namespace.Result Unit := do
  if program.owned.length > 4096 then Namespace.problem {} "E_RESOURCE_LIMIT" "more than 4096 resource functions"
  let mut unused := 4096
  for (_, function) in program.owned do
    let some after := sourceRemaining 4096 unused function.body
      | Namespace.problem function.span "E_RESOURCE_LIMIT" "resource source exceeds its global statement or call arity limit"
    unused := after
  if program.packages.any (fun pkg => pkg.modules.any fun m => !m.pureModule.module.resourceFunctions.isEmpty) then
    Namespace.problem {} "E_OWNER" "resource headers must be reconstructed from original bodies"
  for (owner, function) in program.owned do
    if (Indexed.FunctionSource.blockBindings function.valueBody).any (fun binding => function.resourceNames.contains binding.1) then
      Namespace.problem function.span "E_SHADOW" "pure return bindings cannot shadow resource bindings"
    unless (Indexed.FunctionSource.blockScopes function.resourceNames function.valueBody).all (fun lambda =>
        decide (Indexed.FunctionSource.ScopeSafe program.pureProgram.source.headers.indexed owner.scope lambda)) do
      Namespace.problem function.span "E_CAPTURE" "resource return lambdas must be independent of resource bindings"
  if let some entry := program.entry then
    let some (_, function) := program.owned[entry]? | Namespace.problem {} "E_MAIN" "missing resource main"
    unless function.valueType == .int do Namespace.problem function.span "E_MAIN" "resource main must return Int"

/-- The numerical compiler receives the exact environment accepted by the
complete source/authority checker, never a separately supplied declaration table. -/
def numericalEnvironment {source requireMain}
    (checked : Indexed.AuthoritySource.CheckedProgram source requireMain) : Indexed.Environment :=
  checked.authority.headers.declarations.resolved.declarations.indexed

structure Execution (functions : List Functions.Function) (entry : Nat) (environment : Indexed.Environment) where
  checked : Functions.Checked ⟨functions, entry⟩ environment
  accepted : Functions.check ⟨functions, entry⟩ environment = .ok checked
  numericalOrigins : checked.context.environment = environment ∧
    ∀ receipt ∈ checked.context.products.toList, receipt.environment = environment
  inputOrigins : ∀ receipt ∈ checked.context.inputs.toList, receipt.environment = environment
  outputOrigins : ∀ receipt ∈ checked.context.outputs.toList, receipt.environment = environment
  transformOrigins : ∀ receipt ∈ checked.context.transforms.toList, receipt.environment = environment
  vectorOrigins : ∀ receipt ∈ checked.context.vectorConjugates.toList, receipt.environment = environment
  evaluationOrigins : ∀ receipt ∈ checked.context.evaluations.toList, receipt.environment = environment

structure Checked (program : Program) (requireMain : Bool) where
  envelope : envelope program = .ok ()
  pureProgram : Indexed.AuthoritySource.CheckedProgram program.pureProgram (requireMain && program.entry.isNone)
  pureAccepted : Indexed.AuthoritySource.checkProgram program.pureProgram (requireMain && program.entry.isNone) = .ok pureProgram
  values : ResourcePure.Checked program.pureProgram pureProgram program.pureFragments
  lowered : Lowered
  reconstructed : lower program = .ok lowered
  provenance : lowered.Valid program
  library : Functions.CheckedLibrary lowered.functions (numericalEnvironment pureProgram)
  libraryAccepted : Functions.checkLibrary lowered.functions (numericalEnvironment pureProgram) = .ok library
  execution : (entry : Nat) → program.entry = some entry → Execution lowered.functions entry (numericalEnvironment pureProgram)

private def resourceError (program : Program) (lowered : Lowered) (environment : Indexed.Environment) (error : Storage.Error) : Diagnostic := Id.run do
  -- On rejection only, locate the first actual invalid contract/probe rather
  -- than attributing every resource diagnostic to a synthetic zero span.
  for (function, (_, source)) in lowered.functions.zip program.owned do
    if !(Functions.definitions [function]).isOk || !(Functions.probe lowered.functions function environment).isOk then
      return ⟨error.code, error.message, source.span, []⟩
  return ⟨error.code, error.message, (program.owned.head?).map (·.2.span) |>.getD {}, []⟩

def check (program : Program) (requireMain : Bool := false) : Namespace.Result (Checked program requireMain) :=
  match acceptedEnvelope : envelope program with
  | .error diagnostic => .error diagnostic
  | .ok () => match pureAccepted : Indexed.AuthoritySource.checkProgram program.pureProgram (requireMain && program.entry.isNone) with
    | .error diagnostic => .error diagnostic
    | .ok pureProgram => do
      let values ← ResourcePure.check program.pureProgram pureProgram program.pureFragments
      match reconstructed : lower program with
      | .error diagnostic => .error diagnostic
      | .ok lowered =>
        if provenance : lowered.Valid program then
          match libraryAccepted : Functions.checkLibrary lowered.functions (numericalEnvironment pureProgram) with
          | .error diagnostic => .error (resourceError program lowered (numericalEnvironment pureProgram) diagnostic)
          | .ok library => match entry : program.entry with
            | none => .ok ⟨acceptedEnvelope, pureProgram, pureAccepted, values, lowered, reconstructed, provenance,
                library, libraryAccepted, fun _ impossible => by simp [entry] at impossible⟩
            | some id => match accepted : Functions.check ⟨lowered.functions, id⟩ (numericalEnvironment pureProgram) with
              | .error diagnostic => .error (resourceError program lowered (numericalEnvironment pureProgram) diagnostic)
              | .ok executable =>
                if origins : executable.context.environment = numericalEnvironment pureProgram ∧
                    ∀ receipt ∈ executable.context.products.toList,
                      receipt.environment = numericalEnvironment pureProgram then
                  if inputOrigins : ∀ receipt ∈ executable.context.inputs.toList,
                      receipt.environment = numericalEnvironment pureProgram then
                    if outputOrigins : ∀ receipt ∈ executable.context.outputs.toList,
                        receipt.environment = numericalEnvironment pureProgram then
                      if transformOrigins : ∀ receipt ∈ executable.context.transforms.toList,
                          receipt.environment = numericalEnvironment pureProgram then
                        if vectorOrigins : ∀ receipt ∈ executable.context.vectorConjugates.toList,
                            receipt.environment = numericalEnvironment pureProgram then
                          if evaluationOrigins : ∀ receipt ∈ executable.context.evaluations.toList,
                              receipt.environment = numericalEnvironment pureProgram then
                            .ok ⟨acceptedEnvelope, pureProgram, pureAccepted, values, lowered, reconstructed, provenance,
                              library, libraryAccepted, fun actual same => by
                                have : actual = id := Option.some.inj (same.symm.trans entry)
                                subst actual
                                exact ⟨executable, accepted, origins, inputOrigins, outputOrigins, transformOrigins,
                                  vectorOrigins, evaluationOrigins⟩⟩
                          else Namespace.problem {} "E_OWNER" "evaluation lost its accepted declaration environment"
                        else Namespace.problem {} "E_OWNER" "vector conjugation lost its accepted declaration environment"
                      else Namespace.problem {} "E_OWNER" "numerical transforms lost their accepted declaration environment"
                    else Namespace.problem {} "E_OWNER" "numerical results lost their accepted declaration environment"
                  else Namespace.problem {} "E_OWNER" "numerical inputs lost their accepted declaration environment"
                else Namespace.problem {} "E_OWNER" "numerical execution lost its accepted declaration environment"
        else Namespace.problem {} "E_OWNER" "resource source identity or call provenance audit failed"

end VastitasKernel.ResourceSource
