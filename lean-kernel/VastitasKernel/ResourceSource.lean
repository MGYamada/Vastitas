import VastitasKernel.StorageFunctions
import VastitasKernel.ResourcePure

/-! Unresolved resource functions in the same package namespace as pure indexed
functions, dispatch and edit authority. No owner, local symbol or callee ID is
accepted from source. Public protocol 8 supplies the strict decoder and native
entry boundary. Static dimensions remain separate from runtime scalar value
flow; every pure fragment is reconstructed with its actual owner and position. -/
namespace VastitasKernel.ResourceSource
open Storage

inductive RuntimeExtent where
  | literal (value : Nat)
  | slot (name : String)
  deriving Repr, Inhabited

structure RuntimeLayout where
  rows : RuntimeExtent
  columns : RuntimeExtent
  leading : RuntimeExtent
  transposed : Bool := false
  deriving Repr, Inhabited

inductive RuntimeAction where
  | allocate (owner : String) (scalar : Scalar) (elements : RuntimeExtent) (layout : RuntimeLayout)
  | move (source target : String)
  | drop (owner : String)
  | borrow (name source : String) (access : Access)
  | release (loan : String)
  | fill (loan : String) (value : Literal)
  | expect (loan : String) (row column : Nat) (value : Literal)
  deriving Repr, Inhabited

inductive Parameter where
  | value (name : String) (type : Indexed.Core.PureType) (span : Span)
  | runtimeSpace (name : String) (implementation : Indexed.Source.Path) (dimension : RuntimeExtent) (span : Span)
  | runtimeBasis (name space : String) (span : Span)
  | runtimeMap (name source target : String) (access : Access) (initializes : Bool) (span : Span)
  | owned (name : String) (type : Functions.OwnedType) (span : Span)
  | borrowed (name : String) (scalar : Scalar) (rows columns : Nat)
      (access : Access) (initializes : Bool) (span : Span)
  | space (name : String) (implementation : Indexed.Source.Path) (dimension : Nat) (span : Span)
  | basis (name space : String) (span : Span)
  | map (name source target : String) (access : Access) (initializes : Bool) (span : Span)
  | ownedMap (name source target : String) (span : Span)
  | ownedMapTo (name source : String) (dimension : Nat) (span : Span)
  | involution (name space : String) (span : Span)
  | dualSpace (name parent : String) (span : Span)
  | conjugateSpace (name parent involution : String) (span : Span)
  | derivedBasis (name parent space : String) (span : Span)
  | metric (name basis involution : String) (orthonormal : Bool) (span : Span)
  | vector (name basis : String) (access : Access) (initializes : Bool) (span : Span)
  deriving Repr, Inhabited

def Parameter.name : Parameter → String
  | .value name .. => name
  | .runtimeSpace name .. | .runtimeBasis name .. | .runtimeMap name .. => name
  | .owned name .. | .borrowed name .. | .space name .. | .basis name .. | .map name .. | .ownedMap name .. => name
  | .involution name .. | .dualSpace name .. | .conjugateSpace name .. | .derivedBasis name .. | .metric name .. => name
  | .vector name .. | .ownedMapTo name .. => name

def Parameter.span : Parameter → Span
  | .value _ _ span => span
  | .runtimeSpace _ _ _ span | .runtimeBasis _ _ span | .runtimeMap _ _ _ _ _ span => span
  | .owned _ _ span | .borrowed _ _ _ _ _ _ span => span
  | .space _ _ _ span | .basis _ _ span | .map _ _ _ _ _ span | .ownedMap _ _ _ span => span
  | .involution _ _ span | .dualSpace _ _ span | .conjugateSpace _ _ _ span |
      .derivedBasis _ _ _ span | .metric _ _ _ _ span => span
  | .vector _ _ _ _ span | .ownedMapTo _ _ _ span => span

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

inductive RuntimeNumerical where
  | space (name : String) (implementation : Indexed.Source.Path) (dimension : RuntimeExtent)
  | basis (name space : String)
  | map (name loan source target : String)
  | gemm (left right output : String) (mode : GemmMode) (policy : NumericalPolicy)
      (alpha beta : Option Coefficient := none)
  deriving Repr, Inhabited

inductive NumericalOperation where
  | space (name : String) (implementation : Indexed.Source.Path) (dimension : Nat)
  | basis (name space : String)
  | involution (name space : String)
  | dualSpace (name parent : String)
  | conjugateSpace (name parent involution : String)
  | derivedBasis (name parent space : String)
  | metric (name basis involution : String) (gram : Numerical.Gram)
  | adjointInto (input output sourceMetric targetMetric : String) (policy : NumericalPolicy)
  | hermitianDiagonal (left right output metric scratch : String) (layout : Layout) (policy : NumericalPolicy)
  | transform (name parent : String) (operation : Numerical.Transform String)
  | vector (name loan basis : String)
  | conjugateVector (name parent basis involution : String)
  | evaluate (left right output : String) (operation : Numerical.Evaluation String)
      (mode : GemmMode) (policy : NumericalPolicy) (alpha beta : Option Coefficient)
  | map (name loan source target : String)
  | ownedMap (name owner : String) (layout : Layout) (source target : String)
  | packMap (name owner : String)
  | unpackMap (package space basis owner : String)
  | ownedView (name loan owner : String)
  | borrowOwned (name owner : String) (access : Access)
  | gemm (left right output : String) (mode : GemmMode) (policy : NumericalPolicy)
      (alpha beta : Option Coefficient := none)
  deriving Repr, Inhabited

inductive Statement where
  | value (name : String) (type : Indexed.Core.PureType) (body : Indexed.FunctionSource.Block) (span : Span)
  | runtime (operation : RuntimeAction) (span : Span)
  | runtimeNumerical (operation : RuntimeNumerical) (span : Span)
  | callValue (callee : Indexed.Source.Path) (arguments results : List String)
      (value : String) (type : Indexed.Core.PureType) (span : Span)
  | branchValue (condition : String) (yes no : List Statement) (span : Span)
  | action (operation : Action) (span : Span)
  | numerical (operation : NumericalOperation) (span : Span)
  | tensor (operation : Tensor.Operation String) (span : Span)
  | network (graph : TensorNetwork.Graph String) (output : String) (policy : NumericalPolicy) (span : Span)
  | tree (graph : TensorTree.Graph String) (output : String) (policy : NumericalPolicy)
      (plan : List (TensorTree.PlanStep String Action)) (span : Span)
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

def Function.resourceNames (function : Function) : List String :=
  function.parameters.map Parameter.name ++ function.body.flatMap fun statement =>
    match statement with
    | .runtime (.allocate name ..) _ | .runtime (.move _ name) _ | .runtime (.borrow name ..) _ => [name]
    | .runtimeNumerical (.space name ..) _ | .runtimeNumerical (.basis name ..) _
      | .runtimeNumerical (.map name ..) _ => [name]
    | .action (.allocate name ..) _ | .action (.move _ name) _ | .action (.borrow name ..) _ => [name]
    | .numerical (.space name ..) _ | .numerical (.basis name ..) _ | .numerical (.map name ..) _
    | .numerical (.ownedMap name ..) _ | .numerical (.ownedView name ..) _
    | .numerical (.borrowOwned name ..) _ => [name]
    | .tensor (.view name ..) _ | .tensor (.cachedPack name ..) _ => [name]
    | .call _ _ results _ => results
    | _ => []

inductive BindingKind where
  | owner | loan | numerical | scalar (type : Indexed.Core.PureType)
  | runtimeOwner | runtimeLoan | runtimeNumerical
  deriving Repr, BEq, Inhabited

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

structure FragmentSite where
  owner : Indexed.DeclId
  position : List Nat
  deriving Repr, BEq, DecidableEq, Inhabited

structure State where
  fragments : ResourcePure.Fragments := []
  sites : List FragmentSite := []
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

private def runtimeName (frame : Frame) (span : Span) (name : String) (expected : BindingKind) :
    Namespace.Result Symbol := do
  let (symbol, kind) ← lookup frame name span
  unless kind == expected do
    throw {code := "E_RUNTIME_TYPE", message := "runtime and static handles or numerical roles cannot be interchanged", span}
  return symbol

private def lowerRuntimeExtent (frame : Frame) (span : Span) : RuntimeExtent → Namespace.Result Shapes.Extent
  | .literal value => pure (.literal value)
  | .slot name => do
    let (symbol, kind) ← lookup frame name span
    match kind with
    | .scalar .nat | .scalar .int => pure (.slot symbol)
    | _ => throw {code := "E_RUNTIME_EXTENT", message := "runtime extent requires a live Nat or Int scalar binding", span}

private def lowerRuntimeLayout (frame : Frame) (span : Span) (layout : RuntimeLayout) :
    Namespace.Result Shapes.Layout := do
  return ⟨← lowerRuntimeExtent frame span layout.rows,
    ← lowerRuntimeExtent frame span layout.columns,
    ← lowerRuntimeExtent frame span layout.leading, layout.transposed⟩

private def lowerRuntimeAction (index : Namespace.Indexed) (scope : Namespace.Scope)
    (frame : Frame) (span : Span) : RuntimeAction → M (Frame × Shapes.Action)
  | .allocate name scalar elements layout => do
    let elements ← lowerRuntimeExtent frame span elements
    let layout ← lowerRuntimeLayout frame span layout
    let (frame, name) ← bindName index scope frame name .runtimeOwner span
    return (frame, .allocate name scalar elements layout)
  | .move source target => do
    let source ← runtimeName frame span source .runtimeOwner
    let (frame, target) ← bindName index scope frame target .runtimeOwner span
    return (frame, .move source target)
  | .drop name => return (frame, .drop (← runtimeName frame span name .runtimeOwner))
  | .borrow name source access => do
    let (source, kind) ← lookup frame source span
    let source ← match kind with
      | .runtimeOwner => pure (Storage.Source.owner source)
      | .runtimeLoan => pure (.loan source)
      | _ => throw {code := "E_RUNTIME_TYPE", message := "runtime borrow requires a runtime owner or loan", span}
    let (frame, name) ← bindName index scope frame name .runtimeLoan span
    return (frame, .borrow name source access)
  | .release name => return (frame, .release (← runtimeName frame span name .runtimeLoan))
  | .fill name value => return (frame, .fill (← runtimeName frame span name .runtimeLoan) value)
  | .expect name row column value => return (frame, .expect (← runtimeName frame span name .runtimeLoan) row column value)

private def lowerRuntimeNumerical (index : Namespace.Indexed) (caller : Nat) (scope : Namespace.Scope)
    (frame : Frame) (span : Span) : RuntimeNumerical → M (Frame × Shapes.Numerical.Operation)
  | .space name implementation dimension => do
    let dimension ← lowerRuntimeExtent frame span dimension
    let (resolved, references) ← (Indexed.Source.resolveId index scope implementation).run []
    let references := references.map (fun reference => NumericalReference.mk caller reference)
    modify fun state => {state with numericalReferences := state.numericalReferences ++ references}
    let (frame, name) ← bindName index scope frame name .runtimeNumerical span
    return (frame, .space name resolved dimension)
  | .basis name parent => do
    let parent ← runtimeName frame span parent .runtimeNumerical
    let (frame, name) ← bindName index scope frame name .runtimeNumerical span
    return (frame, .basis name parent)
  | .map name loan source target => do
    let loan ← runtimeName frame span loan .runtimeLoan
    let source ← runtimeName frame span source .runtimeNumerical
    let target ← runtimeName frame span target .runtimeNumerical
    let (frame, name) ← bindName index scope frame name .runtimeNumerical span
    return (frame, .map name loan source target)
  | .gemm left right output mode policy alpha beta => do
    let literal (value : Option Coefficient) : M (Option Storage.Coefficient) := match value with
      | none => pure none
      | some (.literal value) => pure (some (.literal value))
      | some (.loan _) => throw {code := "E_RUNTIME_COEFFICIENT", message := "runtime GEMM initially supports literal coefficients", span}
    return (frame, .gemm (← runtimeName frame span left .runtimeNumerical)
      (← runtimeName frame span right .runtimeNumerical) (← runtimeName frame span output .runtimeNumerical)
      mode policy (← literal alpha) (← literal beta))

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
      | _ => throw {code := "E_RESOURCE_TYPE", message := "non-static-storage values cannot be borrowed as static storage", span}
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
  | .adjointInto input output source target policy =>
    return (frame, .adjointInto (← name input) (← name output) (← name source) (← name target) policy)
  | .hermitianDiagonal left right output metric scratch layout policy =>
    return (frame, .hermitianDiagonal (← name left) (← name right) (← name output)
      (← name metric) (← name scratch) layout policy)
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
  | .packMap output owner =>
    let owner ← name owner
    let (frame, output) ← bindName index scope frame output .owner span
    return (frame, .packMap output owner)
  | .unpackMap package space basis owner =>
    let package ← name package
    let (frame, space) ← bindName index scope frame space .numerical span
    let (frame, basis) ← bindName index scope frame basis .numerical span
    let (frame, owner) ← bindName index scope frame owner .owner span
    return (frame, .unpackMap package space basis owner)
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

/-- Reconstruct the pure function and its argument symbols together, at the
exact enclosing owner and structural source position. Only live scalar bindings
enter this pure context; resource handles and nominal metadata never do. -/
private def fragment (index : Namespace.Indexed) (owner : Indexed.DeclId) (position : List Nat)
    (frame : Frame) (type : Indexed.Core.PureType) (body : Indexed.FunctionSource.Block)
    (span : Span) (terminal : Bool := false) : M (Nat × List Symbol) := do
  unless terminal || ValueFlow.scalar type do
    throw {code := "E_RESOURCE_VALUE", message := "resource values require Nat, Int, Bool or Unit", span}
  if (Indexed.FunctionSource.blockBindings body).any (fun binding => frame.any (·.1 == binding.1)) then
    throw {code := "E_SHADOW", message := "pure bindings cannot shadow enclosing resource or scalar bindings", span}
  unless (Indexed.FunctionSource.blockScopes (frame.map Prod.fst) body).all (fun lambda =>
      decide (Indexed.FunctionSource.ScopeSafe index owner.scope lambda)) do
    throw {code := "E_CAPTURE", message := "resource value lambdas must be independent of enclosing bindings", span}
  let scalarBindings := frame.reverse.filterMap fun (name, symbol, kind) => match kind with
    | .scalar type => some (name, symbol, type)
    | _ => none
  let params := scalarBindings.map fun (name, _, type) =>
    Indexed.FunctionSource.Param.mk name (.data (.pure type)) span
  let state ← get
  let site : FragmentSite := ⟨owner, position⟩
  if state.sites.contains site then
    throw {code := "E_OWNER", message := "pure fragment source position is duplicated", span}
  let id := state.fragments.length
  set {state with
    fragments := state.fragments ++ [(owner, ({name := owner.name, params, result := .data (.pure type), body, span} : Indexed.FunctionSource.Function))]
    sites := state.sites ++ [site]}
  return (id, scalarBindings.map (·.2.1))

private def lowerTreePlan (index : Namespace.Indexed) (scope : Namespace.Scope)
    (frame : Frame) (span : Span) (plan : List (TensorTree.PlanStep String Action)) :
    M (List TensorTree.Event) := do
  unless plan.length ≤ 1024 do throw {code := "E_TENSOR_TREE", message := "tree plan exceeds 1024 explicit steps", span}
  let mut localFrame := frame
  let mut lowered := []
  for event in plan do
    let state ← get
    if state.unused == 0 then throw {code := "E_LIMIT", message := "resource tree exceeds the global statement budget", span}
    set {state with unused := state.unused - 1}
    let name value := Prod.fst <$> lookup localFrame value span
    let (next, event) ← match event with
      | .action action => do
        let (next, action) ← lowerAction index scope localFrame span action
        pure (next, TensorTree.PlanStep.action action)
      | .view output loan axes grouping => do
        let loan ← name loan
        let axes ← (axes.mapM name : Namespace.Result (List Symbol))
        let (next, output) ← bindName index scope localFrame output .numerical span
        pure (next, .view output loan axes grouping)
      | .regroup component target => pure (localFrame, .regroup component (← name target))
      | .rebind component view => pure (localFrame, .rebind component (← name view))
      | .join output edge left right target => pure (localFrame, .join output edge left right (← name target))
    localFrame := next
    lowered := lowered ++ [event]
  return lowered

private def lowerStatements (index : Namespace.Indexed) (owners : List Indexed.DeclId)
    (caller : Nat) (scope : Namespace.Scope) (owner : Indexed.DeclId) (path : List Nat) :
    Nat → Nat → Frame → List Statement → M (Frame × List Functions.Statement)
  | _, _, frame, [] => pure (frame, [])
  | 0, _, _, _ :: _ => throw {code := "E_LIMIT", message := "resource source exceeds traversal bound"}
  | fuel + 1, position, frame, first :: rest => do
    let state ← get
    if state.unused == 0 then throw {code := "E_LIMIT", message := "resource source exceeds the global statement budget"}
    set {state with unused := state.unused - 1}
    let (frame, statement) ← (match first with
    | .value name type body span => do
      let (fragment, arguments) ← fragment index owner (path ++ [position]) frame type body span
      let (frame, symbol) ← bindName index scope frame name (.scalar type) span
      pure (frame, .value symbol fragment arguments type)
    | .runtime operation span => do
      let (frame, operation) ← lowerRuntimeAction index scope frame span operation
      pure (frame, .runtime operation)
    | .runtimeNumerical operation span => do
      let (frame, operation) ← lowerRuntimeNumerical index caller scope frame span operation
      pure (frame, .runtimeNumerical operation)
    | .action action span => do
      let (frame, action) ← lowerAction index scope frame span action
      pure (frame, .action action)
    | .tensor operation span => do
      let name value := Prod.fst <$> lookup frame value span
      let (frame, operation) ← match operation with
        | .view output loan axes grouping => do
          let loan ← name loan
          let axes ← (axes.mapM name : Namespace.Result (List Symbol))
          let (frame, output) ← bindName index scope frame output .numerical span
          pure (frame, Tensor.Operation.view output loan axes grouping)
        | .cachedPack output source target => do
          let source ← name source
          let target ← name target
          let (frame, output) ← bindName index scope frame output .numerical span
          pure (frame, .cachedPack output source target)
        | .cachedContract3 cache left right output policy =>
          pure (frame, .cachedContract3 (← name cache) (← name left) (← name right) (← name output) policy)
        | .pack source target => pure (frame, .pack (← name source) (← name target))
        | .contract3 left right output policy => pure (frame, .contract3 (← name left) (← name right) (← name output) policy)
      pure (frame, .tensor operation)
    | .tree graph output policy plan span => do
      unless graph.Bounded do throw {code := "E_TENSOR_TREE", message := "unsupported bounded tree profile", span}
      let graph ← graph.mapM (fun value => Prod.fst <$> lookup frame value span)
      let output ← Prod.fst <$> lookup frame output span
      let plan ← lowerTreePlan index scope frame span plan
      pure (frame, .tree graph output policy plan)
    | .network graph output policy span => do
      unless graph.Bounded do throw {code := "E_NETWORK", message := "unsupported two-map network profile", span}
      let graph ← graph.mapM (fun value => Prod.fst <$> lookup frame value span)
      let output := (← lookup frame output span).1
      pure (frame, .network graph output policy)
    | .numerical operation span => do
      let (frame, operation) ← lowerNumerical index caller scope frame span operation
      pure (frame, .numerical operation)
    | .call path arguments outputs span | .callValue path arguments outputs _ _ span => do
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
      if let .callValue _ _ _ name type _ := first then
        unless ValueFlow.scalar type do
          throw {code := "E_RESOURCE_VALUE", message := "resource result must be a scalar value", span}
        let (next, symbol) ← bindName index scope frame name (.scalar type) span
        pure (next, .callValue callee arguments results symbol type)
      else pure (frame, .call callee arguments results)
    | .branch _ yes no span | .branchValue _ yes no span => do
      let condition ← match first with
        | .branch condition .. => pure (ValueFlow.Condition.literal condition)
        | .branchValue condition .. => do
          let (symbol, kind) ← lookup frame condition span
          unless (match kind with | .scalar .bool => true | _ => false) do
            throw {code := "E_RESOURCE_VALUE", message := "resource branch requires a Bool scalar binding", span}
          pure (.slot symbol)
        | _ => throw {code := "E_RESOURCE_VALUE", message := "invalid branch", span}
      let (_, yes) ← lowerStatements index owners caller scope owner (path ++ [position, 0]) fuel 0 frame yes
      let (_, no) ← lowerStatements index owners caller scope owner (path ++ [position, 1]) fuel 0 frame no
      pure (frame, .branch condition yes no)
    : M (Frame × Functions.Statement))
    let (frame, rest) ← lowerStatements index owners caller scope owner path fuel (position + 1) frame rest
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
      | .value _ type _ => .scalar type
      | .runtimeSpace .. | .runtimeBasis .. | .runtimeMap .. => .runtimeNumerical
      | .owned .. | .ownedMap .. | .ownedMapTo .. => BindingKind.owner
      | .borrowed .. => .loan
      | _ => .numerical
    let (next, symbol) ← bindName index owner.scope frame parameter.name kind parameter.span
    let parameter ← match parameter with
      | .value _ type _ => pure (Functions.Parameter.value symbol type)
      | .runtimeSpace _ implementation dimension span => do
        let dimension ← lowerRuntimeExtent frame span dimension
        let (resolved, references) ← (Indexed.Source.resolveId index owner.scope implementation).run []
        let references := references.map (fun reference => NumericalReference.mk id reference)
        modify fun state => {state with numericalReferences := state.numericalReferences ++ references}
        pure (.runtimeSpace symbol resolved dimension)
      | .runtimeBasis _ parent span =>
        pure (.runtimeBasis symbol (← runtimeName frame span parent .runtimeNumerical))
      | .runtimeMap _ source target access initializes span =>
        pure (.runtimeMap symbol (← runtimeName frame span source .runtimeNumerical)
          (← runtimeName frame span target .runtimeNumerical) access initializes)
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
      | .ownedMapTo _ source dimension span => do
        let (source, _) ← lookup frame source span
        pure (.ownedMapTo symbol source dimension)
    parameters := parameters ++ [parameter]
    frame := next
  let (resultFrame, body) ← lowerStatements index owners id owner.scope owner [] 4096 0 frame function.body
  let results ← function.results.mapM fun (name, type) => do
    let (symbol, _) ← lookup resultFrame name function.span
    let type ← match type with
      | .owned type => pure (Functions.ResultType.owned type)
      | .ownedMap source target => do
        -- Result dependencies are public inputs, never callee-local identities.
        let (source, _) ← lookup frame source function.span
        let (target, _) ← lookup frame target function.span
        pure (.ownedMap source target)
      | .ownedMapTo source dimension => do
        let (source, _) ← lookup frame source function.span
        pure (.ownedMapTo source dimension)
    return (symbol, type)
  let (fragment, arguments) ← fragment index owner [function.body.length] resultFrame function.valueType function.valueBody function.span true
  return ⟨id, parameters, results, body, some (fragment, arguments, function.valueType)⟩

structure Lowered where
  fragments : ResourcePure.Fragments
  sites : List FragmentSite
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
  return ⟨state.fragments, state.sites, functions, owners, state.references, state.numericalReferences⟩

/-- All pure fragments, including terminal results, come from the exact source
lowering that produces their resource call sites. Invalid source yields no table. -/
def Program.pureFragments (program : Program) : ResourcePure.Fragments :=
  ((lower program).toOption.map Lowered.fragments).getD []

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
      | .branch _ yes no _ | .branchValue _ yes no _ => sourceRemaining depth (← sourceRemaining depth unused yes) no
      | .call _ arguments results _ | .callValue _ arguments results _ _ _ =>
        if arguments.length ≤ 64 && results.length ≤ 64 then some unused else none
      | .tree _ _ _ plan _ =>
        if plan.length ≤ unused then some (unused - plan.length) else none
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
  if let some entry := program.entry then
    let some (_, function) := program.owned[entry]? | Namespace.problem {} "E_MAIN" "missing resource main"
    unless function.valueType == .int do Namespace.problem function.span "E_MAIN" "resource main must return Int"

/-- The numerical compiler receives the exact environment accepted by the
complete source/authority checker, never a separately supplied declaration table. -/
def numericalEnvironment {source requireMain}
    (checked : Indexed.AuthoritySource.CheckedProgram source requireMain) : Indexed.Environment :=
  checked.authority.headers.declarations.resolved.declarations.indexed

structure Execution (functions : List Functions.Function) (entry : Nat) (environment : Indexed.Environment)
    (signatures : List ValueFlow.Signature := []) where
  checked : Functions.Checked ⟨functions, entry⟩ environment signatures
  accepted : Functions.check ⟨functions, entry⟩ environment signatures = .ok checked
  valueReturnOrigins : checked.context.signatures = signatures ∧
    ∀ receipt ∈ checked.context.valueReturns.toList, receipt.signatures = signatures ∧
      functions.find? (·.id == receipt.call.callee) = some receipt.function
  numericalOrigins : checked.context.environment = environment ∧
    ∀ receipt ∈ checked.context.products.toList, receipt.environment = environment
  inputOrigins : ∀ receipt ∈ checked.context.inputs.toList, receipt.environment = environment
  outputOrigins : ∀ receipt ∈ checked.context.outputs.toList, receipt.environment = environment
  transformOrigins : ∀ receipt ∈ checked.context.transforms.toList, receipt.environment = environment
  networkOrigins : ∀ receipt ∈ checked.context.networks.toList, receipt.environment = environment
  tensorViewOrigins : ∀ receipt ∈ checked.context.tensorViews.toList, receipt.environment = environment
  cacheCaptureOrigins : ∀ receipt ∈ checked.context.cacheCaptures.toList, receipt.cache.environment = environment
  cachedContractionOrigins : ∀ receipt ∈ checked.context.cachedContractions.toList, receipt.environment = environment
  tensorPackOrigins : ∀ receipt ∈ checked.context.tensorPacks.toList, receipt.environment = environment
  tensorContractionOrigins : ∀ receipt ∈ checked.context.tensorContractions.toList, receipt.environment = environment
  vectorOrigins : ∀ receipt ∈ checked.context.vectorConjugates.toList, receipt.environment = environment
  evaluationOrigins : ∀ receipt ∈ checked.context.evaluations.toList, receipt.environment = environment
  packageOrigins : ∀ receipt ∈ checked.context.packages.toList, receipt.environment = environment
  packageResultOrigins : ∀ receipt ∈ checked.context.packageResults.toList, receipt.environment = environment
  adjointOrigins : ∀ receipt ∈ checked.context.adjoints.toList, receipt.environment = environment
  diagonalPairingOrigins : ∀ receipt ∈ checked.context.diagonalPairings.toList, receipt.environment = environment
  treeOrigins : ∀ receipt ∈ checked.context.trees.toList, receipt.environment = environment
  runtimeProductOrigins : ∀ receipt ∈ checked.context.shapes.products.toList, receipt.environment = environment
  runtimeInputOrigins : ∀ receipt ∈ checked.context.shapeInputs.toList, receipt.environment = environment

structure Checked (program : Program) (requireMain : Bool) where
  envelope : envelope program = .ok ()
  pureProgram : Indexed.AuthoritySource.CheckedProgram program.pureProgram (requireMain && program.entry.isNone)
  pureAccepted : Indexed.AuthoritySource.checkProgram program.pureProgram (requireMain && program.entry.isNone) = .ok pureProgram
  values : ResourcePure.Checked program.pureProgram pureProgram program.pureFragments
  targets : ResourcePure.Targets values
  lowered : Lowered
  reconstructed : lower program = .ok lowered
  provenance : lowered.Valid program
  library : Functions.CheckedLibrary lowered.functions (numericalEnvironment pureProgram) targets.signatures
  libraryAccepted : Functions.checkLibrary lowered.functions (numericalEnvironment pureProgram) targets.signatures = .ok library
  execution : (entry : Nat) → program.entry = some entry → Execution lowered.functions entry (numericalEnvironment pureProgram) targets.signatures

private def resourceError (program : Program) (lowered : Lowered) (environment : Indexed.Environment) (signatures : List ValueFlow.Signature) (error : Storage.Error) : Diagnostic := Id.run do
  -- On rejection only, locate the first actual invalid contract/probe rather
  -- than attributing every resource diagnostic to a synthetic zero span.
  for (function, (_, source)) in lowered.functions.zip program.owned do
    if !(Functions.definitions [function]).isOk || !(Functions.probe lowered.functions function environment signatures).isOk then
      return ⟨error.code, error.message, source.span, []⟩
  return ⟨error.code, error.message, (program.owned.head?).map (·.2.span) |>.getD {}, []⟩

def check (program : Program) (requireMain : Bool := false) : Namespace.Result (Checked program requireMain) :=
  match acceptedEnvelope : envelope program with
  | .error diagnostic => .error diagnostic
  | .ok () => match pureAccepted : Indexed.AuthoritySource.checkProgram program.pureProgram (requireMain && program.entry.isNone) with
    | .error diagnostic => .error diagnostic
    | .ok pureProgram => do
      let values ← ResourcePure.check program.pureProgram pureProgram program.pureFragments
      let targets ← ResourcePure.checkTargets values
      match reconstructed : lower program with
      | .error diagnostic => .error diagnostic
      | .ok lowered =>
        if provenance : lowered.Valid program then
          match libraryAccepted : Functions.checkLibrary lowered.functions (numericalEnvironment pureProgram) targets.signatures with
          | .error diagnostic => .error (resourceError program lowered (numericalEnvironment pureProgram) targets.signatures diagnostic)
          | .ok library => match entry : program.entry with
            | none => .ok ⟨acceptedEnvelope, pureProgram, pureAccepted, values, targets, lowered, reconstructed, provenance,
                library, libraryAccepted, fun _ impossible => by simp [entry] at impossible⟩
            | some id => match accepted : Functions.check ⟨lowered.functions, id⟩ (numericalEnvironment pureProgram) targets.signatures with
              | .error diagnostic => .error (resourceError program lowered (numericalEnvironment pureProgram) targets.signatures diagnostic)
              | .ok executable =>
                if valueReturnOrigins : executable.context.signatures = targets.signatures ∧
                    ∀ receipt ∈ executable.context.valueReturns.toList, receipt.signatures = targets.signatures ∧
                      lowered.functions.find? (·.id == receipt.call.callee) = some receipt.function then
                  if origins : executable.context.environment = numericalEnvironment pureProgram ∧
                      ∀ receipt ∈ executable.context.products.toList,
                        receipt.environment = numericalEnvironment pureProgram then
                    if inputOrigins : ∀ receipt ∈ executable.context.inputs.toList,
                        receipt.environment = numericalEnvironment pureProgram then
                      if outputOrigins : ∀ receipt ∈ executable.context.outputs.toList,
                          receipt.environment = numericalEnvironment pureProgram then
                        if transformOrigins : ∀ receipt ∈ executable.context.transforms.toList,
                            receipt.environment = numericalEnvironment pureProgram then
                          if networkOrigins : ∀ receipt ∈ executable.context.networks.toList,
                              receipt.environment = numericalEnvironment pureProgram then
                            if tensorViewOrigins : ∀ receipt ∈ executable.context.tensorViews.toList,
                                receipt.environment = numericalEnvironment pureProgram then
                              if cacheCaptureOrigins : ∀ receipt ∈ executable.context.cacheCaptures.toList,
                                  receipt.cache.environment = numericalEnvironment pureProgram then
                                if cachedContractionOrigins : ∀ receipt ∈ executable.context.cachedContractions.toList,
                                    receipt.environment = numericalEnvironment pureProgram then
                                  if tensorPackOrigins : ∀ receipt ∈ executable.context.tensorPacks.toList,
                                      receipt.environment = numericalEnvironment pureProgram then
                                    if tensorContractionOrigins : ∀ receipt ∈ executable.context.tensorContractions.toList,
                                        receipt.environment = numericalEnvironment pureProgram then
                                      if vectorOrigins : ∀ receipt ∈ executable.context.vectorConjugates.toList,
                                          receipt.environment = numericalEnvironment pureProgram then
                                        if evaluationOrigins : ∀ receipt ∈ executable.context.evaluations.toList,
                                            receipt.environment = numericalEnvironment pureProgram then
                                          if packageOrigins : ∀ receipt ∈ executable.context.packages.toList,
                                              receipt.environment = numericalEnvironment pureProgram then
                                            if packageResultOrigins : ∀ receipt ∈ executable.context.packageResults.toList,
                                                receipt.environment = numericalEnvironment pureProgram then
                                              if adjointOrigins : ∀ receipt ∈ executable.context.adjoints.toList,
                                                  receipt.environment = numericalEnvironment pureProgram then
                                                if diagonalPairingOrigins : ∀ receipt ∈ executable.context.diagonalPairings.toList,
                                                    receipt.environment = numericalEnvironment pureProgram then
                                                  if treeOrigins : ∀ receipt ∈ executable.context.trees.toList,
                                                      receipt.environment = numericalEnvironment pureProgram then
                                                    if runtimeOrigins :
                                                        (∀ receipt ∈ executable.context.shapes.products.toList,
                                                          receipt.environment = numericalEnvironment pureProgram) ∧
                                                        (∀ receipt ∈ executable.context.shapeInputs.toList,
                                                          receipt.environment = numericalEnvironment pureProgram) then
                                                      .ok ⟨acceptedEnvelope, pureProgram, pureAccepted, values, targets, lowered, reconstructed, provenance,
                                                        library, libraryAccepted, fun actual same => by
                                                          have : actual = id := Option.some.inj (same.symm.trans entry)
                                                          subst actual
                                                          exact ⟨executable, accepted, valueReturnOrigins, origins, inputOrigins, outputOrigins, transformOrigins,
                                                            networkOrigins, tensorViewOrigins, cacheCaptureOrigins, cachedContractionOrigins, tensorPackOrigins, tensorContractionOrigins, vectorOrigins, evaluationOrigins, packageOrigins, packageResultOrigins, adjointOrigins, diagonalPairingOrigins, treeOrigins, runtimeOrigins.1, runtimeOrigins.2⟩⟩
                                                    else Namespace.problem {} "E_OWNER" "runtime GEMM lost its accepted declaration environment"
                                                  else Namespace.problem {} "E_OWNER" "tensor trees lost their accepted declaration environment"
                                                else Namespace.problem {} "E_OWNER" "diagonal pairing lost its accepted declaration environment"
                                              else Namespace.problem {} "E_OWNER" "materialized adjoint lost its accepted declaration environment"
                                            else Namespace.problem {} "E_OWNER" "package results lost their accepted declaration environment"
                                          else Namespace.problem {} "E_OWNER" "package operations lost their accepted declaration environment"
                                        else Namespace.problem {} "E_OWNER" "evaluation lost its accepted declaration environment"
                                      else Namespace.problem {} "E_OWNER" "vector conjugation lost its accepted declaration environment"
                                    else Namespace.problem {} "E_OWNER" "tensor contraction lost its declaration environment"
                                  else Namespace.problem {} "E_OWNER" "tensor packing lost its declaration environment"
                                else Namespace.problem {} "E_OWNER" "cached contraction lost its declaration environment"
                              else Namespace.problem {} "E_OWNER" "packing cache lost its declaration environment"
                            else Namespace.problem {} "E_OWNER" "tensor views lost their declaration environment"
                          else Namespace.problem {} "E_OWNER" "networks lost their accepted declaration environment"
                        else Namespace.problem {} "E_OWNER" "numerical transforms lost their accepted declaration environment"
                      else Namespace.problem {} "E_OWNER" "numerical results lost their accepted declaration environment"
                    else Namespace.problem {} "E_OWNER" "numerical inputs lost their accepted declaration environment"
                  else Namespace.problem {} "E_OWNER" "numerical execution lost its accepted declaration environment"
                else Namespace.problem {} "E_OWNER" "scalar return lost its exact source function or checked Core signature table"
        else Namespace.problem {} "E_OWNER" "resource source identity or call provenance audit failed"

end VastitasKernel.ResourceSource
