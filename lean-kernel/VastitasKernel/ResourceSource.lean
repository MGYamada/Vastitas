import VastitasKernel.NumericalCoverage
import VastitasKernel.ResourcePure
import VastitasKernel.IndexedObservation
import VastitasKernel.CompatibilityProfile
import VastitasKernel.OperatorProfile
import VastitasKernel.AffineRealizationProfile

/-! Unresolved resource functions in the same package namespace as pure indexed
functions, dispatch and edit authority. No owner, local symbol or callee ID is
accepted from source. The public wire (`ResourceProtocol`) supplies the strict
decoder and native entry boundary. Static dimensions remain separate from runtime scalar value
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

abbrev FloatRepresentation := Storage.Realization.Representation

inductive Statement where
  | affineRealization (callee : Indexed.Source.Path) (site : Indexed.AffineRealizationProfile.Site) (result : String)
  | realization (callee : Indexed.Source.Path) (representation : Option FloatRepresentation)
      (arguments : List Indexed.Source.Path) (result : String) (into : Bool) (span : Span)
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
  /-- The `show!` observations of pure functions of the module, by function
  name (#836). Only the entry point `main` may have them
  (`checkObservations`). -/
  observations : List (String × List Indexed.Core.Observation) := []
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
  /-- The optional field `legacy_geometry` of a request (#533): the checked
  program ends with the kernel's compatibility profile of the legacy geometry
  (`CompatibilityProfile.profilePackage`). The profile is no package of the
  request: `packages` are the request's packages alone. -/
  legacyGeometry : Bool := false
  /-- Closed operator families used as values, reconstructed after wire decoding. -/
  operatorValues : List String := []
  deriving Repr, Inhabited

def Function.header (function : Function) : Namespace.ResourceHeader :=
  ⟨function.name, function.isPublic, function.span⟩

private def usesRealization : List Statement → Bool
  | [] => false
  | stmt :: rest => match stmt with
    | .realization .. | .affineRealization .. => true
    | .branch _ yes no _ | .branchValue _ yes no _ =>
      usesRealization yes || usesRealization no || usesRealization rest
    | _ => usesRealization rest
  termination_by statements => sizeOf statements

private def Program.usesFloat (program : Program) : Bool :=
  program.packages.any fun pkg => pkg.modules.any fun m =>
    m.pureModule.module.imports.any (fun i => i.path.take 2 == ["monad", "float"]) ||
      m.functions.any (fun f => usesRealization f.body)

private def affineSites : List Statement → List Indexed.AffineRealizationProfile.Site
  | [] => []
  | stmt :: rest => match stmt with
    | .affineRealization _ site _ => site :: affineSites rest
    | .branch _ yes no _ | .branchValue _ yes no _ => affineSites yes ++ affineSites no ++ affineSites rest
    | _ => affineSites rest
  termination_by statements => sizeOf statements

/-- Only used profiles are added. Affine sites contribute their mathematical
declarations to a reserved package before namespace and Core checking. -/
def Program.profile (program : Program) : List Indexed.DispatchSource.Package :=
  let sites := program.packages.flatMap fun p => p.modules.flatMap fun m => m.functions.flatMap fun f => affineSites f.body
  (if program.operatorValues.isEmpty then [] else [Indexed.OperatorProfile.package program.operatorValues]) ++
  (if program.usesFloat then [Indexed.FloatProfile.package] else []) ++
  (if sites.isEmpty then [] else [Indexed.AffineRealizationProfile.package sites]) ++
  (if program.legacyGeometry then [Indexed.CompatibilityProfile.profilePackage] else [])

/-- Keep every original declaration, import, contribution, assembly and body.
Only resource headers are reconstructed; no pure placeholder is inserted. The
compatibility profile, if any, is the last package (`Program.profile`). -/
def Program.pureProgram (program : Program) : Indexed.DispatchSource.Program := {
  file := program.file, root := program.root, extended := true, editable := true, authority := true,
  packages := program.packages.map (fun pkg => {
    id := pkg.id, dependencies := pkg.dependencies, geometryCompat := pkg.geometryCompat,
    modules := pkg.modules.map fun m => { m.pureModule with
      module := { m.pureModule.module with resourceFunctions := m.functions.map Function.header } } }) ++
    program.profile }

/-- The namespace of the request alone: that of the pure program without the
compatibility profile, which is not in the request. The price of
a request (`Namespace.priceInput`) reads its namespace only for the imports of
its modules, and the profile has none and is no dependency, so the price is
the same in this namespace and in that of the pure program. -/
def Program.requestNamespace (program : Program) : Namespace.Indexed :=
  { program with legacyGeometry := false, operatorValues := [] }.pureProgram.source.headers.indexed

private def resourceValueUses (candidate : String → Bool) (bound : Indexed.OperatorProfile.Bound) :
    List Statement → List Indexed.Source.Path × Indexed.OperatorProfile.Bound
  | [] => ([], bound)
  | stmt :: rest =>
    let (uses, after) := match stmt with
      | .value n _ b _ => (Indexed.OperatorProfile.blockValues candidate bound b, bound.insert n)
      | .callValue _ _ _ n _ _ => ([], bound.insert n)
      | .branch _ yes no _ | .branchValue _ yes no _ =>
          ((resourceValueUses candidate bound yes).1 ++ (resourceValueUses candidate bound no).1, bound)
      | _ => ([], bound)
    let tail := resourceValueUses candidate after rest
    (uses ++ tail.1, tail.2)
  termination_by stmts => sizeOf stmts

/-- Classify only value occurrences; named calls and glyphs need no wrapper.
Resolve a distinct spelling once per module using bounded namespace queries.
No match here can admit a source reference: the actual body, selection,
static target, and complete method are checked in the augmented namespace. -/
def Program.valueFamilies (p : Program) : Namespace.Result (List String) := do
  let idx := p.requestNamespace
  let mut names := []
  let mut session : Namespace.QuerySession := {index := idx}
  for pkg in p.packages do
    for m in pkg.modules do
      let me := m.pureModule
      let scope : Namespace.Scope := ⟨pkg.id, me.module.path⟩
      let modl := me.module.lookup
      let candidate := fun (n : String) => Namespace.operatorName n || modl.imports.contains n
      let scan := Indexed.OperatorProfile.blockValues candidate
      let freeMethod := fun (f : Indexed.DispatchSource.Method) => scan (.ofList (f.params.map (·.name))) f.body
      let paths := me.functions.flatMap (fun f => scan (.ofList (f.params.map (·.name))) f.body) ++
        me.methods.flatMap freeMethod ++ me.contributions.flatMap (fun c => c.methods.flatMap freeMethod) ++
        m.functions.flatMap (fun f =>
          let (uses, bound) := resourceValueUses candidate (.ofList (f.parameters.map Parameter.name)) f.body
          uses ++ scan bound f.valueBody)
      let mut visited : Std.HashSet (List String) := {}
      for path in paths do
        if visited.contains path.path then continue
        visited := visited.insert path.path
        -- Preserve diagnostics for invalid paths until ordinary elaboration.
        match session.query scope path.path path.span with
        | .error diag => if diag.code == "E_LIMIT" then throw diag else pure ()
        | .ok (t, next) =>
          session := next
          if t.owner.scope == Namespace.operatorScope && !names.contains t.owner.name then
            names := t.owner.name :: names
  return ["add","sub","mul","neg","div"].filter names.contains

def Program.owned (program : Program) : List (Indexed.DeclId × Function) :=
  program.packages.flatMap fun pkg => pkg.modules.flatMap fun m =>
    m.functions.map fun function => (⟨⟨pkg.id, m.pureModule.module.path⟩, function.name⟩, function)

/-- The observations of the program, by the function that has them. -/
def Program.observations (program : Program) : List (Indexed.DeclId × List Indexed.Core.Observation) :=
  program.packages.flatMap fun pkg => pkg.modules.flatMap fun m =>
    m.observations.map fun (name, observations) => (⟨⟨pkg.id, m.pureModule.module.path⟩, name⟩, observations)

def Program.entry (program : Program) : Option Nat :=
  ((program.owned.zipIdx).find? fun ((owner, _), _) => owner.name == "main" &&
    owner.scope.package.source == program.root && owner.scope.path.isEmpty).map Prod.snd

inductive BindingKind where
  | realization (descriptor : Realization.Descriptor)
  | interpreted (plan : Realization.Plan)
  | represented (descriptor : Realization.Descriptor) (loan : Symbol)
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

structure RealizationSite where
  owner : Indexed.DeclId
  position : List Nat
  functionId : Namespace.FunctionId
  operation : Realization.Operation
  callee : Indexed.Source.Path
  span : Span
  affine : Option Indexed.AffineRealizationProfile.Site := none
  deriving Repr, Inhabited

structure State where
  realizationSites : List RealizationSite := []
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
exact enclosing owner and structural source position. Only the live scalar
bindings that the body names enter this pure context, in frame order; resource
handles and nominal metadata never do. The whole frame still decides shadowing
and lambda independence. The names are the free names of the body, so a
binding that the body does not name cannot be observed: shadowing is rejected
and lambdas may not capture. -/
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
  let named := Indexed.FunctionSource.freeBlock [] body
  let scalarBindings := frame.reverse.filterMap fun (name, symbol, kind) => match kind with
    | .scalar type => if named.any (·.path == [name]) then some (name, symbol, type) else none
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

private def realizationTarget (index : Namespace.Indexed) (scope : Namespace.Scope)
    (caller : Nat) (path : Indexed.Source.Path) : M Namespace.Target := do
  let target ← Namespace.resolve index scope path.path path.span
  modify fun s => {s with numericalReferences := ⟨caller, ⟨scope,path,target⟩⟩ :: s.numericalReferences}
  return target

private def localArgument (frame : Frame) (p : Indexed.Source.Path) : M (Symbol × BindingKind) := do
  let [name] := p.path | Namespace.problem p.span "E_REALIZATION_POINT" "expected a local represented value"
  lookup frame name p.span

/-- Only an otherwise unbound constructor gets the edition's protected
mapping. A local import or dependency cannot transfer its authority. -/
private def resolvesAffine (index : Namespace.Indexed) (scope : Namespace.Scope)
    (callee : Indexed.Source.Path) : Bool :=
  let ctor := Namespace.affineConstructor
  callee.path == [ctor.name] && Namespace.unboundName index scope ctor.name &&
    index.byOwner[ctor]?.any (·.kind == .resourceFunction) &&
    index.byOwner[(⟨Namespace.floatScope, "realize"⟩ : Namespace.Owner)]?.any (·.kind == .resourceFunction)

private def lowerRealization (index : Namespace.Indexed) (scope : Namespace.Scope) (caller : Nat)
    (frame : Frame) (owner : Indexed.DeclId) (position : List Nat) (callee : Indexed.Source.Path)
    (rep : Option FloatRepresentation) (args : List Indexed.Source.Path) (out : String) (into : Bool)
    (span : Span) : M (Frame × Functions.Statement) := do
  if let [name] := callee.path then
    if frame.any (·.1 == name) then Namespace.problem callee.span "E_REALIZATION" "local value is not a realization function"
  let target ← Namespace.resolve index scope callee.path callee.span
  unless target.kind == .resourceFunction && target.owner.scope == Namespace.floatScope do
    Namespace.problem callee.span "E_REALIZATION" "expected a function of the selected monad::float profile"
  let ownerOf (p : Indexed.Source.Path) := do
    if let [name] := p.path then
      if frame.any (·.1 == name) then Namespace.problem p.span "E_REALIZATION" "expected an indexed declaration"
    let ref ← realizationTarget index scope caller p
    unless ref.kind == .indexedDeclaration do Namespace.problem p.span "E_REALIZATION" "expected an indexed declaration"
    return ref.owner
  let descriptorOf (p : Indexed.Source.Path) := do
    let (_, .realization d) ← localArgument frame p | Namespace.problem p.span "E_REALIZATION" "expected a realization descriptor"
    return d
  let bind (kind : BindingKind) := do return (← bindName index scope frame out kind span).1
  let (next, op) ← (match target.owner.name, rep, args, into with
    | "realize", some precision, [subject,chart], false => do
      let id ← ownerOf subject
      let "standard_chart" :: parent := chart.path.reverse
        | Namespace.problem chart.span "E_REALIZATION_CHART" "expected an explicit subject::standard_chart"
      if parent.isEmpty then Namespace.problem chart.span "E_REALIZATION_CHART" "expected an explicit chart owner"
      let c ← ownerOf ⟨parent.reverse, chart.span⟩
      unless c == id do Namespace.problem chart.span "E_REALIZATION_CHART" "chart belongs to another nominal object"
      let d : Realization.Descriptor := ⟨id,c,precision⟩
      pure (← bind (.realization d), .realize d)
    | "interpret", none, [graph,r,policy], false => do
      let shadowed := frame.any (·.1 == "NativeFast") || index.byOwner.contains ⟨scope,"NativeFast"⟩ ||
        (Namespace.moduleLookupAt index scope).any (·.imports.contains "NativeFast") ||
        index.byPackage[scope.package.source]?.any (·.dependencies.contains "NativeFast")
      unless policy.path == ["NativeFast"] && !shadowed do
        Namespace.problem policy.span "E_NUMERICAL_POLICY" "resource execution requires NativeFast"
      let d ← descriptorOf r
      let graphId ← match graph.path with
        | [binding, "identity"] => do
          if let some (_, _, .realization parent) := frame.find? (·.1 == binding) then
            unless parent.subject.scope == Namespace.affineConstructor.scope do
              Namespace.problem graph.span "E_REALIZATION" "a named mathematical subject needs an explicit graph"
            pure (Indexed.AffineRealizationProfile.identityGraph parent.subject)
          else ownerOf graph
        | _ => ownerOf graph
      let plan : Realization.Plan := ⟨d, graphId, .nativeFast⟩
      pure (← bind (.interpreted plan), .interpret plan)
    | "point", none, [r,input], false => do
      let d ← descriptorOf r
      let (loan, .loan) ← localArgument frame input
        | Namespace.problem input.span "E_REALIZATION_POINT" "expected an explicit storage loan"
      pure (← bind (.represented d loan), .point d loan)
    | "run", none, [e,input], true => do
      let (_, .interpreted plan) ← localArgument frame e | Namespace.problem e.span "E_REALIZATION" "expected an interpreted computation"
      let (_, .represented x i) ← localArgument frame input | Namespace.problem input.span "E_REALIZATION_POINT" "expected a represented input"
      let (_, .represented y o) ← lookup frame out span | Namespace.problem span "E_REALIZATION_POINT" "expected a represented destination"
      unless x == plan.descriptor && y == plan.descriptor do
        Namespace.problem span "E_REALIZATION_POINT" "represented points must use the interpreted object's chart and representation"
      pure (frame,.run plan i o)
    | _, _, _, _ => Namespace.problem span "E_ARITY" "wrong finite signature or destination for this realization operation"
    : M (Frame × Realization.Operation))
  modify fun s => {s with realizationSites := ⟨owner,position,⟨target.owner⟩,op,callee,span,none⟩ :: s.realizationSites}
  return (next, .numerical (.realization op))

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
    | .affineRealization callee site out => do
      unless resolvesAffine index scope callee && !(frame.any (·.1 == Namespace.affineConstructor.name)) do
        Namespace.problem callee.span "E_REALIZATION" "expected the edition's Affine representation constructor"
      let d := site.descriptor
      let (next, _) ← bindName index scope frame out (.realization d) site.span
      let op := Realization.Operation.realize d
      modify fun s => {s with realizationSites :=
        ⟨owner,path ++ [position],⟨⟨Namespace.floatScope,"realize"⟩⟩,op,callee,site.span,some site⟩ :: s.realizationSites}
      pure (next, .numerical (.realization op))
    | .realization callee rep args out into span =>
      lowerRealization index scope caller frame owner (path ++ [position]) callee rep args out into span
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
  realizationSites : List RealizationSite := []
  deriving Inhabited

def lower (program : Program) : Namespace.Result Lowered := do
  if program.owned.length > 4096 then Namespace.problem {} "E_RESOURCE_LIMIT" "more than 4096 resource functions"
  let owners := program.owned.map Prod.fst
  let index := program.pureProgram.source.headers.indexed
  let (functions, state) ← (program.owned.zipIdx.mapM fun ((owner, function), id) =>
    lowerFunction index owners owner function id).run {}
  return ⟨state.fragments, state.sites, functions, owners, state.references, state.numericalReferences, state.realizationSites.reverse⟩

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

/-- A Fn type of a signature with a data component other than a scalar. -/
private def invalidType (type : Indexed.FunctionSource.FnType) : Bool :=
  match type with
  | .function _ => !type.Valid
  | .data _ => false

private def invalidParameter (parameter : Indexed.FunctionSource.Param) : Option Span :=
  if invalidType parameter.type then some parameter.span else none

mutual
  private def invalidExpression : Nat → Indexed.FunctionSource.Expr → Option Span
    | 0, _ => none
    | fuel + 1, term => match term with
      | .call _ arguments _ | .finiteCall _ _ arguments _ | .finiteLookup _ arguments _ =>
        arguments.findSome? (invalidExpression fuel)
      | .invoke callee arguments _ =>
        invalidExpression fuel callee <|> arguments.findSome? (invalidExpression fuel)
      | .lambda parameters result body span =>
        parameters.findSome? invalidParameter <|> (if invalidType result then some span else none) <|>
          invalidBlock fuel body
      | .unary _ operand _ => invalidExpression fuel operand
      | .binary _ left right _ => invalidExpression fuel left <|> invalidExpression fuel right
      | .branch condition yes no _ =>
        invalidExpression fuel condition <|> invalidBlock fuel yes <|> invalidBlock fuel no
      | .block body _ => invalidBlock fuel body
      | .pack _ witness components _ =>
        invalidExpression fuel witness <|> components.findSome? (invalidExpression fuel)
      | _ => none
  private def invalidStatement : Nat → Indexed.FunctionSource.Stmt → Option Span
    | 0, _ => none
    | fuel + 1, .letE _ annotation value span =>
      (if annotation.any invalidType then some span else none) <|> invalidExpression fuel value
    | fuel + 1, .unpack value _ _ _ => invalidExpression fuel value
  private def invalidBlock : Nat → Indexed.FunctionSource.Block → Option Span
    | 0, _ => none
    | fuel + 1, .mk statements result _ =>
      statements.findSome? (invalidStatement fuel) <|> invalidExpression fuel result
end

private def invalidFunction (function : Indexed.FunctionSource.Function) : Option Span :=
  function.params.findSome? invalidParameter <|>
    (if invalidType function.result then some function.span else none) <|>
    invalidBlock Limits.sourceNesting function.body

private def invalidResource : Nat → List Statement → Option Span
  | 0, _ => none
  | fuel + 1, statements => statements.findSome? fun
    | .value _ _ body _ => invalidBlock Limits.sourceNesting body
    | .branchValue _ yes no _ | .branch _ yes no _ => invalidResource fuel yes <|> invalidResource fuel no
    | _ => none

/-- The place of the first Fn signature of the program with a data component
other than a scalar, in source order: by package and module, the functions
(their parameters, result and body), the methods and the contributions, and
then the pure blocks of the resource functions. -/
def Program.invalidSignature? (program : Program) : Option Span :=
  program.packages.findSome? fun pkg => pkg.modules.findSome? fun m =>
    m.pureModule.functions.findSome? invalidFunction <|>
    m.pureModule.methods.findSome? (fun method => invalidBlock Limits.sourceNesting method.body) <|>
    m.pureModule.contributions.findSome? (fun contribution => contribution.methods.findSome? fun method =>
      invalidBlock Limits.sourceNesting method.body) <|>
    m.functions.findSome? fun function =>
      invalidResource 4096 function.body <|> invalidBlock Limits.sourceNesting function.valueBody

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
  -- Such a signature is rejected at its place, after the namespace of the
  -- request validates (#533).
  if let some span := program.invalidSignature? then
    Namespace.validate program.requestNamespace
    Namespace.problem span "E_TYPE" "Fn signatures support scalars, finite Hom and recursive Fn types"

/-- The numerical compiler receives the exact environment accepted by the
complete source/authority checker, never a separately supplied declaration table. -/
def numericalEnvironment {source requireMain}
    (checked : Indexed.AuthoritySource.CheckedProgram source requireMain) : Indexed.Environment :=
  checked.authority.headers.declarations.resolved.declarations.indexed

/-- Index original source declarations once. Exact polynomial normalization can
erase operation order, so an extensional identity is insufficient. -/
def declaredIdentityKind : Indexed.Source.Body → Option Storage.Realization.GraphKind
  | .morphism _ _ .identity => some .smooth
  | .exactGeometry (.identity _) => some .exact
  | _ => none

def declaredIdentities (source : Indexed.Source.Program) : Std.HashSet (Indexed.DeclId × Storage.Realization.GraphKind) :=
  Std.HashSet.ofList (source.owned.filterMap fun (owner,decl) => (declaredIdentityKind decl.body).map (owner, ·))

/-- Identify the literal checked graph for each canonical chart. -/
def matchesIdentity (plan : Storage.Realization.Plan) (env : Indexed.Core.Declarations) (p : Storage.Realization.ChartProfile) : Bool :=
  match p.base with
  | .smooth .. => Id.run do
    let some (.smoothConstant app _) := env.primitive? plan.graph | return false
    let x := Indexed.Index.object (.global plan.descriptor.subject)
    return env.primitive? plan.graph == some (.smoothConstant ⟨app.family,[x,x]⟩
      (SmoothRuntime.identity p.coordinates.length))
  | .exactComplex .. => Indexed.exactView env.indexed plan.graph == some (.identity plan.descriptor.subject)

def RealizationSite.valid (identities : Std.HashSet (Indexed.DeclId × Storage.Realization.GraphKind))
    (env : Indexed.Core.Declarations) (site : RealizationSite) : Bool := Id.run do
  let d := site.operation.descriptor
  let some profile := d.profile env.indexed | return false
  unless site.functionId.owner == ⟨Namespace.floatScope,site.operation.family⟩ do return false
  match site.operation with
  | .realize _ => return site.affine.all (fun written => profile.coordinates.length == written.dimension)
  | .point .. => return true
  | .interpret plan | .run plan .. =>
    return identities.contains (plan.graph,profile.base.kind) && matchesIdentity plan env profile

def RealizationSite.resolves (index : Namespace.Indexed) (site : RealizationSite) : Bool :=
  if let some written := site.affine then
    resolvesAffine index site.owner.scope site.callee && decide (site.operation = .realize written.descriptor) &&
      site.functionId.owner == ⟨Namespace.floatScope, "realize"⟩
  else
  match Namespace.resolve index site.owner.scope site.callee.path site.callee.span with
  | .ok target => target.kind == .resourceFunction && target.owner == site.functionId.owner
  | .error _ => false

/-- Realization metadata is also checked in uncalled resource functions. -/
def validRealizations (program : Program) (env : Indexed.Core.Declarations) (sites : List RealizationSite) : Bool :=
  if sites.isEmpty then true else
    let headers := program.pureProgram.source.headers
    let index := headers.indexed
    let identities := declaredIdentities headers
    sites.all fun s => s.resolves index && s.valid identities env

/-- Physical loans are allocated per activation; the lexical run must retain
the original function, statement position and selected nominal plan. -/
def RealizationSite.matchesRun (owners : Array Indexed.DeclId) (r : Functions.RealizationRunReceipt)
    (s : RealizationSite) : Bool :=
  (r.location.source.function.bind (owners[·]?)) == some s.owner && s.position == r.location.source.path &&
    match s.operation with | .run p .. => p == r.plan | _ => false

def RunSources (lowered : Lowered) (rs : List Functions.RealizationRunReceipt) : Prop :=
  ∀ r ∈ rs, ∃ s ∈ lowered.realizationSites, s.matchesRun lowered.owners.toArray r = true

private def checkRunSources (lowered : Lowered) (rs : List Functions.RealizationRunReceipt) :
    Namespace.Result (PLift (RunSources lowered rs)) := do
  if empty : rs = [] then return ⟨by simp [RunSources,empty]⟩
  let owners := lowered.owners.toArray
  let table := lowered.realizationSites.attach.foldl (fun m s => m.insert (s.val.owner,s.val.position) s)
    ({} : Std.HashMap (Indexed.DeclId × List Nat) {s // s ∈ lowered.realizationSites})
  let findSource (r : Functions.RealizationRunReceipt) :
      Option {s // s ∈ lowered.realizationSites ∧ s.matchesRun owners r = true} := do
    let id ← r.location.source.function
    let owner ← owners[id]?
    let s ← table[(owner,r.location.source.path)]?
    if same : s.val.matchesRun owners r = true then return ⟨s.val,s.property,same⟩
    else none
  if all : rs.all (fun r => (findSource r).isSome) = true then
    return ⟨by
      intro r member
      let site := (findSource r).get ((List.all_eq_true.mp all) _ member)
      exact ⟨site.val,site.property⟩⟩
  else Namespace.problem {} "E_NUMERICAL_ORIGIN" "run receipt differs from its original source plan or location"

private def runAt : List Nat → List Functions.Statement → Option Realization.Plan
  | [i], block => do
    let .numerical (.realization (.run plan ..)) ← block[i]? | none
    return plan
  | i :: arm :: path, block => do
    let .branch _ yes no ← block[i]? | none
    if arm == 0 then runAt path yes else if arm == 1 then runAt path no else none
  | [], _ => none

def sourceRun (functions : List Functions.Function) (site : Functions.NumericalSourceSite) : Option Realization.Plan := do
  let id ← site.function
  let f ← functions.find? (·.id == id)
  runAt site.path f.body

structure Execution (functions : List Functions.Function) (entry : Nat) (environment : Indexed.Environment)
    (signatures : List ValueFlow.Signature := []) where
  checked : Functions.Checked ⟨functions, entry⟩ environment signatures
  accepted : Functions.check ⟨functions, entry⟩ environment signatures = .ok checked
  numericalCoverage : NumericalCoverage.audit functions entry checked.context = true
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
  realizationOrigins : ∀ receipt ∈ checked.context.realizationRuns.toList,
    receipt.environment = environment ∧ sourceRun functions receipt.location.source = some receipt.plan

/-- The diagnostic of a `show!` outside the top-level `let` statements of the
entry point, as the frontend reports it. -/
def misplacedObservation : String :=
  "`show!` is allowed only as the whole initializer of a `let` statement at the top level of `fn main`"

/-- The compiled entry point does not bind the top-level statements of its
source in order. Elaboration keeps them, so no accepted program reaches it. -/
private def unbound (span : Span) : Namespace.Result α :=
  Namespace.problem span "E_INTERNAL_OBSERVATION" "the compiled entry point does not bind its top-level statements in order"

/-- The observations of the entry point, checked independently of the
frontend (#836): only the pure entry point `main` has them; each names a
top-level `let` statement of its body, each statement at most once and in the
order of the statements; and its value, in the compiled Core of the checked
pure program, has a type that `show!` writes. The labels are presentation only
and are not checked. -/
def checkObservations (program : Program) {requireMain : Bool}
    (checked : Indexed.AuthoritySource.CheckedProgram program.pureProgram requireMain) :
    Namespace.Result (List Indexed.Core.Observation) := do
  let source := program.pureProgram.source
  let span (owner : Indexed.DeclId) : Span :=
    ((source.functions.find? (·.1 == owner)).map (·.2.span)).getD {}
  let entry := (Indexed.FunctionSource.Compiler.entryDefinition source).bind (source.functions[·]?)
  let mut shown : Option (List Indexed.Core.Observation) := none
  for (owner, observations) in program.observations do
    let some (main, _) := entry | Namespace.problem (span owner) "E_UNSUPPORTED" misplacedObservation
    unless owner == main do Namespace.problem (span owner) "E_UNSUPPORTED" misplacedObservation
    if shown.isSome then Namespace.problem (span owner) "E_PROTOCOL" "the entry point has two observation lists"
    shown := some observations
  let some observations := shown | return []
  let some (_, function) := entry | return []
  let .mk statements _ _ := function.body
  unless Indexed.Core.Observation.ordered observations do
    Namespace.problem function.span "E_PROTOCOL" "observations must name top-level statements of main in order"
  for observation in observations do
    match statements[observation.statement]? with
    | some (.letE ..) => pure ()
    | some (.unpack _ _ _ span) => Namespace.problem span "E_UNSUPPORTED" misplacedObservation
    | none => Namespace.problem function.span "E_PROTOCOL" "an observation names no top-level statement of main"
  let core := checked.compiled.core.module
  let some id := core.main | unbound function.span
  let some compiled := core.functions.find? (·.id == id) | unbound function.span
  let .scope body := compiled.body | unbound function.span
  let some (steps, _) := Indexed.Core.Observation.statements (Indexed.Core.Observation.extent observations) body
    | unbound function.span
  for observation in observations do
    let some (.letE _ _ _ statementSpan) := statements[observation.statement]? | unbound function.span
    let some (.letE symbol value) := steps[observation.statement]? | unbound function.span
    -- Core erases a Fn value to `Unit`; elaboration remembers it.
    if let some (_, label) := checked.executable.lowered.functionLets.find? (·.1 == symbol) then
      Namespace.problem statementSpan "E_TYPE"
        s!"`show!` cannot display a value of type {label}; it displays Int, Nat, Bool, Unit and Pair values"
    unless Indexed.Core.Observation.displayable value.result.type do
      let label := Indexed.Source.Diagnostics.typeLabel core.declarations checked.compiler.input.body.geometry {}
        value.result.type
      Namespace.problem statementSpan "E_TYPE"
        s!"`show!` cannot display a value of type {label}; it displays Int, Nat, Bool, Unit and Pair values"
  return observations

/-- The value of an accepted result with the equation that accepts it. -/
private def withAcceptance (result : Namespace.Result α) : Namespace.Result {value // result = .ok value} :=
  match result with
  | .ok value => .ok ⟨value, rfl⟩
  | .error diagnostic => .error diagnostic

structure Checked (program : Program) (requireMain : Bool) where
  envelope : envelope program = .ok ()
  pureProgram : Indexed.AuthoritySource.CheckedProgram program.pureProgram (requireMain && program.entry.isNone)
  pureAccepted : Indexed.AuthoritySource.checkProgram program.pureProgram (requireMain && program.entry.isNone) = .ok pureProgram
  /-- The observations of the entry point (#836). -/
  observations : List Indexed.Core.Observation
  observed : checkObservations program pureProgram = .ok observations
  values : ResourcePure.Checked program.pureProgram pureProgram program.pureFragments
  targets : ResourcePure.Targets values
  lowered : Lowered
  reconstructed : lower program = .ok lowered
  provenance : lowered.Valid program
  realizations : validRealizations program pureProgram.authority.headers.declarations.resolved.declarations lowered.realizationSites = true
  library : Functions.CheckedLibrary lowered.functions (numericalEnvironment pureProgram) targets.signatures
  libraryAccepted : Functions.checkLibrary lowered.functions (numericalEnvironment pureProgram) targets.signatures = .ok library
  execution : (entry : Nat) → program.entry = some entry → Execution lowered.functions entry (numericalEnvironment pureProgram) targets.signatures
  runSources : ∀ id (same : program.entry = some id),
    RunSources lowered (execution id same).checked.context.realizationRuns.toList

private def statementSpan : Statement → Span
  | .affineRealization _ site _ => site.span
  | .value _ _ _ span | .runtime _ span | .runtimeNumerical _ span | .action _ span
  | .numerical _ span | .tensor _ span | .realization _ _ _ _ _ span => span
  | .callValue _ _ _ _ _ span | .branchValue _ _ _ span | .call _ _ _ span
  | .branch _ _ _ span | .network _ _ _ span | .tree _ _ _ _ span => span

private def statementAt : List Nat → List Statement → Option Statement
  | [], _ => none
  | [position], statements => statements[position]?
  | position :: arm :: path, statements => do
    let statement ← statements[position]?
    match statement with
    | .branch _ yes no _ | .branchValue _ yes no _ =>
      if arm == 0 then statementAt path yes
      else if arm == 1 then statementAt path no else none
    | _ => none

private def statementNames : Statement → List String
  | .value name .. => [name]
  | .action (.allocate name ..) _ | .action (.move _ name) _ | .action (.borrow name ..) _ => [name]
  | .runtime (.allocate name ..) _ | .runtime (.move _ name) _ | .runtime (.borrow name ..) _ => [name]
  | .runtimeNumerical (.space name ..) _ | .runtimeNumerical (.basis name ..) _
  | .runtimeNumerical (.map name ..) _ => [name]
  | .numerical (.space name ..) _ | .numerical (.basis name ..) _ | .numerical (.involution name ..) _
  | .numerical (.dualSpace name ..) _ | .numerical (.conjugateSpace name ..) _
  | .numerical (.derivedBasis name ..) _ | .numerical (.metric name ..) _
  | .numerical (.transform name ..) _ | .numerical (.vector name ..) _
  | .numerical (.conjugateVector name ..) _ | .numerical (.map name ..) _
  | .numerical (.ownedMap name ..) _ | .numerical (.packMap name ..) _
  | .numerical (.ownedView name ..) _ | .numerical (.borrowOwned name ..) _ => [name]
  | .numerical (.unpackMap _ space basis owner) _ => [space, basis, owner]
  | .tensor (.view name ..) _ | .tensor (.cachedPack name ..) _ => [name]
  | .call _ _ results _ => results
  | .callValue _ _ results name _ _ => results ++ [name]
  | _ => []

private def statementSymbols : Functions.Statement → List Symbol
  | .value name .. => [name]
  | .action (.allocate name ..) | .action (.move _ name) | .action (.borrow name ..) => [name]
  | .runtime (.allocate name ..) | .runtime (.move _ name) | .runtime (.borrow name ..) => [name]
  | .runtimeNumerical (.space name ..) | .runtimeNumerical (.basis name ..)
  | .runtimeNumerical (.map name ..) => [name]
  | .numerical (.space name ..) | .numerical (.basis name ..) | .numerical (.involution name ..)
  | .numerical (.dualSpace name ..) | .numerical (.conjugateSpace name ..)
  | .numerical (.derivedBasis name ..) | .numerical (.metric name ..)
  | .numerical (.transform name ..) | .numerical (.vector name ..)
  | .numerical (.conjugateVector name ..) | .numerical (.map name ..)
  | .numerical (.ownedMap name ..) | .numerical (.packMap name ..)
  | .numerical (.ownedView name ..) | .numerical (.borrowOwned name ..) => [name]
  | .numerical (.unpackMap _ space basis owner) => [space, basis, owner]
  | .tensor (.view name ..) | .tensor (.cachedPack name ..) => [name]
  | .call _ _ results => results
  | .callValue _ _ results name _ => results ++ [name]
  | _ => []

/-- Symbol, source name, introducing span and whether the binding is a vector. -/
private abbrev BindingSite := Symbol × String × Span × Bool

private def introducesVector : Statement → Bool
  | .numerical (.vector ..) _ | .numerical (.conjugateVector ..) _ => true
  | _ => false

/-- A cell statement or `release` may name a vector in place of its loan. The
note then names the vector, not a loan that the source never bound. -/
private def vectorRole : String → String
  | "loan" => "vector"
  | "source loan" => "source vector"
  | "destination loan" => "destination vector"
  | role => role

/-- Recover names only on rejection, by pairing original statements with their
actual lowered statements. Nothing is added to the accepted IR or runtime. -/
private def statementBindings : Nat → List Statement → List Functions.Statement → List BindingSite
  | 0, _, _ | _, [], _ | _, _, [] => []
  | fuel + 1, source :: sources, lowered :: rest =>
    let here := (statementSymbols lowered).zip (statementNames source) |>.map fun (symbol, name) =>
      (symbol, name, statementSpan source, introducesVector source)
    let children := match source, lowered with
      | .branch _ yes no _, .branch _ left right
      | .branchValue _ yes no _, .branch _ left right =>
        statementBindings fuel yes left ++ statementBindings fuel no right
      | _, _ => []
    here ++ children ++ statementBindings fuel sources rest

private def functionBindings (source : Function) (lowered : Functions.Function) : List BindingSite :=
  ((source.parameters.zip lowered.parameters).map fun (original, parameter) =>
    (parameter.name, original.name, original.span,
      match original with | .vector .. => true | _ => false)) ++
    statementBindings 4096 source.body lowered.body

private def siteSpan (source : Function) (place : ErrorPlace) : Span :=
  match place with
  | .header => source.span
  | .result => match source.valueBody with | .mk _ _ span => span
  | .statement position => ((statementAt position source.body).map statementSpan).getD source.span

/-- Presentation only: the parameter that `Functions.arguments` marked at the
header of a callee, with its position. The mark exists only for an argument
that the kernel has rejected and whose bases it names. This function reads
that rejection and decides no acceptance. -/
private def rejectedParameter (program : Program) (lowered : Lowered) (sites : List ErrorSite) :
    Option (Nat × Parameter) := do
  let marked (entry : ErrorSubject) := entry.role == Functions.rejectedParameterRole
  let site ← sites.find? fun site => site.place == .header && site.subjects.any marked
  let entry ← site.subjects.find? marked
  let (_, source) ← program.owned[site.function]?
  let function ← lowered.functions.find? (·.id == site.function)
  let index ← function.parameters.findIdx? (·.name == entry.name)
  let parameter ← source.parameters[index]?
  return (index, parameter)

/-- Presentation only: the sentence for a call argument in another basis than
its parameter requires. The kernel has rejected the argument before this text
is made, and nothing here decides acceptance. The call site holds the two
bases of each endpoint that the kernel reports, in the names of the caller.
The sentence is made only when the source names the argument, the parameter
and both bases of an endpoint. An endpoint with one named basis, or a site
that is no call, leaves the message of the kernel as it is. -/
private def callBasisMessage (program : Program) (lowered : Lowered) (sites : List ErrorSite)
    (primary : ErrorSite) : Option String := do
  let (index, parameter) ← rejectedParameter program lowered sites
  let (_, caller) ← program.owned[primary.function]?
  let function ← lowered.functions.find? (·.id == primary.function)
  let .statement position := primary.place | none
  let arguments ← match statementAt position caller.body with
    | some (.call _ arguments _ _) | some (.callValue _ arguments _ _ _ _) => some arguments
    | _ => none
  let argument ← arguments[index]?
  let bindings := functionBindings caller function
  let named := primary.subjects.filterMap fun entry =>
    (bindings.find? (·.1 == entry.name)).map fun binding => (entry.role, binding.2.1)
  let mut clauses : List String := []
  for endpoint in Numerical.BasisMismatch.endpoints do
    match named.lookup (Numerical.BasisMismatch.actualRole endpoint),
        named.lookup (Numerical.BasisMismatch.requiredRole endpoint) with
    | some actual, some required =>
      clauses := clauses ++ [s!"has {endpoint} `{actual}` but requires `{required}`"]
    | none, none => pure ()
    | _, _ => none
  if clauses.isEmpty then none
  return s!"argument `{argument}` for parameter `{parameter.name}` {" and ".intercalate clauses}"

private def resourceError (program : Program) (lowered : Lowered) (error : Storage.Error) : Diagnostic := Id.run do
  let owned := program.owned
  let sites := error.context.sites.filter fun site => (owned[site.function]?).isSome
  -- A rejected input contract belongs at its caller; a body failure keeps its
  -- exact statement, with caller locations retained as notes.
  let primary := sites.find? (fun site => match site.place with | .statement _ => true | _ => false)
    |>.orElse (fun _ => sites.head?)
  if let some primary := primary then
    if let some (_, source) := owned[primary.function]? then
      let span := siteSpan source primary.place
      let mut notes : List DiagnosticNote := []
      for site in sites do
        if let some (_, function) := owned[site.function]? then
          let location := siteSpan function site.place
          if location ≠ span then
            let message := match site.place with
              | .header => s!"while checking resource function `{function.name}`"
              | .result => s!"while checking the result of resource function `{function.name}`"
              | .statement position => match statementAt position function.body with
                | some (.call ..) | some (.callValue ..) => "resource callee was invoked here"
                | _ => "within this resource statement"
            unless notes.any (fun note => note.message == message && decide (note.span = location)) do
              notes := notes ++ [⟨message, location⟩]
      -- A rejected argument whose bases the kernel names: its parameter is
      -- callee context, so it precedes the operand notes.
      if let some (_, parameter) := rejectedParameter program lowered sites then
        notes := notes ++ [⟨s!"parameter `{parameter.name}` is declared here", parameter.span⟩]
      -- Function-exit subjects (leaked owners or loans) stay with the callee
      -- whose result failed, even when the primary span is its caller.
      let subjectSites := primary :: sites.filter fun site => site.place == .result && site != primary
      for site in subjectSites do
        if let some (_, original) := owned[site.function]? then
          if let some function := lowered.functions.find? (·.id == site.function) then
            let bindings := functionBindings original function
            for entry in site.subjects do
              if let some (_, name, introduced, vector) := bindings.find? (·.1 == entry.name) then
                let role := if vector then vectorRole entry.role else entry.role
                let message := s!"{role} is `{name}`, introduced here"
                unless notes.any (fun note => note.message == message && decide (note.span = introduced)) do
                  notes := notes ++ [⟨message, introduced⟩]
      let message := (callBasisMessage program lowered sites primary).getD error.message
      return ⟨error.code, message, span, notes.take 32⟩
  -- Header-only failures have no expanded statement. Never re-run every body
  -- probe merely to decorate a diagnostic.
  for (function, (_, source)) in lowered.functions.zip owned do
    if !(Functions.definitions [function]).isOk then
      return ⟨error.code, error.message, source.span, []⟩
  return ⟨error.code, error.message, (owned.head?).map (·.2.span) |>.getD {}, []⟩

/-- One origin audit of `check`: the proof of `p`, or `E_OWNER` with `message`. -/
private def requireOrigin (p : Prop) [Decidable p] (message : String) : Namespace.Result (PLift p) :=
  if h : p then pure (PLift.up h) else Namespace.problem {} "E_OWNER" message

def check (program : Program) (requireMain : Bool := false) : Namespace.Result (Checked program requireMain) :=
  match acceptedEnvelope : envelope program with
  | .error diagnostic => .error diagnostic
  | .ok () => match pureAccepted : Indexed.AuthoritySource.checkProgram program.pureProgram (requireMain && program.entry.isNone) with
    | .error diagnostic => .error diagnostic
    | .ok pureProgram => do
      let ⟨observations, observed⟩ ← withAcceptance (checkObservations program pureProgram)
      -- Without resource fragments the pure passes are those of `pureProgram`;
      -- they run once and `Wire.namespaceUnits` charges them once (#533).
      let values : ResourcePure.Checked program.pureProgram pureProgram program.pureFragments ←
        if empty : program.pureFragments.isEmpty then
          .ok (by rw [List.isEmpty_iff.mp empty]; exact ResourcePure.reuse pureProgram)
        else ResourcePure.check program.pureProgram pureProgram program.pureFragments
      let targets ← ResourcePure.checkTargets values
      match reconstructed : lower program with
      | .error diagnostic => .error diagnostic
      | .ok lowered =>
        if provenance : lowered.Valid program then do
          let identities := declaredIdentities program.pureProgram.source.headers
          let env := pureProgram.authority.headers.declarations.resolved.declarations
          let realizations ← if h : validRealizations program env lowered.realizationSites = true then pure (PLift.up h)
            else
              let span := (lowered.realizationSites.find? fun s => !s.valid identities env).map (·.span)
              Namespace.problem (span.getD {}) "E_REALIZATION" "expected the selected affine's standard chart and an identity graph with matching endpoints"
          match libraryAccepted : Functions.checkLibrary lowered.functions (numericalEnvironment pureProgram) targets.signatures with
          | .error diagnostic => .error (resourceError program lowered diagnostic)
          | .ok library => match entry : program.entry with
            | none => .ok ⟨acceptedEnvelope, pureProgram, pureAccepted, observations, observed, values, targets, lowered, reconstructed, provenance, realizations.down,
                library, libraryAccepted, (fun _ impossible => by simp [entry] at impossible),
                fun _ impossible => by simp [entry] at impossible⟩
            | some id => match reused : Functions.checkWithLibrary ⟨lowered.functions, id⟩ library with
              | .error diagnostic => .error (resourceError program lowered diagnostic)
              | .ok executable => do
                have accepted := (Functions.checkWithLibrary_eq_check ⟨lowered.functions, id⟩ library).symm.trans reused
                let coverage ← if h : NumericalCoverage.audit lowered.functions id executable.context then
                    pure (PLift.up h)
                  else Namespace.problem {} "E_NUMERICAL_ORIGIN" "numerical instructions differ from their source receipts"
                let ⟨valueReturnOrigins⟩ ← requireOrigin (executable.context.signatures = targets.signatures ∧
                    ∀ receipt ∈ executable.context.valueReturns.toList, receipt.signatures = targets.signatures ∧
                      lowered.functions.find? (·.id == receipt.call.callee) = some receipt.function)
                  "scalar return lost its exact source function or checked Core signature table"
                let ⟨origins⟩ ← requireOrigin (executable.context.environment = numericalEnvironment pureProgram ∧
                    ∀ receipt ∈ executable.context.products.toList, receipt.environment = numericalEnvironment pureProgram)
                  "numerical execution lost its accepted declaration environment"
                let ⟨inputOrigins⟩ ← requireOrigin (∀ receipt ∈ executable.context.inputs.toList,
                    receipt.environment = numericalEnvironment pureProgram)
                  "numerical inputs lost their accepted declaration environment"
                let ⟨outputOrigins⟩ ← requireOrigin (∀ receipt ∈ executable.context.outputs.toList,
                    receipt.environment = numericalEnvironment pureProgram)
                  "numerical results lost their accepted declaration environment"
                let ⟨transformOrigins⟩ ← requireOrigin (∀ receipt ∈ executable.context.transforms.toList,
                    receipt.environment = numericalEnvironment pureProgram)
                  "numerical transforms lost their accepted declaration environment"
                let ⟨networkOrigins⟩ ← requireOrigin (∀ receipt ∈ executable.context.networks.toList,
                    receipt.environment = numericalEnvironment pureProgram)
                  "networks lost their accepted declaration environment"
                let ⟨tensorViewOrigins⟩ ← requireOrigin (∀ receipt ∈ executable.context.tensorViews.toList,
                    receipt.environment = numericalEnvironment pureProgram)
                  "tensor views lost their declaration environment"
                let ⟨cacheCaptureOrigins⟩ ← requireOrigin (∀ receipt ∈ executable.context.cacheCaptures.toList,
                    receipt.cache.environment = numericalEnvironment pureProgram)
                  "packing cache lost its declaration environment"
                let ⟨cachedContractionOrigins⟩ ← requireOrigin (∀ receipt ∈ executable.context.cachedContractions.toList,
                    receipt.environment = numericalEnvironment pureProgram)
                  "cached contraction lost its declaration environment"
                let ⟨tensorPackOrigins⟩ ← requireOrigin (∀ receipt ∈ executable.context.tensorPacks.toList,
                    receipt.environment = numericalEnvironment pureProgram)
                  "tensor packing lost its declaration environment"
                let ⟨tensorContractionOrigins⟩ ← requireOrigin (∀ receipt ∈ executable.context.tensorContractions.toList,
                    receipt.environment = numericalEnvironment pureProgram)
                  "tensor contraction lost its declaration environment"
                let ⟨vectorOrigins⟩ ← requireOrigin (∀ receipt ∈ executable.context.vectorConjugates.toList,
                    receipt.environment = numericalEnvironment pureProgram)
                  "vector conjugation lost its accepted declaration environment"
                let ⟨evaluationOrigins⟩ ← requireOrigin (∀ receipt ∈ executable.context.evaluations.toList,
                    receipt.environment = numericalEnvironment pureProgram)
                  "evaluation lost its accepted declaration environment"
                let ⟨packageOrigins⟩ ← requireOrigin (∀ receipt ∈ executable.context.packages.toList,
                    receipt.environment = numericalEnvironment pureProgram)
                  "package operations lost their accepted declaration environment"
                let ⟨packageResultOrigins⟩ ← requireOrigin (∀ receipt ∈ executable.context.packageResults.toList,
                    receipt.environment = numericalEnvironment pureProgram)
                  "package results lost their accepted declaration environment"
                let ⟨adjointOrigins⟩ ← requireOrigin (∀ receipt ∈ executable.context.adjoints.toList,
                    receipt.environment = numericalEnvironment pureProgram)
                  "materialized adjoint lost its accepted declaration environment"
                let ⟨diagonalPairingOrigins⟩ ← requireOrigin (∀ receipt ∈ executable.context.diagonalPairings.toList,
                    receipt.environment = numericalEnvironment pureProgram)
                  "diagonal pairing lost its accepted declaration environment"
                let ⟨treeOrigins⟩ ← requireOrigin (∀ receipt ∈ executable.context.trees.toList,
                    receipt.environment = numericalEnvironment pureProgram)
                  "tensor trees lost their accepted declaration environment"
                let ⟨runtimeOrigins⟩ ← requireOrigin ((∀ receipt ∈ executable.context.shapes.products.toList,
                      receipt.environment = numericalEnvironment pureProgram) ∧
                    (∀ receipt ∈ executable.context.shapeInputs.toList,
                      receipt.environment = numericalEnvironment pureProgram))
                  "runtime GEMM lost its accepted declaration environment"
                let ⟨runOrigins⟩ ← requireOrigin (∀ receipt ∈ executable.context.realizationRuns.toList,
                    receipt.environment = numericalEnvironment pureProgram ∧
                    sourceRun lowered.functions receipt.location.source = some receipt.plan)
                  "realization run lost its selected source graph or checked environment"
                let links ← checkRunSources lowered executable.context.realizationRuns.toList
                let execute : (actual : Nat) → program.entry = some actual →
                    Execution lowered.functions actual (numericalEnvironment pureProgram) targets.signatures := fun actual same => by
                    have : actual = id := Option.some.inj (same.symm.trans entry)
                    subst actual
                    exact ⟨executable, accepted, coverage.down, valueReturnOrigins, origins, inputOrigins, outputOrigins, transformOrigins,
                      networkOrigins, tensorViewOrigins, cacheCaptureOrigins, cachedContractionOrigins, tensorPackOrigins, tensorContractionOrigins, vectorOrigins, evaluationOrigins, packageOrigins, packageResultOrigins, adjointOrigins, diagonalPairingOrigins, treeOrigins, runtimeOrigins.1, runtimeOrigins.2, runOrigins⟩
                .ok ⟨acceptedEnvelope, pureProgram, pureAccepted, observations, observed, values, targets, lowered,
                  reconstructed, provenance, realizations.down, library, libraryAccepted, execute, fun actual same => by
                    have : actual = id := Option.some.inj (same.symm.trans entry)
                    subst actual
                    exact links.down⟩
        else Namespace.problem {} "E_OWNER" "resource source identity or call provenance audit failed"

end VastitasKernel.ResourceSource
