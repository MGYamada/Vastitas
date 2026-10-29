import VastitasKernel.IndexedDispatchSource

namespace VastitasKernel.Indexed.DispatchSource

structure ResolvedMethod where
  ordinal : Nat
  scope : Namespace.Scope
  source : Method
  target : Namespace.Target
  header : Surface.Method
  deriving Inhabited

/-- Reconstruct method correspondence by source position and full header
resolution. The rich body is retained from that exact source position. -/
def resolveMethods (program : Program) : Namespace.Result (Array ResolvedMethod) := do
  let index := program.source.headers.indexed
  let methods ← program.methods.zipIdx.mapM fun ((scope, method), ordinal) => do
    if method.params.any (·.ty.isFunction) then
      Namespace.problem method.span "E_TYPE" "function values are not dispatch selectors"
    let action : Namespace.M ResolvedMethod := do
      let target ← Namespace.lookup index scope method.header.name method.span true
      let params ← method.params.mapM fun param => do
        return { param with ty := ← Namespace.selectorType index scope param.ty param.span }
      let header ← Namespace.function index scope { method.header.toFunction with params } target
      return ⟨ordinal, scope, method, target, { header with requirements := method.requirements }⟩
    return (← action.run []).1
  return methods.toArray

def methodOriginsValid (program : Program) (lowered : Namespace.Lowered)
    (methods : Array ResolvedMethod) : Bool :=
  let index := program.source.headers.indexed
  methods.size == program.methods.length && methods.size == lowered.surface.methods.length &&
    methods.toList.zipIdx.all fun (method, ordinal) =>
      method.ordinal == ordinal && decide (method.target.kind = .generic) &&
      method.scope == method.target.owner.scope &&
      decide (lowered.surface.methods[ordinal]? = some method.header) &&
      decide ((Namespace.resolve index method.scope
        method.source.target.path method.source.target.span).toOption = some method.target)

structure MethodInstance where
  method : Nat
  key : Dispatch.Key
  owner : DeclId
  function : FunctionSource.Function
  scope : Namespace.Scope := owner.scope
  deriving Inhabited

def scalarType : Nat → Option Core.PureType
  | 0 => some .nat | 1 => some .int | 2 => some .bool | 3 => some .unit | _ => none

def expandMethods (methods : Array ResolvedMethod) (families : List DispatchChecker.Family) :
    Namespace.Result (List MethodInstance) := do
  let mut instances := #[]
  for family in families do
    for (ordinal, key) in family.checked.applicablePairs do
      let some method := methods[ordinal]?
        | Namespace.problem {} "E_INTERNAL_DISPATCH" "applicable method has no original body"
      unless method.header.name == family.raw.name && method.source.params.length == key.length do
        Namespace.problem method.source.span "E_INTERNAL_DISPATCH" "method expansion changed family or arity"
      let params ← (method.source.params.zip key).mapM fun (param, scalar) => do
        let some type := scalarType scalar
          | Namespace.problem param.span "E_TYPE" "only finite scalar types are dispatch keys"
        return FunctionSource.Param.mk param.name (.data (.pure type)) param.span
      let function : FunctionSource.Function := {
        name := method.target.owner.name, params, result := .data (.pure method.source.result),
        body := method.source.body, span := method.source.span }
      instances := instances.push ⟨ordinal, key, method.target.owner, function, method.scope⟩
  return instances.toList

def expansionValid (families : List DispatchChecker.Family) (instances : List MethodInstance) : Bool :=
  instances.map (fun entry => (entry.method, entry.key)) == families.flatMap (·.checked.applicablePairs)

structure Prepared (program : Program) where
  supported : supported program = .ok ()
  declarations : Source.CheckedDeclarations program.source.headers
  lowered : Namespace.Lowered
  namespaceFrom : Namespace.lower program.source.headers.indexed = .ok lowered
  graph : Namespace.MembershipGraph
  graphFrom : Namespace.membershipGraph program.source.headers.indexed = .ok graph
  memberships : Namespace.MembershipsAuthorized graph
  references : Namespace.ReferencesValid program.source.headers.indexed lowered
  validated : ((DispatchChecker.validateProgram (Surface.headers lowered.surface)).run {}).map Prod.fst = .ok ()
  methods : Array ResolvedMethod
  methodsFrom : resolveMethods program = .ok methods
  origins : methodOriginsValid program lowered methods = true
  families : List DispatchChecker.Family
  familiesFrom : ((DispatchChecker.prepareFamilies (Surface.headers lowered.surface)).run {}).map Prod.fst = .ok families
  instances : List MethodInstance
  expanded : expandMethods methods families = .ok instances
  expansion : expansionValid families instances = true
  scopes : program.scopesSafe = true

def prepare (program : Program) : Namespace.Result (Prepared program) := do
  match support : supported program with
  | .error diagnostic => .error diagnostic
  | .ok () =>
    let declarations ← Source.checkDeclarations program.source.headers
    match namespaceFrom : Namespace.lower program.source.headers.indexed with
    | .error diagnostic => .error diagnostic
    | .ok lowered =>
      match graphFrom : Namespace.membershipGraph program.source.headers.indexed with
      | .error diagnostic => .error diagnostic
      | .ok graph =>
        if memberships : Namespace.MembershipsAuthorized graph then
          if references : Namespace.ReferencesValid program.source.headers.indexed lowered then
            match validated : ((DispatchChecker.validateProgram (Surface.headers lowered.surface)).run {}).map Prod.fst with
            | .error diagnostic => .error diagnostic
            | .ok () =>
              match methodsFrom : resolveMethods program with
              | .error diagnostic => .error diagnostic
              | .ok methods =>
                if origins : methodOriginsValid program lowered methods = true then
                  match familiesFrom : ((DispatchChecker.prepareFamilies (Surface.headers lowered.surface)).run {}).map Prod.fst with
                  | .error diagnostic => .error diagnostic
                  | .ok families =>
                    match expanded : expandMethods methods families with
                    | .error diagnostic => .error diagnostic
                    | .ok instances =>
                      if expansion : expansionValid families instances = true then
                        if scopes : program.scopesSafe = true then
                          return ⟨support, declarations, lowered, namespaceFrom, graph, graphFrom, memberships,
                            references, validated, methods, methodsFrom, origins, families, familiesFrom, instances, expanded, expansion, scopes⟩
                        else .error (FunctionSource.scopeDiagnosticFor program.source.headers.indexed program.lambdaScopes)
                      else Namespace.problem {} "E_INTERNAL_DISPATCH" "method expansion omitted an applicable key"
                else Namespace.problem {} "E_OWNER" "method source/header correspondence failed"
          else Namespace.problem {} "E_OWNER" "dispatch namespace reference audit failed"
        else .error (Namespace.membershipAuthorityDiagnostic graph)

end VastitasKernel.Indexed.DispatchSource
