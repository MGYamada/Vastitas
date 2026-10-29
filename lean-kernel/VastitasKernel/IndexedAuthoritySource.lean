import VastitasKernel.IndexedDispatchCheck
import VastitasKernel.Authority

/-! Rich contribution bodies share the indexed source AST. All grants, loans,
transfers and final family/footprint checks come from the actual authority
assembler; its header placeholders never replace checking the rich bodies. -/
namespace VastitasKernel.Indexed.AuthoritySource
open DispatchSource

def supported (program : DispatchSource.Program) : Namespace.Result Unit := do
  unless program.authority && program.editable do
    Namespace.problem {} "E_PROTOCOL" "indexed authority requires explicit edit and authority input"
  if program.packages.any (fun pkg => pkg.modules.any fun m =>
      !m.module.functions.isEmpty || !m.module.methods.isEmpty || !m.module.contributions.isEmpty) then
    Namespace.problem {} "E_STAGE" "old function/method/contribution bodies cannot replace rich indexed bodies"

structure ResolvedContribution where
  header : Edit.ContributionEntry
  methods : Array DispatchSource.ResolvedMethod
  deriving Inhabited

def resolveContributions (program : DispatchSource.Program) : Namespace.Result (List ResolvedContribution) := do
  let index := program.source.headers.indexed
  program.contributions.mapM fun (scope, contribution) => do
    let (header, _) ← (Edit.lowerContribution index scope contribution.header).run []
    unless header.methods.length == contribution.methods.length do
      Namespace.problem contribution.span "E_OWNER" "contribution header lost a source method"
    let methods ← contribution.methods.zipIdx.mapM fun (method, ordinal) => do
      if method.params.any (·.ty.isFunction) then
        Namespace.problem method.span "E_TYPE" "function values are not dispatch selectors"
      let some resolved := header.methods[ordinal]?
        | Namespace.problem method.span "E_OWNER" "missing original contribution method"
      return DispatchSource.ResolvedMethod.mk ordinal scope method header.target resolved
    return ⟨header, methods.toArray⟩

inductive MethodOrigin where
  | ordinary (ordinal : Nat)
  | contribution (owner : DeclId) (ordinal : Nat)
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, DecidableEq, Hashable

structure MethodSource where
  origin : MethodOrigin
  method : DispatchSource.ResolvedMethod
  deriving Inhabited

/-- Applied order comes from the actual checked trace. A canonical contribution
ID and complete reconstructed header identify its original rich method bodies. -/
def appliedMethods (ordinary : Array DispatchSource.ResolvedMethod)
    (contributions : List ResolvedContribution) (applied : List Authority.Applied) :
    Namespace.Result (Array MethodSource) := do
  let byId := contributions.foldl (fun table contribution => table.insert contribution.header.id contribution)
    ({} : Std.HashMap DeclId ResolvedContribution)
  let mut methods := ordinary.map fun method => ⟨.ordinary method.ordinal, method⟩
  for application in applied do
    let some original := byId[application.contribution.id]?
      | Namespace.problem application.contribution.span "E_OWNER" "applied contribution has no rich source declaration"
    unless original.header == application.contribution do
      Namespace.problem application.contribution.span "E_OWNER" "applied contribution differs from its reconstructed source"
    for method in original.methods do
      methods := methods.push ⟨.contribution original.header.id method.ordinal, { method with ordinal := methods.size }⟩
  return methods

structure PreparedHeaders (program : DispatchSource.Program) where
  supported : supported program = .ok ()
  declarations : Source.CheckedDeclarations program.source.headers
  assembled : Authority.Assembled program.source.headers.indexed
  assembledFrom : Authority.assemble program.source.headers.indexed = .ok assembled
  ordinary : Array DispatchSource.ResolvedMethod
  ordinaryFrom : DispatchSource.resolveMethods program = .ok ordinary
  ordinaryValid : DispatchSource.methodOriginsValid program assembled.prepared.core.base ordinary = true
  contributions : List ResolvedContribution
  contributionsFrom : resolveContributions program = .ok contributions
  contributionHeaders : contributions.map (·.header) = assembled.prepared.core.contributions
  methods : Array MethodSource
  methodsFrom : appliedMethods ordinary contributions assembled.state.applied = .ok methods
  finalHeaders : methods.toList.map (·.method.header) = (Authority.finalSurface assembled.prepared assembled.state).methods
  validated : ((DispatchChecker.validateProgram (Surface.headers
    (Authority.finalSurface assembled.prepared assembled.state))).run {}).map Prod.fst = .ok ()
  scopes : program.scopesSafe = true

def prepareHeaders (program : DispatchSource.Program) : Namespace.Result (PreparedHeaders program) := do
  match support : supported program with
  | .error diagnostic => .error diagnostic
  | .ok () =>
    let declarations ← Source.checkDeclarations program.source.headers
    match assembledFrom : Authority.assemble program.source.headers.indexed with
    | .error diagnostic => .error diagnostic
    | .ok assembled =>
      match ordinaryFrom : DispatchSource.resolveMethods program with
      | .error diagnostic => .error diagnostic
      | .ok ordinary =>
        if ordinaryValid : DispatchSource.methodOriginsValid program assembled.prepared.core.base ordinary = true then
          match contributionsFrom : resolveContributions program with
          | .error diagnostic => .error diagnostic
          | .ok contributions =>
            if contributionHeaders : contributions.map (·.header) = assembled.prepared.core.contributions then
              match methodsFrom : appliedMethods ordinary contributions assembled.state.applied with
              | .error diagnostic => .error diagnostic
              | .ok methods =>
                if finalHeaders : methods.toList.map (·.method.header) = (Authority.finalSurface assembled.prepared assembled.state).methods then
                  if scopes : program.scopesSafe = true then
                    match validated : ((DispatchChecker.validateProgram (Surface.headers
                        (Authority.finalSurface assembled.prepared assembled.state))).run {}).map Prod.fst with
                    | .error diagnostic => .error diagnostic
                    | .ok () => return ⟨support, declarations, assembled, assembledFrom, ordinary, ordinaryFrom, ordinaryValid,
                        contributions, contributionsFrom, contributionHeaders, methods, methodsFrom, finalHeaders, validated, scopes⟩
                  else .error (FunctionSource.scopeDiagnosticFor program.source.headers.indexed program.lambdaScopes)
                else Namespace.problem {} "E_OWNER" "final method headers differ from the checked authority assembly"
            else Namespace.problem {} "E_OWNER" "contribution source/header correspondence failed"
        else Namespace.problem {} "E_OWNER" "ordinary method source/header correspondence failed"

end VastitasKernel.Indexed.AuthoritySource
