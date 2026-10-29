import VastitasKernel.IndexedAuthoritySource

namespace VastitasKernel.Indexed.AuthoritySource
open DispatchSource

structure Unapplied where
  methods : Array MethodSource := #[]
  instances : List MethodInstance := []
  headers : List Surface.Function := []
  deriving Inhabited

/-- Use the final hierarchy, including keys outside the callable domain. The
complete headers are compared with the actual assembler's discarded audit;
canonical contribution IDs and original ordinals retain rich body provenance. -/
def expandUnapplied {program : Program} (prepared : PreparedHeaders program) : Namespace.Result Unapplied := do
  let mut methods := #[]
  let mut instances := #[]
  let mut headers := #[]
  let assembled := prepared.assembled
  let surface := Authority.finalSurface assembled.prepared assembled.state
  for contribution in prepared.contributions do
    if assembled.state.applied.any (·.contribution.id == contribution.header.id) then continue
    for original in contribution.methods do
      let method := original.header
      let some family := assembled.families.find? (·.raw.name == method.name)
        | Namespace.problem method.span "E_NAME" "unapplied contribution generic is absent"
      let selectors ← ((method.params.mapM fun param =>
        Abstract.selector family.nominals param.ty.core param.span).run {}).map Prod.fst
      let normalized ← (Dispatch.normalizeMethod family.nominals.hierarchy family.raw.params.length
        { id := original.ordinal, selectors, requirements := method.requirements }).mapError fun error =>
          DispatchChecker.dispatchDiagnostic family.nominals (Surface.headers surface) family.raw error
      let keys := family.checked.keys.filter (Dispatch.applicable family.nominals.hierarchy · normalized)
      if keys.isEmpty then Namespace.problem method.span "E_CAPABILITY" "unapplied method has no admitted concrete key"
      let ordinal := prepared.methods.size + methods.size
      methods := methods.push ⟨.contribution contribution.header.id original.ordinal, { original with ordinal }⟩
      for key in keys do
        if instances.size >= Limits.specializations then
          Namespace.problem method.span "E_LIMIT" "unapplied contribution audit exceeds specialization limit"
        let params ← (original.source.params.zip key).mapM fun (param, scalar) => do
          let some type := scalarType scalar
            | Namespace.problem param.span "E_TYPE" "only finite scalar types are dispatch keys"
          return FunctionSource.Param.mk param.name (.data (.pure type)) param.span
        let function : FunctionSource.Function := {
          name := original.target.owner.name, params, result := .data (.pure original.source.result),
          body := original.source.body, span := original.source.span }
        instances := instances.push ⟨ordinal, key, original.target.owner, function, original.scope⟩
        let headerParams := (method.params.zip key).map fun (param, scalar) =>
          { param with ty := .data (.named (Dispatch.nominalName scalar)) }
        let name := contribution.header.id.symbol ++ "audit_method_" ++ toString original.ordinal ++ "_" ++
          String.intercalate "_" (key.map toString)
        headers := headers.push { method.toFunction with name, params := headerParams }
  return ⟨methods, instances.toList, headers.toList⟩

structure Prepared (program : Program) where
  headers : PreparedHeaders program
  applied : List MethodInstance
  appliedFrom : expandMethods (headers.methods.map (·.method)) headers.assembled.families = .ok applied
  expansion : expansionValid headers.assembled.families applied = true
  unapplied : Unapplied
  unappliedFrom : expandUnapplied headers = .ok unapplied
  auditHeaders : headers.assembled.audit.functions =
    (Authority.finalSurface headers.assembled.prepared headers.assembled.state).functions ++ unapplied.headers

set_option maxHeartbeats 800000 in
def prepare (program : Program) : Namespace.Result (Prepared program) := do
  let headers ← prepareHeaders program
  match appliedFrom : expandMethods (headers.methods.map (·.method)) headers.assembled.families with
  | .error diagnostic => .error diagnostic
  | .ok applied =>
    if expansion : expansionValid headers.assembled.families applied = true then
      match unappliedFrom : expandUnapplied headers with
      | .error diagnostic => .error diagnostic
      | .ok unapplied =>
        if auditHeaders : headers.assembled.audit.functions =
            (Authority.finalSurface headers.assembled.prepared headers.assembled.state).functions ++ unapplied.headers then
          return ⟨headers, applied, appliedFrom, expansion, unapplied, unappliedFrom, auditHeaders⟩
        else Namespace.problem {} "E_OWNER" "unapplied body keys differ from the actual authority audit"
    else Namespace.problem {} "E_INTERNAL_DISPATCH" "applied method expansion omitted an applicable key"

def Prepared.instances {program : Program} (prepared : Prepared program) : List MethodInstance :=
  prepared.applied ++ prepared.unapplied.instances

def Prepared.methods {program : Program} (prepared : Prepared program) : Array ResolvedMethod :=
  (prepared.headers.methods ++ prepared.unapplied.methods).map (·.method)

def Prepared.seeds {program : Program} (prepared : Prepared program) :
    List (DeclId × Namespace.Scope × FunctionSource.Function) :=
  (program.source.functions.map fun (owner, function) => (owner, owner.scope, function)) ++
    prepared.instances.map fun entry => (entry.owner, entry.scope, entry.function)

def Prepared.excluded {program : Program} (prepared : Prepared program) : Std.HashSet Nat :=
  Std.HashSet.ofList (List.range prepared.unapplied.instances.length |>.map fun offset =>
    program.source.functions.length + prepared.applied.length + offset)

def Prepared.dispatcher {program : Program} (prepared : Prepared program) :
    Namespace.Result FunctionSource.Compiler.DispatchInput := do
  let byName := prepared.headers.assembled.families.foldl (fun table family => table.insert family.raw.name family)
    ({} : Std.HashMap String DispatchChecker.Family)
  let index := program.source.headers.indexed
  let mut families := {}
  for target in index.declarations do
    if target.kind == .generic then
      let some family := byName[Namespace.symbol index.toProgram target]?
        | Namespace.problem {} "E_INTERNAL_DISPATCH" "generic has no assembled finite family"
      families := families.insert target.owner family
  let definitions := prepared.applied.zipIdx.foldl (fun table (entry, ordinal) =>
    table.insert (entry.method, entry.key) (program.source.functions.length + ordinal))
    ({} : Std.HashMap (Nat × Dispatch.Key) Nat)
  return ⟨families, definitions⟩

end VastitasKernel.Indexed.AuthoritySource
