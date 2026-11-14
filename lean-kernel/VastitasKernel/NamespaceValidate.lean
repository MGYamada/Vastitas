import VastitasKernel.NamespaceResolve

/-! Symbols, the package graph, recipients, versions, the places of duplicates and
collisions, and the validation of imports, for the namespace checker
(`NamespaceChecker.lean`). -/
namespace VastitasKernel.Namespace
open Surface
-- The namespace checker uses `lexOrd` as a local instance from `ImportKey`
-- (`NamespaceResolve.lean`) on.
attribute [local instance] lexOrd

def symbol (p : Program) (target : Target) : String :=
  if target.owner.scope.package.source == p.root && target.owner.scope.path.isEmpty &&
      target.owner.name == "main" then "main" else target.owner.symbol

/-- The source names of what the lowered headers of `p` call by an internal
name: a declaration is named by its path, a binder by its source spelling. A
name that `p` does not declare (a builtin, the root `main`) is unchanged. The
table is built at the first name a diagnostic needs, so an accepted program
never pays for it. -/
def sourceNames (p : Indexed) : DispatchChecker.SourceNames :=
  let table : Thunk (Std.HashMap String String) := Thunk.mk fun _ =>
    p.declarations.foldl (fun table target =>
      let name := symbol p.toProgram target
      if name == "main" then table else table.insert name target.owner.qualified) {}
  { declaration := fun name => table.get.getD name name, binder := localSource }

/-- Presentation only. `check` is one dispatch check of the lowered headers of
`p`, as a function of the names its diagnostics use; these names reach the
text of a diagnostic and nothing else. The accepted equations state the check
under the internal names, so that none of them mentions a name. After that
check was rejected, this repeats it under the source names and returns its
diagnostic, which names each declaration as the source does. -/
def sourceDiagnostic (p : Indexed) (check : DispatchChecker.SourceNames → Result α)
    (rejected : Diagnostic) : Diagnostic :=
  match check (sourceNames p) with
  | .error diagnostic => diagnostic
  | .ok _ => rejected

def UniqueOwners (p : Indexed) : Prop :=
  (p.declarations.map (·.owner)).Nodup

/-- The proposition remains list distinctness; the executable decision uses the
shared, proved hash-set audit instead of comparing every pair of owners. -/
instance (p : Indexed) : Decidable (UniqueOwners p) :=
  decidable_of_iff (Finite.distinct (p.declarations.map (·.owner)) = true)
    (Finite.distinct_iff _)

def graphVisit : Nat → Indexed → String → List String → StateT (Std.HashSet String) Result Unit
  | 0, _, _, _ => problem {} "E_LIMIT" s!"dependency graph exceeds the {Limits.dependencyGraph}-unit budget"
  | fuel + 1, p, source, active => do
    if active.contains source then problem {} "E_CYCLE" "cyclic package dependency"
    if (← get).contains source then return
    let some pkg := packageAt p source | problem {} "E_NAME" "unknown package dependency"
    for dep in pkg.dependencies do graphVisit fuel p dep.target (source :: active)
    modify (·.insert source)

def validateGraph (p : Indexed) : Result Unit :=
  ((p.packages.forM fun pkg => graphVisit Limits.dependencyGraph p pkg.id.source []).run {}).map (·.1)

/-- Root-reachable package records, reconstructed from the unresolved graph.
No dependency of the issuing module on the recipient is required. -/
def recipientCandidates (p : Indexed) (name : String) : Result (List Package) := do
  let (_, selected) ← (graphVisit Limits.dependencyGraph p p.root []).run {}
  return p.packages.filter fun pkg => selected.contains pkg.id.source && pkg.id.name == name

/-- Resolve the complete name before inspecting module paths. A matching module
or version cannot disambiguate packages; return the full selected identity.
The original source-location rule remains confined to protocols 5–8. -/
def recipientPackage (p : Indexed) (reference : RecipientPackage) (span : Span) : Result Package := do
  match reference with
  | .source source => match packageAt p source with
    | some pkg => return pkg
    | none => problem span "E_OWNER" "edit recipient is outside the selected dependency closure"
  | .name name => match ← recipientCandidates p name with
    | [pkg] => return pkg
    | [] => problem span "E_OWNER" s!"edit recipient package '{name}' is outside the selected dependency closure"
    | _ => problem span "E_OWNER" s!"edit recipient package '{name}' is ambiguous in the selected dependency closure"

def versionNumber (s : String) : Bool :=
  !s.isEmpty && s.toList.all Char.isDigit && (s == "0" || !s.startsWith "0")

def versionIdentifiers (s : String) (prerelease : Bool) : Bool :=
  (s.splitOn ".").all fun part =>
    !part.isEmpty && part.toList.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '-')) &&
      (!prerelease || !part.toList.all Char.isDigit || versionNumber part)

def validVersion (s : String) : Bool := Id.run do
  let build := s.splitOn "+"
  if build.length > 2 || (build.length == 2 && !versionIdentifiers build[1]! false) then return false
  let pieces := build[0]!.splitOn "-"
  let numbers := pieces[0]!.splitOn "."
  return numbers.length == 3 && numbers.all versionNumber &&
    (pieces.length == 1 || versionIdentifiers (String.intercalate "-" (pieces.drop 1)) true)

def duplicateSpan [BEq α] (entries : List (α × Span)) : Span := Id.run do
  let mut seen := []
  for (key, span) in entries do
    if seen.contains key then return span
    seen := key :: seen
  return {}

def ownerLocations (p : Indexed) : List (Owner × Span) :=
  p.packages.flatMap fun pkg => pkg.modules.flatMap fun m =>
    let scope : Scope := ⟨pkg.id, m.path⟩
    (m.functions.map fun f => (⟨scope, f.name⟩, f.span)) ++
    (m.resourceFunctions.map fun f => (⟨scope, f.name⟩, f.span)) ++
    (m.generics.map fun g => (⟨scope, g.name⟩, g.span)) ++
    (m.abstractTypes.map fun t => (⟨scope, t.name⟩, t.span)) ++
    (m.grants.map fun g => (⟨scope, g.name⟩, g.span)) ++
    (m.delegations.map fun g => (⟨scope, g.name⟩, g.span)) ++
    (m.transfers.map fun t => (⟨scope, t.name⟩, t.span)) ++
    (m.contributions.map fun c => (⟨scope, c.name⟩, c.span)) ++
    (if m.path.isEmpty then [] else
      [(⟨⟨pkg.id, m.path.dropLast⟩, m.path.getLast!⟩, m.span)])

/-! Presentation only. The definitions up to `ImportWork` choose the place and
the notes of a diagnostic after a check of `validateWithWork` has rejected the
program; none of them decides acceptance. A place is the start of a
declaration in its file, and the order of places is the order of the source:
the frontend numbers the bytes of all files of a request in one sequence. -/

/-- Every declaration with its place, including the `indexed` declarations
that `Program` does not hold, in source order. -/
def declarationPlaces (p : Indexed) : List (Owner × Span) :=
  (ownerLocations p ++ p.indexedPlaces).mergeSort fun a b => a.2.start ≤ b.2.start

/-- The place of the declaration of `owner`, when the request gives one. -/
def declarationPlace (p : Indexed) (owner : Owner) : Option Span :=
  ((ownerLocations p ++ p.indexedPlaces).find? (·.1 == owner)).map (·.2)

/-- The second of two declarations of one owner in source order, with its name
and a note at the first. `UniqueOwners` decides acceptance. -/
def duplicateOwner (p : Indexed) : Diagnostic := Id.run do
  let mut seen : Std.HashMap Owner Span := {}
  for (owner, span) in declarationPlaces p do
    if let some first := seen[owner]? then
      return { code := "E_DUPLICATE", message := s!"`{owner.name}` is declared more than once in this module", span,
               notes := [{ span := first, message := "first declaration is here" }] }
    seen := seen.insert owner span
  return { code := "E_DUPLICATE", message := "duplicate declaration owner" }

private def kindWords : Kind → String
  | .module => "a module" | .function => "a function" | .generic => "a generic"
  | .abstractType => "an abstract type" | .grant => "a grant"
  | .contribution => "a contribution" | .delegation => "a delegation"
  | .transfer => "a transfer" | .indexedDeclaration => "an indexed declaration"
  | .resourceFunction => "a resource function"

/-- A name that a module binds, the words for its binding and its place. A
dependency alias has no place in a source file. -/
private structure Binding where
  name : String
  words : String
  span : Option Span

/-- The diagnostic for a module whose declarations, imports and dependency
aliases do not have distinct names. The dependency aliases of the package come
first, then the declarations and the imports of the module in source order.
The diagnostic is at the first binding whose name an earlier binding has, with
a note at the earlier binding when it has a place. `Finite.distinct` decides
acceptance. -/
def collision (p : Indexed) (pkg : Package) (m : Module) : Diagnostic := Id.run do
  let scope : Scope := ⟨pkg.id, m.path⟩
  let declarations : List Binding := (declarationPlaces p).filterMap fun (owner, span) =>
    if owner.scope == scope then
      let kind := (p.byOwner[owner]?).map (kindWords ·.kind)
      some ⟨owner.name, s!"{kind.getD "a declaration"} of this module", some span⟩
    else none
  let imports : List Binding := m.imports.map fun entry => ⟨entry.alias, "an import of this module", some entry.span⟩
  let placed := (declarations ++ imports).mergeSort fun a b =>
    (a.span.map (·.start)).getD 0 ≤ (b.span.map (·.start)).getD 0
  let aliases : List Binding := pkg.dependencies.map fun dep => ⟨dep.alias, "a dependency alias of this package", none⟩
  let mut seen : Std.HashMap String Binding := {}
  for binding in aliases ++ placed do
    if let some first := seen[binding.name]? then
      return { code := "E_DUPLICATE", message := s!"'{binding.name}' is already the name of {first.words}",
               span := binding.span.getD m.span,
               notes := first.span.toList.map fun span => { span, message := "first declaration is here" } }
    seen := seen.insert binding.name binding
  return { code := "E_DUPLICATE", message := "declaration, import, or dependency alias collision", span := m.span }

structure ImportWork where
  units : Nat
  bounded : units ≤ Limits.namespaceImportWork

def ImportWork.add (work : ImportWork) (consumed : Nat) (span : Span) : Result ImportWork :=
  let next := work.units + consumed
  if h : next ≤ Limits.namespaceImportWork then
    .ok ⟨next, h⟩
  else problem span "E_LIMIT" s!"program-wide namespace import validation exceeds {Limits.namespaceImportWork} member visits"

theorem ImportWork.add_exact {prior next : ImportWork} {amount : Nat} {span : Span}
    (ok : prior.add amount span = .ok next) : next.units = prior.units + amount := by
  unfold ImportWork.add at ok
  dsimp only at ok
  split at ok
  · cases ok; rfl
  · contradiction

def importWorkStep (p : Indexed) (scope : Scope) (entry : Import) (work : ImportWork) :
    Result (Target × ImportWork) := do
  let limit := Limits.namespaceResolution
  let (target, remaining) ← (memberAt limit p scope scope entry.alias {} entry.span).run limit
  let consumed := limit - remaining
  return (target, ← work.add consumed entry.span)

theorem importWorkStep_exact {p : Indexed} {scope : Scope} {entry : Import} {prior next : ImportWork}
    {target : Target} (ok : importWorkStep p scope entry prior = .ok (target, next)) :
    ∃ remaining, (memberAt Limits.namespaceResolution p scope scope entry.alias {} entry.span).run
        Limits.namespaceResolution = .ok (target, remaining) ∧
      next.units = prior.units + (Limits.namespaceResolution - remaining) := by
  unfold importWorkStep at ok
  cases actual : (memberAt Limits.namespaceResolution p scope scope entry.alias {} entry.span).run
      Limits.namespaceResolution with
  | error diagnostic => simp [actual, bind, Except.bind] at ok
  | ok pair =>
    rcases pair with ⟨value, remaining⟩
    cases debit : prior.add (Limits.namespaceResolution - remaining) entry.span with
    | error diagnostic => simp [actual, debit, bind, Except.bind] at ok
    | ok result =>
      have pair : (value, result) = (target, next) := by
        simpa [actual, debit, bind, Except.bind, pure, Except.pure] using ok
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
      exact ⟨remaining, rfl, ImportWork.add_exact debit⟩

def validateWithWork (p : Indexed) : Result ImportWork := do
  let mut work : ImportWork := ⟨0, Nat.zero_le _⟩
  if p.authority && !p.editable then problem {} "E_PROTOCOL" "authority requires edit input"
  if !p.authority && p.packages.any (fun pkg => pkg.modules.any fun m =>
      !m.delegations.isEmpty || !m.transfers.isEmpty || m.grants.any (·.delegable) ||
      (m.assembly.map fun a => a.events.any EditEvent.authority).getD false) then
    problem {} "E_PROTOCOL" "delegation and transfer require protocol 6"
  if !p.editable && p.packages.any (fun pkg => pkg.modules.any fun m =>
      !m.grants.isEmpty || !m.contributions.isEmpty || m.assembly.isSome) then
    problem {} "E_PROTOCOL" "edit declarations require protocol 5"
  if !p.extended && p.packages.any (fun pkg => pkg.modules.any fun m =>
      !m.abstractTypes.isEmpty || !m.subtypes.isEmpty || !m.abstractMethods.isEmpty) then
    problem {} "E_PROTOCOL" "abstract declarations require protocol 4"
  if p.packages.isEmpty || (packageAt p p.root).isNone then problem {} "E_PROTOCOL" "missing root package"
  if !Finite.distinct (p.packages.map (·.id.source)) then problem {} "E_DUPLICATE" "duplicate package location"
  if !Finite.distinct p.scopes then
    problem (duplicateSpan (p.packages.flatMap fun pkg =>
      pkg.modules.map fun m => (Scope.mk pkg.id m.path, m.span))) "E_DUPLICATE" "duplicate logical module"
  if !UniqueOwners p then throw (duplicateOwner p)
  if !Finite.distinct (p.declarations.map (symbol p.toProgram)) then problem {} "E_DUPLICATE" "conflicting generated declaration identities"
  validateGraph p
  for pkg in p.packages do
    if pkg.id.name.isEmpty || pkg.id.source.isEmpty || !validVersion pkg.id.version then
      problem {} "E_PROTOCOL" "invalid package name, location or SemVer version"
    if !(pkg.modules.any (·.path.isEmpty)) then problem {} "E_PROTOCOL" "package has no root module"
    if !Finite.distinct (pkg.dependencies.map (·.alias)) then problem {} "E_DUPLICATE" "duplicate dependency alias"
    for dep in pkg.dependencies do
      sourceName dep.alias {}
      if dep.alias == "package" then problem {} "E_RESERVED" "package is reserved as a path prefix"
    for m in pkg.modules do
      let scope : Scope := ⟨pkg.id, m.path⟩
      for part in m.path do
        moduleName part m.span
        if part == "package" then problem m.span "E_RESERVED" "package is reserved as a path prefix"
      if !m.path.isEmpty && (moduleAt p ⟨pkg.id, m.path.dropLast⟩).isNone then
        problem m.span "E_NAME" "module has no declared parent"
      let declarations := p.byScope[scope]?.getD []
      let names := declarations.map (·.owner.name) ++ m.imports.map (·.alias) ++ pkg.dependencies.map (·.alias)
      if !Finite.distinct names then throw (collision p pkg m)
      for decl in declarations do
        if let .error diagnostic := declarationName decl.kind decl.owner.name m.span then
          throw { diagnostic with span := (declarationPlace p decl.owner).getD m.span }
      for entry in m.imports do
        -- An indexed spelling is the name of a `use` without `as` only: the
        -- alias is the last segment of the path. A `use … as` alias keeps the
        -- ordinary check, so a request cannot bind `origin` to another
        -- declaration (#759). Keep the legacy diagnostic order unless such
        -- a spelling can be resolved in this declaration-aware namespace. The
        -- target is still checked below, so a function or a module cannot
        -- acquire a reserved alias.
        let implicit := entry.path.getLast? == some entry.alias
        if !(implicit && indexedSpelling entry.alias &&
            p.declarations.any (·.kind == .indexedDeclaration)) then
          sourceName entry.alias entry.span
        if entry.alias == "package" then problem entry.span "E_RESERVED" "package is reserved as a path prefix"
        let (target, next) ← importWorkStep p scope entry work
        work := next
        declarationName (if implicit && target.kind == .indexedDeclaration then target.kind else .function)
          entry.alias entry.span
  return work

def validate (p : Indexed) : Result Unit := (validateWithWork p).map fun _ => ()

end VastitasKernel.Namespace
