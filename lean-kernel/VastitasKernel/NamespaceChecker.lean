import VastitasKernel.Namespace
import VastitasKernel.FunctionChecker
import VastitasKernel.Distinct

namespace VastitasKernel.Namespace
open Surface

abbrev Result := Except Diagnostic

def problem (span : Span) (code message : String) : Result α :=
  .error { code, message, span }

def sourceName (name : String) (span : Span) : Result Unit := do
  let _ ← (DispatchChecker.checkSourceName name span).run {}
  if ["mod", "use", "pub", "self", "super"].contains name then
    problem span "E_RESERVED" s!"'{name}' is reserved for modules"

/-- Contextual module spelling only; functions, generics and bindings retain
the ordinary reserved-name checks. This grants no additional edit authority. -/
def moduleName (name : String) (span : Span) : Result Unit :=
  if name == "generic" then pure () else sourceName name span

/-- Compatibility spellings may name actual indexed declarations. They do not
select a declaration kind, representation, or operation. Scalar/Fn/Pair and
language keywords remain reserved. Public protocols 2–6 cannot create this kind. -/
def indexedSpelling (name : String) : Bool :=
  ["Scheme", "CInfScheme", "Point", "Morphism", "Pointed", "QQ", "CInfReal",
    "Affine", "Base", "origin", "id", "compose", "apply", "dimension"].contains name

def declarationName (kind : Kind) (name : String) (span : Span) : Result Unit :=
  if kind == .module then moduleName name span
  else if kind == .indexedDeclaration && indexedSpelling name then pure ()
  else sourceName name span

def packageAt (p : Indexed) (source : String) : Option Package :=
  p.byPackage[source]?.map (·.source)

def moduleLookupAt (p : Indexed) (scope : Scope) : Option ModuleLookup := do
  let pkg ← p.byPackage[scope.package.source]?
  if pkg.source.id != scope.package then none else pkg.modules[scope.path]?

def moduleAt (p : Indexed) (scope : Scope) : Option Module :=
  (moduleLookupAt p scope).map (·.source)

def dependencyRoot (pkg : Package) : Target :=
  ⟨⟨⟨pkg.id, []⟩, ""⟩, .module, true⟩

def moduleTarget (p : Indexed) (scope : Scope) (span : Span) : Result Target := do
  let some m := moduleAt p scope | problem span "E_NAME" "unknown module"
  if scope.path.isEmpty then return ⟨⟨scope, ""⟩, .module, true⟩
  return ⟨⟨⟨scope.package, scope.path.dropLast⟩, scope.path.getLast!⟩, .module, m.isPublic⟩

def targetScope (t : Target) : Scope :=
  if t.owner.name.isEmpty then t.owner.scope else t.moduleScope

def ancestors (scope : Scope) (path : List String) (span : Span) : Result (Scope × List String) := do
  match path with
  | "super" :: rest =>
    if scope.path.isEmpty then problem span "E_NAME" "super has no parent at the package root"
    ancestors { scope with path := scope.path.dropLast } rest span
  | rest => return (scope, rest)

abbrev ResolutionM := StateT Nat Result

/-- A lossless ordered key for persistent active-import paths. Balanced trees
share unchanged branches when nested path resolution retains a parent set. -/
abbrev ImportKey := String × String × String × List String × String

attribute [local instance] lexOrd

def importKey (entry : Scope × String) : ImportKey :=
  (entry.1.package.source, entry.1.package.name, entry.1.package.version, entry.1.path, entry.2)

def charge (span : Span) : ResolutionM Unit
  | 0 => problem span "E_LIMIT" s!"namespace resolution exceeds the {Limits.namespaceResolution}-unit budget"
  | remaining + 1 => .ok ((), remaining)

-- Import resolution uses the original requesting scope for each traversed
-- visibility edge. Resolving an alias checks its declaration's visibility first,
-- then its source path in the alias's own scope, preserving the original target.
mutual
  def memberAt : Nat → Indexed → Scope → Scope → String → Std.TreeSet ImportKey → Span → ResolutionM Target
    | 0, _, _, _, _, _, span => problem span "E_LIMIT" s!"namespace resolution exceeds the {Limits.namespaceResolution}-unit budget"
    | fuel + 1, p, requester, scope, name, active, span => do
      charge span
      if let some target := p.byOwner[Owner.mk scope name]? then
        if !visible requester target then
          problem span "E_VISIBILITY" s!"'{name}' is private in its declaring module"
        return target
      let some m := moduleLookupAt p scope | problem span "E_NAME" "unknown module"
      let some entry := m.imports[name]?
        | problem span "E_NAME" s!"undefined name '{name}' in this module"
      let access : Target := ⟨⟨scope, name⟩, .module, entry.isPublic⟩
      if !visible requester access then problem span "E_VISIBILITY" s!"import '{name}' is private"
      if active.contains (importKey (scope, name)) then problem entry.span "E_CYCLE" "cyclic import or re-export"
      let target ← resolveAt fuel p scope entry.path (active.insert (importKey (scope, name))) entry.span
      if entry.isPublic && !target.isPublic then
        problem entry.span "E_VISIBILITY" "pub use requires a public declaration"
      return target
  def descend : Nat → Indexed → Scope → Target → List String → Std.TreeSet ImportKey → Span → ResolutionM Target
    | 0, _, _, _, _, _, span => problem span "E_LIMIT" s!"namespace resolution exceeds the {Limits.namespaceResolution}-unit budget"
    | fuel + 1, p, requester, target, path, active, span => do
      match path with
      | [] => return target
      | name :: rest =>
        if target.kind != .module then problem span "E_NAME" "a function cannot contain path components"
        let next ← memberAt fuel p requester (targetScope target) name active span
        descend fuel p requester next rest active span
  def resolveAt : Nat → Indexed → Scope → List String → Std.TreeSet ImportKey → Span → ResolutionM Target
    | 0, _, _, _, _, span => problem span "E_LIMIT" s!"namespace resolution exceeds the {Limits.namespaceResolution}-unit budget"
    | fuel + 1, p, scope, path, active, span => do
      let some pkg := p.byPackage[scope.package.source]? | problem span "E_NAME" "unknown package"
      match path with
      | [] => problem span "E_NAME" "empty reference path"
      | "package" :: name :: rest => descend fuel p scope (dependencyRoot pkg.source) (name :: rest) active span
      | "self" :: rest => descend fuel p scope (← moduleTarget p scope span) rest active span
      | "super" :: rest =>
        let (parent, remaining) ← ancestors scope ("super" :: rest) span
        descend fuel p scope (← moduleTarget p parent span) remaining active span
      | name :: rest =>
        if let some dep := pkg.dependencies[name]? then
          let some target := packageAt p dep.target | problem span "E_NAME" "unknown dependency target"
          descend fuel p scope (dependencyRoot target) rest active span
        else
          let target ← memberAt fuel p scope scope name active span
          descend fuel p scope target rest active span
end

def resolve (p : Indexed) (scope : Scope) (path : List String) (span : Span) : Result Target :=
  ((resolveAt Limits.namespaceResolution p scope path {} span).run Limits.namespaceResolution).map (·.1)

/-- Structured "not found" for a one-component reference in an existing module:
no dependency alias, declaration or import of this name exists. A present
entry that fails to resolve is never reinterpreted as absent. -/
def unboundName (p : Indexed) (scope : Scope) (name : String) : Bool :=
  match p.byPackage[scope.package.source]?, moduleLookupAt p scope with
  | some pkg, some m =>
    name != "self" && name != "super" && name != "package" &&
      !pkg.dependencies.contains name && !p.byOwner.contains ⟨scope, name⟩ && !m.imports.contains name
  | _, _ => false

/-- An unbound name never resolves, so treating it as absent cannot shadow a
declaration, import or dependency alias. -/
theorem resolve_unboundName (p : Indexed) (scope : Scope) (name : String) (span : Span)
    (unbound : unboundName p scope name = true) :
    ∃ diagnostic, resolve p scope [name] span = .error diagnostic ∧ diagnostic.code = "E_NAME" := by
  unfold unboundName at unbound
  split at unbound
  · rename_i pkg m hpkg hm
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at unbound
    obtain ⟨⟨⟨⟨⟨hself, hsuper⟩, hpackage⟩, hdep⟩, hown⟩, himp⟩ := unbound
    obtain ⟨fuel, limit⟩ : ∃ fuel, Limits.namespaceResolution = fuel + 2 :=
      ⟨Limits.namespaceResolution - 2, by decide⟩
    have hdep' : pkg.dependencies[name]? = none := Std.HashMap.getElem?_eq_none_of_contains_eq_false hdep
    have hown' : p.byOwner[(⟨scope, name⟩ : Owner)]? = none :=
      Std.HashMap.getElem?_eq_none_of_contains_eq_false hown
    have himp' : m.imports[name]? = none := Std.HashMap.getElem?_eq_none_of_contains_eq_false himp
    unfold resolve
    rw [limit]
    simp only [resolveAt, hpkg]
    simp only [hdep', memberAt, hown', hm, himp']
    exact ⟨_, rfl, rfl⟩
  · simp at unbound

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

/-- Presentation only: a declaration that repeats the owner of another, and its
place. Of the declarations of one owner it is the second in the text of the
module, and of the repeated owners of the first module that has one, the one
whose repetition comes first. -/
def repeatedOwner (entries : List (Owner × Span)) : Option (Owner × Span) := Id.run do
  let mut spans : Std.HashMap Owner (List Span) := {}
  for (owner, span) in entries do
    spans := spans.insert owner (span :: spans.getD owner [])
  let repeated (owner : Owner) : Option Span :=
    match (spans.getD owner []).mergeSort (fun left right => left.start ≤ right.start) with
    | _ :: second :: _ => some second
    | _ => none
  let some (first, _) := entries.find? fun (owner, _) => (repeated owner).isSome | return none
  let mut best : Option (Owner × Span) := none
  for (owner, _) in entries do
    if owner.scope == first.scope then
      if let some span := repeated owner then
        if best.all fun (_, other) => span.start < other.start then best := some (owner, span)
  return best

def duplicateSpan [BEq α] (entries : List (α × Span)) : Span := Id.run do
  let mut seen := []
  for (key, span) in entries do
    if seen.contains key then return span
    seen := key :: seen
  return {}

def ownerLocations (p : Indexed) : List (Owner × Span) :=
  p.locations ++ p.packages.flatMap fun pkg => pkg.modules.flatMap fun m =>
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
  if !UniqueOwners p then
    match repeatedOwner (ownerLocations p) with
    | some (owner, span) => problem span "E_DUPLICATE" s!"`{owner.name}` is declared more than once in this module"
    | none => problem {} "E_DUPLICATE" "duplicate declaration owner"
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
      if !Finite.distinct names then problem m.span "E_DUPLICATE" "declaration, import, or dependency alias collision"
      for decl in declarations do
        declarationName decl.kind decl.owner.name m.span
      for entry in m.imports do
        -- Keep the legacy diagnostic order unless an indexed spelling can be
        -- resolved in this declaration-aware namespace. The target is still
        -- checked below, so a function cannot acquire a reserved alias.
        if !(indexedSpelling entry.alias &&
            p.declarations.any (·.kind == .indexedDeclaration)) then
          sourceName entry.alias entry.span
        if entry.alias == "package" then problem entry.span "E_RESERVED" "package is reserved as a path prefix"
        let (target, next) ← importWorkStep p scope entry work
        work := next
        declarationName (if target.kind == .indexedDeclaration then target.kind else .function)
          entry.alias entry.span
  return work

def validate (p : Indexed) : Result Unit := (validateWithWork p).map fun _ => ()

structure Reference where
  scope : Scope
  path : List String
  span : Span
  target : Target
  method : Bool := false
  membership : Bool := false
  deriving Repr, Inhabited, DecidableEq

structure Lowered where
  surface : Surface.Program
  references : List Reference
  deriving Repr, Inhabited

def Authorized (reference : Reference) : Prop :=
  (reference.method = true → reference.target.kind = .generic ∧ reference.target.owner.scope = reference.scope) ∧
  (reference.membership = true → reference.target.kind = .abstractType ∧ reference.target.owner.scope = reference.scope)

def ReferencesValid (p : Indexed) (lowered : Lowered) : Prop :=
  ∀ reference ∈ lowered.references,
    (resolve p reference.scope reference.path reference.span).toOption = some reference.target ∧ Authorized reference

instance (p : Indexed) (lowered : Lowered) : Decidable (ReferencesValid p lowered) := by
  unfold ReferencesValid Authorized
  infer_instance

abbrev M := StateT (List Reference) Result

/-- Resolve a structured path component-wise; wire path lists are never
rejoined into a string and split again. -/
def lookupPath (p : Indexed) (scope : Scope) (path : List String) (span : Span) (method := false)
    (membership := false) : M Target := do
  let target ← resolve p scope path span
  if method && (target.kind != .generic || target.owner.scope != scope) then
    problem span "E_OWNER" "only the exact module defining a generic may add methods"
  if membership && (target.kind != .abstractType || target.owner.scope != scope) then
    problem span "E_OWNER" "only the exact module defining an abstract type may add scalar memberships"
  modify (⟨scope, path, span, target, method, membership⟩ :: ·)
  return target

def lookup (p : Indexed) (scope : Scope) (name : String) (span : Span) (method := false) (membership := false) : M Target :=
  lookupPath p scope (name.splitOn "::") span method membership

def binder (p : Indexed) (scope : Scope) (name : String) (span : Span) : Result String := do
  sourceName name span
  let some m := moduleLookupAt p scope | problem span "E_NAME" "unknown module"
  let some pkg := p.byPackage[scope.package.source]? | problem span "E_NAME" "unknown package"
  if p.byOwner.contains ⟨scope, name⟩ || m.imports.contains name ||
      pkg.dependencies.contains name then
    problem span "E_SHADOW" s!"binding '{name}' conflicts with a module declaration, import or dependency alias"
  return localName name

def index : RawIndex → RawIndex
  | .name name => .name (localName name)
  | .base name => .base name

def dataType : RawType → RawType
  | .point target source => .point (index target) (index source)
  | .morphism source target => .morphism (index source) (index target)
  | ty => ty

mutual
  def type : TypeExpr → TypeExpr
    | .data ty => .data (dataType ty)
    | .function params result => .function (types params) (type result)
  def types : TypeList → TypeList
    | .nil => .nil
    | .cons head tail => .cons (type head) (types tail)
end

def parameters (p : Indexed) (scope : Scope) (params : List Param) : Result (List Param) :=
  params.mapM fun param => do
    return { param with name := ← binder p scope param.name param.span, ty := type param.ty }

def referenceName (p : Indexed) (scope : Scope) (bound : List String) (name : String) (span : Span) : M String := do
  if !name.contains ':' && (bound.contains name || builtinNames.contains name) then
    return if builtinNames.contains name then name else localName name
  let target ← lookup p scope name span
  if target.kind != .function && target.kind != .generic then
    problem span "E_NAME" "this declaration is not a function or generic value"
  return symbol p.toProgram target

mutual
  def expression : Nat → Indexed → Scope → List String → Expr → M Expr
    | 0, _, _, _, expr => problem expr.span "E_LIMIT" "namespace expression nesting limit exceeded"
    | fuel + 1, p, scope, bound, expr => do
      match expr with
      | .integer .. | .boolean .. | .unit .. =>
        return expr
      | .reference _ span => problem span "E_PROTOCOL" "internal function reference in namespace input"
      | .variable name span =>
        return .variable (← referenceName p scope bound name span) span
      | .call name args span =>
        return .call (← referenceName p scope bound name span)
          (← args.mapM (expression fuel p scope bound)) span
      | .invoke callee args span =>
        return .invoke (← expression fuel p scope bound callee)
          (← args.mapM (expression fuel p scope bound)) span
      | .lambda params result body span =>
        -- Outer local references retain their local spelling; the independent
        -- Surface capture audit rejects them, including dependent type indices.
        return .lambda (← parameters p scope params) (type result)
          (← block fuel p scope (params.map (·.name) ++ bound) body) span
      | .unary op value span =>
        return .unary op (← expression fuel p scope bound value) span
      | .binary op left right span =>
        return .binary op (← expression fuel p scope bound left)
          (← expression fuel p scope bound right) span
      | .ite cond yes no span =>
        return .ite (← expression fuel p scope bound cond)
          (← block fuel p scope bound yes) (← block fuel p scope bound no) span
      | .block body span =>
        return .block (← block fuel p scope bound body) span
      | .pack scheme point span =>
        return .pack (← expression fuel p scope bound scheme)
          (← expression fuel p scope bound point) span
  def block : Nat → Indexed → Scope → List String → Block → M Block
    | 0, _, _, _, .mk _ _ span => problem span "E_LIMIT" "namespace block nesting limit exceeded"
    | fuel + 1, p, scope, bound, .mk statements result span => do
      let mut bound := bound
      -- An array keeps rewriting linear in the number of statements.
      let mut output : Array Stmt := #[]
      for statement in statements do
        match statement with
        | .letE name annotation value s =>
          let renamed ← binder p scope name s
          let value ← expression fuel p scope bound value
          output := output.push (.letE renamed (annotation.map type) value s)
          bound := name :: bound
        | .unpack value scheme point s =>
          let value ← expression fuel p scope bound value
          let scheme' ← binder p scope scheme s
          let point' ← binder p scope point s
          output := output.push (.unpack value scheme' point' s)
          bound := point :: scheme :: bound
      return .mk output.toList (← expression fuel p scope bound result) span
end

def function (p : Indexed) (scope : Scope) (f : Surface.Function) (target : Target) : M Surface.Function := do
  return { f with
    name := symbol p.toProgram target
    params := ← parameters p scope f.params
    result := type f.result
    body := ← block Limits.namespaceNesting p scope (f.params.map (·.name)) f.body }

def abstractPath (p : Indexed) (scope : Scope) (path : TypePath) (membership := false) : M TypePath := do
  if path.path.length == 1 && Abstract.builtins.contains path.name then
    if membership then problem path.span "E_OWNER" "builtin subtype relations cannot be edited"
    return path
  let target ← lookup p scope path.name path.span false membership
  if target.kind != .abstractType then problem path.span "E_TYPE" "expected an abstract type declaration"
  return { path with path := [symbol p.toProgram target] }

def selectorType (p : Indexed) (scope : Scope) (ty : TypeExpr) (span : Span) : M TypeExpr := do
  match ty with
  | .data (.named name) =>
    let path ← abstractPath p scope ⟨name.splitOn "::", span⟩
    return .data (.named path.name)
  | _ => return ty

/-- Origins are reconstructed from enclosing decoded package/module declarations,
never from caller-supplied owner fields. -/
structure AbstractOrigin where
  scope : Scope
  declaration : RawAbstractType
  deriving Repr, Inhabited

structure MembershipOrigin where
  scope : Scope
  membership : RawSubtype
  deriving Repr, Inhabited

structure MembershipGraph where
  declarations : List AbstractOrigin
  memberships : List MembershipOrigin
  deriving Repr, Inhabited

def membershipGraph (p : Indexed) : Result MembershipGraph := do
  let mut declarations := []
  let mut memberships := []
  for pkg in p.packages do
    for m in pkg.modules do
      let scope : Scope := ⟨pkg.id, m.path⟩
      for declaration in m.abstractTypes do
        let parents ← declaration.parents.mapM fun path => do
          if path.path.length == 1 && Abstract.builtins.contains path.name then return path
          let target ← resolve p scope path.path path.span
          if target.kind != .abstractType then problem path.span "E_TYPE" "expected an abstract type declaration"
          return { path with path := [symbol p.toProgram target] }
        let target : Target := ⟨⟨scope, declaration.name⟩, .abstractType, declaration.isPublic⟩
        declarations := { scope, declaration := { declaration.toRawAbstractType with
          name := symbol p.toProgram target, parents } } :: declarations
      for membership in m.subtypes do
        if (Dispatch.parseScalar membership.scalar).isNone then
          problem membership.span "E_TYPE" "subtype membership requires Nat, Int, Bool, or Unit"
        let target ← resolve p scope membership.target.path membership.target.span
        if target.kind != .abstractType || target.owner.scope != scope then
          problem membership.span "E_OWNER" "only the exact module defining an abstract type may add scalar memberships"
        memberships := { scope, membership := { membership with target :=
          { membership.target with path := [symbol p.toProgram target] } } } :: memberships
  if declarations.length + Abstract.builtins.length > Limits.nominalTypes then
    problem ((declarations.head?).map (·.declaration.span) |>.getD {}) "E_LIMIT"
      s!"nominal hierarchy exceeds {Limits.nominalTypes} types including the six builtins"
  return { declarations := declarations.reverse, memberships := memberships.reverse }

def MembershipGraph.rawDeclarations (graph : MembershipGraph) : List RawAbstractType :=
  graph.declarations.map (·.declaration)

def MembershipGraph.names (graph : MembershipGraph) : List String :=
  Abstract.canonicalNames graph.rawDeclarations

def MembershipGraph.hierarchy (graph : MembershipGraph) : Dispatch.Hierarchy :=
  Abstract.build graph.rawDeclarations (graph.memberships.map (·.membership))

/-- Only abstract inheritance is used for a support path. Scalar edges cannot
circularly justify their own authority. -/
def MembershipGraph.inheritance (graph : MembershipGraph) : Dispatch.Hierarchy :=
  Abstract.build graph.rawDeclarations []

def MembershipSupported (graph : MembershipGraph) (inheritance : Dispatch.Hierarchy)
    (ancestor : AbstractOrigin) (scalar : Nat) : Prop :=
  ∃ support ∈ graph.memberships,
    support.scope = ancestor.scope ∧
    Dispatch.parseScalar support.membership.scalar = some scalar ∧
    inheritance.subtype (graph.names.idxOf support.membership.target.name)
      (graph.names.idxOf ancestor.declaration.name) = true

instance : Decidable (MembershipSupported graph inheritance ancestor scalar) := by
  unfold MembershipSupported
  infer_instance

def MembershipsAuthorized (graph : MembershipGraph) : Prop :=
  let hierarchy := graph.hierarchy
  let inheritance := graph.inheritance
  ∀ ancestor ∈ graph.declarations, ∀ scalar ∈ [0, 1, 2, 3],
    hierarchy.subtype scalar (graph.names.idxOf ancestor.declaration.name) = true →
      MembershipSupported graph inheritance ancestor scalar

instance : Decidable (MembershipsAuthorized graph) := by
  unfold MembershipsAuthorized
  infer_instance

def membershipAuthorityDiagnostic (graph : MembershipGraph) : Diagnostic := Id.run do
  let hierarchy := graph.hierarchy
  let inheritance := graph.inheritance
  for ancestor in graph.declarations do
    for scalar in [0, 1, 2, 3] do
      if hierarchy.subtype scalar (graph.names.idxOf ancestor.declaration.name) &&
          !decide (MembershipSupported graph inheritance ancestor scalar) then
        let cause := graph.memberships.find? fun m =>
          Dispatch.parseScalar m.membership.scalar == some scalar &&
          inheritance.subtype (graph.names.idxOf m.membership.target.name)
            (graph.names.idxOf ancestor.declaration.name)
        return {
          code := "E_OWNER"
          message := s!"inherited {Dispatch.nominalName scalar} membership lacks authorization from the ancestor's exact defining module"
          span := cause.map (·.membership.span) |>.getD ancestor.declaration.span
          notes := [{ span := ancestor.declaration.span, message := "this abstract selector's owner must independently declare the scalar membership" }] }
  return { code := "E_OWNER", message := "inherited scalar membership lacks owner authorization" }


def lower (p : Indexed) : Result Lowered := do
  validate p
  let action : M Surface.Program := do
    -- Arrays keep lowering linear in the number of declarations.
    let mut functions : Array Surface.Function := #[]
    let mut generics : Array RawGeneric := #[]
    let mut methods : Array Surface.Method := #[]
    let mut abstractTypes : Array RawAbstractType := #[]
    let mut subtypes : Array RawSubtype := #[]
    let mut abstractMethods : Array RawAbstractMethod := #[]
    for pkg in p.packages do
      for m in pkg.modules do
        let scope : Scope := ⟨pkg.id, m.path⟩
        for declaration in m.abstractTypes do
          let target : Target := ⟨⟨scope, declaration.name⟩, .abstractType, declaration.isPublic⟩
          abstractTypes := abstractTypes.push { declaration.toRawAbstractType with
            name := symbol p.toProgram target
            parents := ← declaration.parents.mapM (abstractPath p scope) }
        for membership in m.subtypes do
          subtypes := subtypes.push { membership with target := ← abstractPath p scope membership.target true }
        for f in m.functions do
          functions := functions.push (← function p scope f.toFunction ⟨⟨scope, f.name⟩, .function, f.isPublic⟩)
        for g in m.generics do
          let params ← g.params.mapM fun param => do
            return { param with name := ← binder p scope param.name param.span }
          generics := generics.push { g.toRawGeneric with
            name := symbol p.toProgram ⟨⟨scope, g.name⟩, .generic, g.isPublic⟩, params }
        for contract in m.abstractMethods do
          let target ← lookup p scope contract.name contract.span true
          let params ← contract.params.mapM fun param => do
            let ty ← selectorType p scope (.data param.ty) param.span
            return { param with name := ← binder p scope param.name param.span, ty := ty.core }
          let domain ← contract.domain.mapM fun clause => clause.mapM (abstractPath p scope)
          abstractMethods := abstractMethods.push { contract with
            name := symbol p.toProgram target, params, domain }
        for method in m.methods do
          let target ← lookup p scope method.name method.span true
          let params ← method.params.mapM fun param => do
            return { param with ty := ← selectorType p scope param.ty param.span }
          let f ← function p scope { method.toFunction with params } target
          methods := methods.push { f with requirements := method.requirements }
    return {
      version := if p.extended then 4 else 2, file := p.file, functions := functions.toList
      generics := generics.toList, methods := methods.toList, abstractTypes := abstractTypes.toList
      subtypes := subtypes.toList, abstractMethods := abstractMethods.toList }
  let (surface, references) ← action.run []
  return { surface, references }

end VastitasKernel.Namespace

namespace VastitasKernel

def checkNamespaceProgram (p : Namespace.Program) (requireMain : Bool := false)
    (render : Namespace.Lowered → Diagnostic → Diagnostic := fun _ diagnostic => diagnostic) : Except Diagnostic CertifiedModule := do
  if p.editable then
    throw ({ code := "E_PROTOCOL", message := "protocol 5 requires the edit assembly checker" } : Diagnostic)
  let indexed := p.indexed
  let lowered ← Namespace.lower indexed
  (do
    let graph ← Namespace.membershipGraph indexed
    if !Namespace.MembershipsAuthorized graph then
      throw (Namespace.membershipAuthorityDiagnostic graph)
    if !Namespace.UniqueOwners indexed || !Namespace.ReferencesValid indexed lowered then
      throw ({ code := "E_INTERNAL_NAMESPACE", message := "namespace identity or reference audit failed" } : Diagnostic)
    checkSurfaceProgram lowered.surface requireMain).mapError (render lowered)

end VastitasKernel
