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
  p.packages.find? (·.id.source == source)

def moduleAt (p : Indexed) (scope : Scope) : Option Module := do
  let pkg ← packageAt p scope.package.source
  if pkg.id != scope.package then none else pkg.modules.find? (·.path == scope.path)

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

def charge (span : Span) : ResolutionM Unit
  | 0 => problem span "E_LIMIT" s!"namespace resolution exceeds the {Limits.namespaceResolution}-unit budget"
  | remaining + 1 => .ok ((), remaining)

-- Import resolution uses the original requesting scope for each traversed
-- visibility edge. Resolving an alias checks its declaration's visibility first,
-- then its source path in the alias's own scope, preserving the original target.
mutual
  def memberAt : Nat → Indexed → Scope → Scope → String → List (Scope × String) → Span → ResolutionM Target
    | 0, _, _, _, _, _, span => problem span "E_LIMIT" s!"namespace resolution exceeds the {Limits.namespaceResolution}-unit budget"
    | fuel + 1, p, requester, scope, name, active, span => do
      charge span
      if let some target := p.byOwner[Owner.mk scope name]? then
        if !visible requester target then
          problem span "E_VISIBILITY" s!"'{name}' is private in its declaring module"
        return target
      let some m := moduleAt p scope | problem span "E_NAME" "unknown module"
      let some entry := m.imports.find? (·.alias == name)
        | problem span "E_NAME" s!"undefined name '{name}' in this module"
      let access : Target := ⟨⟨scope, name⟩, .module, entry.isPublic⟩
      if !visible requester access then problem span "E_VISIBILITY" s!"import '{name}' is private"
      if active.contains (scope, name) then problem entry.span "E_CYCLE" "cyclic import or re-export"
      let target ← resolveAt fuel p scope entry.path ((scope, name) :: active) entry.span
      if entry.isPublic && !target.isPublic then
        problem entry.span "E_VISIBILITY" "pub use requires a public declaration"
      return target
  def descend : Nat → Indexed → Scope → Target → List String → List (Scope × String) → Span → ResolutionM Target
    | 0, _, _, _, _, _, span => problem span "E_LIMIT" s!"namespace resolution exceeds the {Limits.namespaceResolution}-unit budget"
    | fuel + 1, p, requester, target, path, active, span => do
      match path with
      | [] => return target
      | name :: rest =>
        if target.kind != .module then problem span "E_NAME" "a function cannot contain path components"
        let next ← memberAt fuel p requester (targetScope target) name active span
        descend fuel p requester next rest active span
  def resolveAt : Nat → Indexed → Scope → List String → List (Scope × String) → Span → ResolutionM Target
    | 0, _, _, _, _, span => problem span "E_LIMIT" s!"namespace resolution exceeds the {Limits.namespaceResolution}-unit budget"
    | fuel + 1, p, scope, path, active, span => do
      let some pkg := packageAt p scope.package.source | problem span "E_NAME" "unknown package"
      match path with
      | [] => problem span "E_NAME" "empty reference path"
      | "package" :: name :: rest => descend fuel p scope (dependencyRoot pkg) (name :: rest) active span
      | "self" :: rest => descend fuel p scope (← moduleTarget p scope span) rest active span
      | "super" :: rest =>
        let (parent, remaining) ← ancestors scope ("super" :: rest) span
        descend fuel p scope (← moduleTarget p parent span) remaining active span
      | name :: rest =>
        if let some dep := pkg.dependencies.find? (·.alias == name) then
          let some target := packageAt p dep.target | problem span "E_NAME" "unknown dependency target"
          descend fuel p scope (dependencyRoot target) rest active span
        else
          let target ← memberAt fuel p scope scope name active span
          descend fuel p scope target rest active span
end

def resolve (p : Indexed) (scope : Scope) (path : List String) (span : Span) : Result Target :=
  ((resolveAt Limits.namespaceResolution p scope path [] span).run Limits.namespaceResolution).map (·.1)

def symbol (p : Program) (target : Target) : String :=
  if target.owner.scope.package.source == p.root && target.owner.scope.path.isEmpty &&
      target.owner.name == "main" then "main" else target.owner.symbol

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

def validate (p : Indexed) : Result Unit := do
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
  if !UniqueOwners p then problem (duplicateSpan (ownerLocations p)) "E_DUPLICATE" "duplicate declaration owner"
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
        let (target, _) ← (memberAt Limits.namespaceResolution p scope scope entry.alias [] entry.span).run Limits.namespaceResolution
        declarationName (if target.kind == .indexedDeclaration then target.kind else .function)
          entry.alias entry.span

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

def lookup (p : Indexed) (scope : Scope) (name : String) (span : Span) (method := false) (membership := false) : M Target := do
  let path := (name.splitOn "::")
  let target ← resolve p scope path span
  if method && (target.kind != .generic || target.owner.scope != scope) then
    problem span "E_OWNER" "only the exact module defining a generic may add methods"
  if membership && (target.kind != .abstractType || target.owner.scope != scope) then
    problem span "E_OWNER" "only the exact module defining an abstract type may add scalar memberships"
  modify (⟨scope, path, span, target, method, membership⟩ :: ·)
  return target

def binder (p : Indexed) (scope : Scope) (name : String) (span : Span) : Result String := do
  sourceName name span
  let some m := moduleAt p scope | problem span "E_NAME" "unknown module"
  let some pkg := packageAt p scope.package.source | problem span "E_NAME" "unknown package"
  if p.byOwner.contains ⟨scope, name⟩ || m.imports.any (·.alias == name) ||
      pkg.dependencies.any (·.alias == name) then
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
      let mut output := []
      for statement in statements do
        match statement with
        | .letE name annotation value s =>
          let renamed ← binder p scope name s
          let value ← expression fuel p scope bound value
          output := output ++ [.letE renamed (annotation.map type) value s]
          bound := name :: bound
        | .unpack value scheme point s =>
          let value ← expression fuel p scope bound value
          let scheme' ← binder p scope scheme s
          let point' ← binder p scope point s
          output := output ++ [.unpack value scheme' point' s]
          bound := point :: scheme :: bound
      return .mk output (← expression fuel p scope bound result) span
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
    let mut functions := []
    let mut generics := []
    let mut methods := []
    let mut abstractTypes := []
    let mut subtypes := []
    let mut abstractMethods := []
    for pkg in p.packages do
      for m in pkg.modules do
        let scope : Scope := ⟨pkg.id, m.path⟩
        for declaration in m.abstractTypes do
          let target : Target := ⟨⟨scope, declaration.name⟩, .abstractType, declaration.isPublic⟩
          abstractTypes := abstractTypes ++ [{ declaration.toRawAbstractType with
            name := symbol p.toProgram target
            parents := ← declaration.parents.mapM (abstractPath p scope) }]
        for membership in m.subtypes do
          subtypes := subtypes ++ [{ membership with target := ← abstractPath p scope membership.target true }]
        for f in m.functions do
          functions := functions ++ [← function p scope f.toFunction ⟨⟨scope, f.name⟩, .function, f.isPublic⟩]
        for g in m.generics do
          let params ← g.params.mapM fun param => do
            return { param with name := ← binder p scope param.name param.span }
          generics := generics ++ [{ g.toRawGeneric with
            name := symbol p.toProgram ⟨⟨scope, g.name⟩, .generic, g.isPublic⟩, params }]
        for contract in m.abstractMethods do
          let target ← lookup p scope contract.name contract.span true
          let params ← contract.params.mapM fun param => do
            let ty ← selectorType p scope (.data param.ty) param.span
            return { param with name := ← binder p scope param.name param.span, ty := ty.core }
          let domain ← contract.domain.mapM fun clause => clause.mapM (abstractPath p scope)
          abstractMethods := abstractMethods ++ [{ contract with
            name := symbol p.toProgram target, params, domain }]
        for method in m.methods do
          let target ← lookup p scope method.name method.span true
          let params ← method.params.mapM fun param => do
            return { param with ty := ← selectorType p scope param.ty param.span }
          let f ← function p scope { method.toFunction with params } target
          methods := methods ++ [{ f with requirements := method.requirements }]
    return { version := if p.extended then 4 else 2, file := p.file, functions, generics, methods, abstractTypes, subtypes, abstractMethods }
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
