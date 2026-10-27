import VastitasKernel.Namespace
import VastitasKernel.FunctionChecker

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
  | 0 => problem span "E_LIMIT" "namespace resolution exceeds the 4096-unit budget"
  | remaining + 1 => .ok ((), remaining)

-- Import resolution uses the original requesting scope for each traversed
-- visibility edge. Resolving an alias checks its declaration's visibility first,
-- then its source path in the alias's own scope, preserving the original target.
mutual
  def memberAt : Nat → Indexed → Scope → Scope → String → List (Scope × String) → Span → ResolutionM Target
    | 0, _, _, _, _, _, span => problem span "E_LIMIT" "namespace resolution exceeds the 4096-unit budget"
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
    | 0, _, _, _, _, _, span => problem span "E_LIMIT" "namespace resolution exceeds the 4096-unit budget"
    | fuel + 1, p, requester, target, path, active, span => do
      match path with
      | [] => return target
      | name :: rest =>
        if target.kind != .module then problem span "E_NAME" "a function cannot contain path components"
        let next ← memberAt fuel p requester (targetScope target) name active span
        descend fuel p requester next rest active span
  def resolveAt : Nat → Indexed → Scope → List String → List (Scope × String) → Span → ResolutionM Target
    | 0, _, _, _, _, span => problem span "E_LIMIT" "namespace resolution exceeds the 4096-unit budget"
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
  ((resolveAt 4096 p scope path [] span).run 4096).map (·.1)

def symbol (p : Program) (target : Target) : String :=
  if target.owner.scope.package.source == p.root && target.owner.scope.path.isEmpty &&
      target.owner.name == "main" then "main" else target.owner.symbol

def UniqueOwners (p : Indexed) : Prop :=
  (p.declarations.map (·.owner)).Nodup

instance (p : Indexed) : Decidable (UniqueOwners p) := inferInstanceAs (Decidable (List.Nodup _))

def graphVisit : Nat → Indexed → String → List String → StateT (Std.HashSet String) Result Unit
  | 0, _, _, _ => problem {} "E_LIMIT" "dependency graph exceeds the 4096-unit budget"
  | fuel + 1, p, source, active => do
    if active.contains source then problem {} "E_CYCLE" "cyclic package dependency"
    if (← get).contains source then return
    let some pkg := packageAt p source | problem {} "E_NAME" "unknown package dependency"
    for dep in pkg.dependencies do graphVisit fuel p dep.target (source :: active)
    modify (·.insert source)

def validateGraph (p : Indexed) : Result Unit :=
  ((p.packages.forM fun pkg => graphVisit 4096 p pkg.id.source []).run {}).map (·.1)

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
    (m.generics.map fun g => (⟨scope, g.name⟩, g.span)) ++
    (if m.path.isEmpty then [] else
      [(⟨⟨pkg.id, m.path.dropLast⟩, m.path.getLast!⟩, m.span)])

def validate (p : Indexed) : Result Unit := do
  if p.packages.isEmpty || (packageAt p p.root).isNone then problem {} "E_PROTOCOL" "missing root package"
  if !(p.packages.map (·.id.source)).Nodup then problem {} "E_DUPLICATE" "duplicate package location"
  if !p.scopes.Nodup then
    problem (duplicateSpan (p.packages.flatMap fun pkg =>
      pkg.modules.map fun m => (Scope.mk pkg.id m.path, m.span))) "E_DUPLICATE" "duplicate logical module"
  if !UniqueOwners p then problem (duplicateSpan (ownerLocations p)) "E_DUPLICATE" "duplicate declaration owner"
  if !(p.declarations.map (symbol p.toProgram)).Nodup then problem {} "E_DUPLICATE" "conflicting generated declaration identities"
  validateGraph p
  for pkg in p.packages do
    if pkg.id.name.isEmpty || pkg.id.source.isEmpty || !validVersion pkg.id.version then
      problem {} "E_PROTOCOL" "invalid package name, location or SemVer version"
    if !(pkg.modules.any (·.path.isEmpty)) then problem {} "E_PROTOCOL" "package has no root module"
    if !(pkg.dependencies.map (·.alias)).Nodup then problem {} "E_DUPLICATE" "duplicate dependency alias"
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
      if !names.Nodup then problem m.span "E_DUPLICATE" "declaration, import, or dependency alias collision"
      for decl in declarations do
        if decl.kind == .module then moduleName decl.owner.name m.span
        else sourceName decl.owner.name m.span
      for entry in m.imports do
        sourceName entry.alias entry.span
        if entry.alias == "package" then problem entry.span "E_RESERVED" "package is reserved as a path prefix"
        let _ ← (memberAt 4096 p scope scope entry.alias [] entry.span).run 4096
        pure ()

structure Reference where
  scope : Scope
  path : List String
  span : Span
  target : Target
  method : Bool := false
  deriving Repr, Inhabited

structure Lowered where
  surface : Surface.Program
  references : List Reference
  deriving Repr, Inhabited

def Authorized (reference : Reference) : Prop :=
  reference.method = true → reference.target.kind = .generic ∧ reference.target.owner.scope = reference.scope

def ReferencesValid (p : Indexed) (lowered : Lowered) : Prop :=
  ∀ reference ∈ lowered.references,
    (resolve p reference.scope reference.path reference.span).toOption = some reference.target ∧ Authorized reference

instance (p : Indexed) (lowered : Lowered) : Decidable (ReferencesValid p lowered) := by
  unfold ReferencesValid Authorized
  infer_instance

abbrev M := StateT (List Reference) Result

def lookup (p : Indexed) (scope : Scope) (name : String) (span : Span) (method := false) : M Target := do
  let path := (name.splitOn "::")
  let target ← resolve p scope path span
  if method && (target.kind != .generic || target.owner.scope != scope) then
    problem span "E_OWNER" "only the exact module defining a generic may add methods"
  modify (⟨scope, path, span, target, method⟩ :: ·)
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
  if target.kind == .module then problem span "E_NAME" "a module is not a value"
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
    body := ← block 1024 p scope (f.params.map (·.name)) f.body }

def lower (p : Indexed) : Result Lowered := do
  validate p
  let action : M Surface.Program := do
    let mut functions := []
    let mut generics := []
    let mut methods := []
    for pkg in p.packages do
      for m in pkg.modules do
        let scope : Scope := ⟨pkg.id, m.path⟩
        for f in m.functions do
          functions := functions ++ [← function p scope f.toFunction ⟨⟨scope, f.name⟩, .function, f.isPublic⟩]
        for g in m.generics do
          let params ← g.params.mapM fun param => do
            return { param with name := ← binder p scope param.name param.span }
          generics := generics ++ [{ g.toRawGeneric with
            name := symbol p.toProgram ⟨⟨scope, g.name⟩, .generic, g.isPublic⟩, params }]
        for method in m.methods do
          let target ← lookup p scope method.name method.span true
          let f ← function p scope method.toFunction target
          methods := methods ++ [{ f with requirements := method.requirements }]
    return { version := 2, file := p.file, functions, generics, methods }
  let (surface, references) ← action.run []
  return { surface, references }

end VastitasKernel.Namespace

namespace VastitasKernel

def checkNamespaceProgram (p : Namespace.Program) (requireMain : Bool := false)
    (render : Namespace.Lowered → Diagnostic → Diagnostic := fun _ diagnostic => diagnostic) : Except Diagnostic CertifiedModule := do
  let indexed := p.indexed
  let lowered ← Namespace.lower indexed
  (do
    if !Namespace.UniqueOwners indexed || !Namespace.ReferencesValid indexed lowered then
      throw ({ code := "E_INTERNAL_NAMESPACE", message := "namespace identity or reference audit failed" } : Diagnostic)
    checkSurfaceProgram lowered.surface requireMain).mapError (render lowered)

end VastitasKernel
