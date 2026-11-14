import VastitasKernel.Namespace
import VastitasKernel.FunctionScope
import VastitasKernel.Distinct

/-! Names, module lookup and import resolution of the namespace checker
(`NamespaceChecker.lean`). -/
namespace VastitasKernel.Namespace
open Surface

abbrev Result := Except Diagnostic

def problem (span : Span) (code message : String) : Result α :=
  .error { code, message, span }

def sourceName (name : String) (span : Span) : Result Unit := do
  let _ ← (DispatchChecker.checkSourceName name span).run {}
  if ["mod", "use", "pub", "self", "super"].contains name then
    problem span "E_RESERVED" s!"'{name}' is reserved for modules"

/-- The seven geometric operations. A module may take one of these names, as
in `mod dim;`; every other declaration and binding, including the name that a
`use` binds, keeps the ordinary reserved-name check. `dimension` is none of
them: it is an ordinary name, as in `nature::dimension` (#778). -/
def geometricOperation (name : String) : Bool :=
  ["Affine", "Base", "origin", "id", "compose", "apply", "dim"].contains name

/-- Contextual module spellings only: `generic` and the seven geometric
operations. Functions, generics, imports and bindings retain the ordinary
reserved-name checks. This grants no additional edit authority. -/
def moduleName (name : String) (span : Span) : Result Unit :=
  if name == "generic" || geometricOperation name then pure () else sourceName name span

/-- Compatibility spellings may name actual indexed declarations: the
declaration itself, and a `use` without `as` that imports one, whose alias is
the last segment of its path. They do not select a declaration kind,
representation, or operation. Scalar/Fn/Pair and language keywords remain
reserved. Public protocols 2–6 cannot create this kind. -/
def indexedSpelling (name : String) : Bool :=
  ["Scheme", "CInfScheme", "Point", "Morphism", "Pointed", "QQ", "CInfReal",
    "Affine", "Base", "origin", "id", "compose", "apply", "dim"].contains name

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

/-- Structured "names a module" for a one-component reference in an existing
package: the declaration of this name in the scope is a module, and no
dependency alias of this name exists. A module is neither a value nor a
function, so a module named after a geometric operation does not hide it. -/
def childModule (p : Indexed) (scope : Scope) (name : String) : Bool :=
  match p.byPackage[scope.package.source]? with
  | some pkg =>
    name != "self" && name != "super" && name != "package" &&
      !pkg.dependencies.contains name &&
      match p.byOwner[(⟨scope, name⟩ : Owner)]? with
      | some target => target.kind == .module
      | none => false
  | none => false

/-- A name of a child module resolves to that module or fails, so it never
reaches a function, a generic or an indexed declaration. -/
theorem resolve_childModule (p : Indexed) (scope : Scope) (name : String) (span : Span)
    (child : childModule p scope name = true) (target : Target)
    (resolved : resolve p scope [name] span = .ok target) : target.kind = .module := by
  unfold childModule at child
  split at child
  · rename_i pkg hpkg
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at child
    obtain ⟨⟨⟨⟨hself, hsuper⟩, hpackage⟩, hdep⟩, hmodule⟩ := child
    split at hmodule
    · rename_i found hown
      obtain ⟨fuel, limit⟩ : ∃ fuel, Limits.namespaceResolution = fuel + 2 :=
        ⟨Limits.namespaceResolution - 2, by decide⟩
      have hdep' : pkg.dependencies[name]? = none :=
        Std.HashMap.getElem?_eq_none_of_contains_eq_false hdep
      unfold resolve at resolved
      rw [limit] at resolved
      simp only [resolveAt, hpkg] at resolved
      simp only [hdep', memberAt, hown] at resolved
      have hkind : found.kind = .module := by
        revert hmodule; cases found.kind <;> decide
      have hcharge : StateT.run (charge span) (fuel + 2) = .ok ((), fuel + 1) := rfl
      cases hv : visible scope found
      · simp [hv, problem, hcharge] at resolved
        cases resolved
      · simp [hv, descend, hcharge] at resolved
        cases resolved
        exact hkind
    · simp at hmodule
  · simp at child

end VastitasKernel.Namespace
