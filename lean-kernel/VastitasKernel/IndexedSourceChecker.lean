import VastitasKernel.IndexedSource
import VastitasKernel.NamespaceChecker
import VastitasKernel.IndexedTypeAudit

namespace VastitasKernel.Indexed.Source

abbrev ResolveM := StateT (List Reference) Namespace.Result

def resolveId (p : Namespace.Indexed) (scope : Namespace.Scope) (path : Path) : ResolveM DeclId := do
  let target ← Namespace.resolve p scope path.path path.span
  if target.kind != .indexedDeclaration then
    Namespace.problem path.span "E_TYPE" "expected an indexed declaration"
  modify (⟨scope, path, target⟩ :: ·)
  return target.owner

def resolveParameter (p : Namespace.Indexed) (scope : Namespace.Scope) : Parameter → ResolveM Indexed.Parameter
  | .domain => pure .domain
  | .marker => pure .marker
  | .natural => pure .natural
  | .object domain => return .object (← resolveId p scope domain)

def resolveType (p : Namespace.Indexed) (scope : Namespace.Scope) (type : ObjectType) : ResolveM Indexed.ObjectType :=
  return ⟨← resolveId p scope type.domain, ← resolveId p scope type.marker⟩

def resolveIndex (p : Namespace.Indexed) (scope : Namespace.Scope) : BoundIndex → ResolveM Indexed.BoundIndex
  | .witness => pure .witness
  | .natural value => pure (.natural value)
  | .global path => return .global (← resolveId p scope path)
  | .domain path => return .domain (← resolveId p scope path)
  | .marker path => return .marker (← resolveId p scope path)

def resolveField (p : Namespace.Indexed) (scope : Namespace.Scope) (field : BoundApplication) :
    ResolveM Indexed.BoundApplication :=
  return ⟨← resolveId p scope field.family, ← field.indices.mapM (resolveIndex p scope)⟩

def resolveShape (p : Namespace.Indexed) (scope : Namespace.Scope) (shape : PackageShape) :
    ResolveM Indexed.PackageShape :=
  return ⟨← resolveType p scope shape.witnessType, ← shape.fields.mapM (resolveField p scope)⟩

def resolvePrimitive (p : Namespace.Indexed) (scope : Namespace.Scope) : Primitive → ResolveM PrimitiveBinding
  | .descriptor implementation => return .descriptor (← resolveId p scope implementation)
  | .global declaration => return .global (← resolveId p scope declaration)
  | .origin domain family base =>
      return .origin (← resolveType p scope domain) (← resolveId p scope family) (← resolveId p scope base)
  | .identity domain family => return .identity (← resolveType p scope domain) (← resolveId p scope family)
  | .dimension domain => return .dimension (← resolveType p scope domain)
  | .compose family => return .compose (← resolveId p scope family)
  | .apply maps points => return .apply (← resolveId p scope maps) (← resolveId p scope points)

def resolveBody (p : Namespace.Indexed) (owner : DeclId) (body : Body) (env : Core.Declarations) :
    ResolveM Core.Declarations := do
  let scope := owner.scope
  let add (declaration : Indexed.Declaration) := { env with indexed := env.indexed ++ [⟨owner, declaration⟩] }
  match body with
  | .marker => return add .marker
  | .implementation marker representation capabilities =>
      return add (.implementation (← resolveId p scope marker) representation capabilities)
  | .classification parents domain =>
      return add (.classification (← parents.mapM (resolveId p scope)) (← domain.mapM (resolveId p scope)))
  | .global implementation => return add (.global (← resolveId p scope implementation))
  | .family family => return add (.family
      ⟨← family.parameters.mapM (resolveParameter p scope), family.constraints, family.representation⟩)
  | .package cases =>
      return { env with packages := env.packages ++ [⟨owner, ← cases.mapM (resolveShape p scope)⟩] }
  | .primitive binding =>
      return { env with primitives := env.primitives ++ [⟨owner, ← resolvePrimitive p scope binding⟩] }

def resolveGeometrySetting (p : Namespace.Indexed) (scope : Namespace.Scope)
    (setting : GeometrySetting Path) : ResolveM (GeometrySetting DeclId) := do
  return ⟨← resolveId p scope setting.domain, ← resolveId p scope setting.marker,
    ← resolveId p scope setting.baseObject, ← resolveId p scope setting.affine,
    ← resolveId p scope setting.base, ← resolveId p scope setting.origin,
    ← resolveId p scope setting.identity, ← resolveId p scope setting.dimension⟩

def resolveGeometry (p : Program) (env : Core.Declarations) :
    ResolveM (Option (GeometryProfile DeclId)) := do
  let profiles := p.packages.filterMap fun pkg => pkg.geometryCompat.map (pkg.id, ·)
  let resolved ← profiles.mapM fun (owner, profile) => do
    let scope : Namespace.Scope := ⟨owner, []⟩
    let resolved : GeometryProfile DeclId :=
      ⟨← resolveGeometrySetting p.indexed scope profile.scheme,
       ← resolveGeometrySetting p.indexed scope profile.smooth,
       ← resolveId p.indexed scope profile.point, ← resolveId p.indexed scope profile.morphism,
       ← resolveId p.indexed scope profile.pointed, ← resolveId p.indexed scope profile.compose,
       ← resolveId p.indexed scope profile.apply⟩
    unless resolved.valid env do
      Namespace.problem {} "E_TYPE" "geometry compatibility export does not match its declared finite contracts"
    return resolved
  -- Several independently named libraries may coexist. Only the legacy
  -- unqualified dialect needs a unique interpretation; new syntax still works.
  return match resolved with | [profile] => some profile | _ => none

/-- Every declaration, including unused dependencies, is resolved before the
complete finite environment is validated. No observed-use domain inference. -/
def lower (p : Program) : Namespace.Result Resolved := do
  let index := p.indexed
  let action : ResolveM Core.Declarations := p.owned.foldlM (fun env entry =>
    resolveBody index entry.1 entry.2.body env) ⟨[], [], []⟩
  let (declarations, references) ← action.run []
  let (geometry, geometryReferences) ← (resolveGeometry p declarations).run []
  return ⟨declarations, references.reverse ++ geometryReferences.reverse, geometry⟩

def Reference.Valid (p : Namespace.Indexed) (reference : Reference) : Prop :=
  reference.scope ∈ p.scopes ∧ reference.target.kind = .indexedDeclaration ∧
    (Namespace.resolve p reference.scope reference.path.path reference.path.span).toOption =
      some reference.target

instance (p : Namespace.Indexed) (reference : Reference) : Decidable (reference.Valid p) := by
  unfold Reference.Valid
  infer_instance

def ReferencesValid (p : Namespace.Indexed) (resolved : Resolved) : Prop :=
  ∀ reference ∈ resolved.references, reference.Valid p

instance (p : Namespace.Indexed) (resolved : Resolved) : Decidable (ReferencesValid p resolved) := by
  unfold ReferencesValid
  infer_instance

/-- This certificate is only declaration acceptance. Function bodies, finite
dispatch, edit assemblies and source-to-Core term translation are not certified
here; they are composed by the public protocol-7 entry point. -/
structure CheckedDeclarations (p : Program) where
  resolved : Resolved
  namespaceAccepted : Namespace.validate p.indexed = .ok ()
  ownersUnique : Namespace.UniqueOwners p.indexed
  lowered : lower p = .ok resolved
  referencesValid : ReferencesValid p.indexed resolved
  idsPreserved : resolved.declarations.ids = p.declarationIds
  accepted : Core.validDeclarations resolved.declarations = true
  geometryAccepted : resolved.geometry.all (·.valid resolved.declarations) = true

def checkDeclarations (p : Program) : Except Diagnostic (CheckedDeclarations p) := do
  if p.owned.length > 4096 then Namespace.problem {} "E_LIMIT" "more than 4096 indexed declarations"
  match namespaceAccepted : Namespace.validate p.indexed with
  | .error error => .error error
  | .ok () =>
    if ownersUnique : Namespace.UniqueOwners p.indexed then
      match lowered : lower p with
      | .error error => .error error
      | .ok resolved =>
        if referencesValid : ReferencesValid p.indexed resolved then
          if idsPreserved : resolved.declarations.ids = p.declarationIds then
            if accepted : Core.validDeclarations resolved.declarations = true then
              if geometryAccepted : resolved.geometry.all (·.valid resolved.declarations) = true then
                return ⟨resolved, namespaceAccepted, ownersUnique, lowered,
                  referencesValid, idsPreserved, accepted, geometryAccepted⟩
              else Namespace.problem {} "E_TYPE" "geometry compatibility contract audit failed"
            else Namespace.problem {} "E_TYPE" "invalid indexed declaration, package, or primitive contract"
          else Namespace.problem {} "E_OWNER" "indexed declaration identity audit failed"
        else Namespace.problem {} "E_OWNER" "indexed declaration reference audit failed"
    else Namespace.problem {} "E_DUPLICATE" "duplicate declaration owner"

end VastitasKernel.Indexed.Source
