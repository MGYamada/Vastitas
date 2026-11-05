import VastitasKernel.IndexedSource
import VastitasKernel.IndexedPrimitiveFamilies
import VastitasKernel.NamespaceChecker
import VastitasKernel.IndexedTypeAudit
import VastitasKernel.IndexedAlgebraSource
import VastitasKernel.IndexedSmoothSource
import VastitasKernel.IndexedMetricSource

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

def resolveArgument (p : Namespace.Indexed) (scope : Namespace.Scope) : WireArgument → ResolveM ResolvedArgument
  | .path path => return .declaration (← resolveId p scope path)
  | .objectType type => return .objectType (← resolveType p scope type)
  | .coordinate name => pure (.coordinate name)
  | .polynomial expression => pure (.polynomial expression)
  | .pullbackMode mode => pure (.pullbackMode mode)

/-- The binding of a primitive's wire form through its family: the arguments
are the family's fields in wire order, each is resolved in the family's
resolution order, and `build` embeds the placeholders that the stage passes
fill. A form the decoder cannot produce (an unknown op, other field names,
another order or other kinds) is `E_PROTOCOL` before any name is resolved, so
`build` always receives arguments of the family's kinds. -/
def resolvePrimitive (p : Namespace.Indexed) (scope : Namespace.Scope) (primitive : Primitive) :
    ResolveM PrimitiveBinding := do
  let some family := primitiveFamily? primitive.op
    | Namespace.problem {} "E_PROTOCOL" "unknown indexed primitive contract"
  unless primitive.arguments.map (fun (name, argument) => (name, argument.kind)) ==
      family.fields.map (fun field => (field.name, field.kind)) do
    Namespace.problem {} "E_PROTOCOL" s!"the arguments of `{family.op}` are not its wire fields"
  let mut resolved : List (String × ResolvedArgument) := []
  for name in family.resolutionOrder do
    if let some (_, argument) := primitive.arguments.find? (·.1 == name) then
      resolved := resolved ++ [(name, ← resolveArgument p scope argument)]
  let arguments := family.fieldNames.filterMap fun name => (resolved.find? (·.1 == name)).map (·.2)
  match family.build arguments with
  | .ok binding => pure binding
  | .error message => Namespace.problem {} "E_PROTOCOL" message

def resolveRepresentation (p : Namespace.Indexed) (scope : Namespace.Scope) :
    Source.Representation → ResolveM Indexed.Representation
  | .affineDescriptor => pure .affineDescriptor
  | .scalarBase setting coefficient => pure (.scalarBase setting coefficient)
  | .linearDescriptor base coefficient => return .linearDescriptor (← resolveId p scope base) coefficient
  | .presentedAffine field => pure (.presentedAffine field)
  | .smoothAffine => pure .smoothAffine

def resolveBody (p : Namespace.Indexed) (owner : DeclId) (span : Span) (body : Body)
    (env : Core.Declarations) : ResolveM Core.Declarations := do
  let scope := owner.scope
  let add (declaration : Indexed.Declaration) := { env with indexed := env.indexed ++ [⟨owner, declaration⟩] }
  match body with
  | .marker => return add .marker
  | .implementation marker representation capabilities =>
      return add (.implementation (← resolveId p scope marker)
        (← resolveRepresentation p scope representation) capabilities)
  | .classification parents domain =>
      return add (.classification (← parents.mapM (resolveId p scope)) (← domain.mapM (resolveId p scope)))
  | .global implementation => return add (.global (← resolveId p scope implementation))
  | .family family => return add (.family
      ⟨← family.parameters.mapM (resolveParameter p scope), family.constraints, family.representation⟩)
  | .package cases =>
      return { env with packages := env.packages ++ [⟨owner, ← cases.mapM (resolveShape p scope)⟩] }
  | .primitive binding =>
      return { env with primitives := env.primitives ++ [⟨owner, ← resolvePrimitive p scope binding⟩] }
  | .morphism family indices definition => do
      if let .restrict morphism := definition then
        let _ ← resolveId p scope morphism
      -- The exact map is elaborated once objects are known.
      let application : Application :=
        ⟨← resolveId p scope family, ← indices.mapM fun index => return .object (.global (← resolveId p scope index))⟩
      return { env with primitives := env.primitives ++ [⟨owner, .relativeConstant application ⟨0, [], []⟩⟩] }
  | .affineFiber implementation left right _ => do
      -- The presentation is derived once both factors are elaborated.
      let implementation ← resolveId p scope implementation
      let data : AlgebraDeclarations.AffineData := {
        generators := [], construction := .fiber (← resolveId p scope left) (← resolveId p scope right) none [],
        base := none, bindings := [], structureImages := [], basis := [], cofactors := [] }
      return add (.affine implementation data)
  | .affineLocalization implementation object _ inverse => do
      -- The element is expanded once the object is elaborated.
      let implementation ← resolveId p scope implementation
      let data : AlgebraDeclarations.AffineData := {
        generators := [], construction := .localization (← resolveId p scope object) [] inverse [],
        base := none, bindings := [], structureImages := [], basis := [], cofactors := [] }
      return add (.affine implementation data)
  | .iso forward backward => do
      -- Placeholders name the referenced morphisms; elaboration copies their checked maps.
      let reference (id : DeclId) : Application × AlgebraRuntime.Map := (⟨id, []⟩, ⟨0, [], []⟩)
      return { env with primitives := env.primitives ++ [⟨owner,
        .relativeIso (reference (← resolveId p scope forward)) (reference (← resolveId p scope backward))⟩] }
  | .cartesian first second fiber inverse => do
      let reference (id : DeclId) : Application × AlgebraRuntime.Map := (⟨id, []⟩, ⟨0, [], []⟩)
      let first ← resolveId p scope first
      let second ← resolveId p scope second
      let fiber ← resolveId p scope fiber
      let inverse ← resolveId p scope inverse
      return { env with primitives := env.primitives ++ [⟨owner,
        .relativeCartesian (reference first) (reference second) (reference inverse) fiber⟩] }
  | .affine implementation generators relations base bindings => do
      let implementation ← resolveId p scope implementation
      let base ← base.mapM (resolveId p scope)
      let data ← lowerAffineData span generators relations base bindings
      return add (.affine implementation data)
  | .smoothAffine implementation dimension coordinates => do
      let implementation ← resolveId p scope implementation
      match SmoothDeclarations.checkObject dimension coordinates with
      | .ok () => return add (.smoothAffine implementation coordinates)
      | .error error => smoothProblem span error
  | .metric family indices _ => do
      let family ← resolveId p scope family
      let indices ← indices.mapM (resolveId p scope)
      let [object] := indices
        | smoothProblem span (.metric <| s!"a metric names one object, as in `MetricForm<X>`, " ++
            s!"but {indices.length} are given")
      -- The Gram matrix is elaborated once the object is known.
      return add (.metric family object [])
  | .evidence metric kind => do
      let metric ← resolveId p scope metric
      -- The certificate is computed once the metric is elaborated.
      return add (.metricEvidence metric (match kind with
        | .nondegenerate => .nondegenerate []
        | .riemannian => .riemannian [] [] []))

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
    resolveBody index entry.1 entry.2.span entry.2.body env) ⟨[], [], []⟩
  let (declarations, references) ← action.run []
  let sources := p.owned.map fun (owner, d) => (owner, d.span, d.body)
  checkSmoothImplementations sources declarations
  let declarations ← elaborateAffine sources declarations
  let declarations ← elaborateSmooth sources declarations
  let declarations ← elaborateMetrics sources declarations
  let restrictTargets ← p.owned.filterMapM fun (owner, d) => match d.body with
    | .morphism _ _ (.restrict morphism) => do
      let target ← Namespace.resolve index owner.scope morphism.path morphism.span
      pure (some (owner, target.owner))
    | _ => pure none
  let declarations ← elaborateRelative sources declarations restrictTargets
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
