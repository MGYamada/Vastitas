import VastitasKernel.IndexedSource
import VastitasKernel.IndexedPrimitiveFamilies
import VastitasKernel.NamespaceChecker
import VastitasKernel.IndexedTypeAudit
import VastitasKernel.IndexedAlgebraSource
import VastitasKernel.IndexedSmoothSource
import VastitasKernel.IndexedMetricSource
import VastitasKernel.IndexedFrameSource
import VastitasKernel.IndexedNatureSource
import VastitasKernel.IndexedDeclarationRules

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
  | .frame family => return .frame (← resolveId p scope family)

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
  | .natural value => pure (.natural value)

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
  /- Frames and physical dimensions (Stage 4). Every path is resolved here;
  the matrices, the magnitudes, the coefficients and the coordinate order are
  elaborated once the objects are known (`elaborateFrames`,
  `elaborateNature`). -/
  | .frame family indices _ _ => do
      let family ← resolveId p scope family
      let indices ← indices.mapM (resolveId p scope)
      let [object] := indices
        | Namespace.problem span "E_FRAME" <| s!"a frame names one object, as in `Frame<X>`, " ++
            s!"but {indices.length} are given"
      -- The matrix and, for a constant frame, the inverse are elaborated once the object is known.
      return add (.frame family object [] [])
  | .baseDimension => return add .baseDimension
  | .quantity dimension => do
      let dimension ← dimension.mapM fun (base, exponent) => do pure (← resolveId p scope base, exponent)
      return add (.quantity dimension)
  | .reading family indices quantities => do
      let family ← resolveId p scope family
      let indices ← indices.mapM (resolveId p scope)
      let [object] := indices
        | Namespace.problem span "E_DIMENSION" <| s!"a reading names one object, as in `Reading<X>`, " ++
            s!"but {indices.length} are given"
      -- In source order; the coordinate order is elaborated once the object is known.
      let quantities ← quantities.mapM fun (_, quantity) => resolveId p scope quantity
      return add (.reading family object quantities)
  | .scale quantity _ => do
      -- The magnitude is elaborated with the other nature declarations.
      return add (.scale (← resolveId p scope quantity) 0)
  | .physicalMetric family indices metric reading value entries => do
      let family ← resolveId p scope family
      let indices ← indices.mapM (resolveId p scope)
      let [object] := indices
        | Namespace.problem span "E_DIMENSION" <| s!"a physical metric names one object, as in " ++
            s!"`PhysicalMetric<X>`, but {indices.length} are given"
      let metric ← resolveId p scope metric
      let reading ← resolveId p scope reading
      let value ← value.mapM fun factors =>
        factors.mapM fun (base, exponent) => do pure (← resolveId p scope base, exponent)
      -- The coefficients are elaborated, and normalized scales put in coordinate order, later.
      let factor (scale : Path) (exponent : Int) : ResolveM (DeclId × Int) := do
        pure (← resolveId p scope scale, exponent)
      let entries : Indexed.PhysicalGram ← match entries with
        | .euclidean => pure .euclidean
        | .gram rows => do
          let rows ← rows.mapM fun row => row.mapM fun monomial => do
            let factors ← monomial.factors.mapM fun (scale, exponent) => factor scale exponent
            pure ({ coefficient := 0, factors } : Indexed.ScaleMonomial)
          pure (.gram rows)
        | .normalized scales => do
          pure (.normalized (← scales.mapM fun (_, scale) => resolveId p scope scale))
      return add (.physicalMetric family object metric reading value entries)

/-- How a diagnostic names the export of a package. The request has no span
for a manifest, so the message names the package as its manifest does, and the
manifest itself. -/
def exportName (owner : Namespace.PackageId) : String :=
  s!"the geometry compatibility export of package `{owner.name}` ({owner.source})"

/-- A path of an export has no span. A diagnostic about one names the entry
of the table and the export in its message. -/
def atExportEntry {α : Type} (owner : Namespace.PackageId) (key : String) (action : ResolveM α) :
    ResolveM α := fun references =>
  match action references with
  | .ok result => .ok result
  | .error diagnostic => .error { diagnostic with
      message := s!"{exportName owner}, entry `{key}`: {diagnostic.message}" }

def resolveGeometrySetting (p : Namespace.Indexed) (scope : Namespace.Scope) (table : String)
    (setting : GeometrySetting Path) : ResolveM (GeometrySetting DeclId) := do
  let entry (key : String) (path : Path) :=
    atExportEntry scope.package s!"{table}.{key}" (resolveId p scope path)
  return ⟨← entry "domain" setting.domain, ← entry "marker" setting.marker,
    ← entry "base_object" setting.baseObject, ← entry "affine" setting.affine,
    ← entry "base" setting.base, ← entry "origin" setting.origin,
    ← entry "identity" setting.identity, ← entry "dimension" setting.dimension⟩

/-- Presentation only: the first entry of a setting that `GeometrySetting.valid`
rejects, as its key and the declaration that it names. The conjuncts are those
of `GeometrySetting.valid`, in its order. -/
def invalidSettingEntry (env : Core.Declarations) (profile : GeometryProfile DeclId)
    (table : String) (setting : GeometrySetting DeclId) : Option (String × DeclId) :=
  let type := setting.objectType
  let entry (key : String) (id : DeclId) : Option (String × DeclId) := some (s!"{table}.{key}", id)
  if !(match Indexed.lookup env.indexed setting.domain with | some (.classification ..) => true | _ => false) then
    entry "domain" setting.domain
  else if !decide (type.Valid env.indexed) then entry "marker" setting.marker
  else if !(ObjectRef.type? env.indexed (.global setting.baseObject)).any
      (fun base => decide (base.Refines env.indexed type)) then entry "base_object" setting.baseObject
  else if !(match env.primitive? setting.affine with
      | some (.descriptor implementation) => (implementationType env.indexed implementation).any
          (fun concrete => decide (concrete.Refines env.indexed type))
      | _ => false) then entry "affine" setting.affine
  else if env.primitive? setting.base != some (.global setting.baseObject) then entry "base" setting.base
  else if env.primitive? setting.origin != some (.origin type profile.point setting.baseObject) then
    entry "origin" setting.origin
  else if env.primitive? setting.identity != some (.identity type profile.morphism) then
    entry "identity" setting.identity
  else if env.primitive? setting.dimension != some (.dimension type) then entry "dimension" setting.dimension
  else if env.package? ⟨profile.pointed, [.domain setting.domain, .marker setting.marker]⟩ !=
      some ⟨type, [⟨profile.point, [.witness, .global setting.baseObject]⟩]⟩ then some ("pointed", profile.pointed)
  else none

/-- Presentation only: why `GeometryProfile.valid` rejects an export, by the
first entry of its table that does not fit. The conjuncts are those of
`GeometryProfile.valid`, in its order. Acceptance is `GeometryProfile.valid`
alone; an export that it rejects for a reason that this function does not
find is reported without the entry. -/
def invalidExportEntry (env : Core.Declarations) (profile : GeometryProfile DeclId) : Option String :=
  let names (entry : String × DeclId) : Option String :=
    some s!"`{entry.1}` names `{qualified entry.2}`, which does not fit that entry"
  if profile.scheme.marker == profile.smooth.marker then
    some s!"`scheme.marker` and `smooth.marker` name one marker, `{qualified profile.scheme.marker}`"
  else if !profile.familyValid env profile.point .point then names ("point", profile.point)
  else if !profile.familyValid env profile.morphism .morphism then names ("morphism", profile.morphism)
  else if let some entry := invalidSettingEntry env profile "scheme" profile.scheme then names entry
  else if let some entry := invalidSettingEntry env profile "smooth" profile.smooth then names entry
  else if env.primitive? profile.compose != some (.compose profile.morphism) then names ("compose", profile.compose)
  else if env.primitive? profile.apply != some (.apply profile.morphism profile.point) then
    names ("apply", profile.apply)
  else none

def resolveGeometry (p : Program) (env : Core.Declarations) :
    ResolveM (Option (GeometryProfile DeclId)) := do
  let profiles := p.packages.filterMap fun pkg => pkg.geometryCompat.map (pkg.id, ·)
  let resolved ← profiles.mapM fun (owner, profile) => do
    let scope : Namespace.Scope := ⟨owner, []⟩
    let entry (key : String) (path : Path) := atExportEntry owner key (resolveId p.indexed scope path)
    let resolved : GeometryProfile DeclId :=
      ⟨← resolveGeometrySetting p.indexed scope "scheme" profile.scheme,
       ← resolveGeometrySetting p.indexed scope "smooth" profile.smooth,
       ← entry "point" profile.point, ← entry "morphism" profile.morphism,
       ← entry "pointed" profile.pointed, ← entry "compose" profile.compose,
       ← entry "apply" profile.apply⟩
    unless resolved.valid env do
      let reason := match invalidExportEntry env resolved with
        | some reason => s!": {reason}"
        | none => ""
      Namespace.problem {} "E_TYPE"
        s!"{exportName owner} does not match its declared finite contracts{reason}"
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
  let declarations ← elaborateFrames sources declarations
  let declarations ← elaborateNature sources declarations
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

private def representationSpelling : Indexed.Representation → String
  | .affineDescriptor => "affine_descriptor"
  | .scalarBase .. => "scalar_base"
  | .linearDescriptor .. => "linear_descriptor"
  | .presentedAffine _ => "presented_affine"
  | .smoothAffine => "smooth_affine"

private def kindSpelling : CoefficientKind → String
  | .real => "real"
  | .complex => "complex"

/-- How an implementation comes by its coefficient kind. -/
private def kindClause (representation : Indexed.Representation) (kind : CoefficientKind) : String :=
  match representation with
  | .smoothAffine => "is `smooth_affine`, which counts as `real`"
  | _ => s!"has the kind `{kindSpelling kind}`"

/-- Presentation only: the rule of `Entry.Valid` that an invalid
`implementation` declaration breaks, in the words of the source. The rules of
the declaration itself come first, then the rule that the implementations of
one marker have one coefficient kind, which names a second declaration. The
result is `none` for another declaration, and for an implementation that
breaks no rule of this function. -/
def implementationRule (env : Environment) (entry : Entry) : Option String := do
  let .implementation marker representation capabilities := entry.declaration | none
  let name := qualified entry.id
  let form := representationSpelling representation
  if !isMarker env marker then
    return s!"the marker of the implementation `{name}` must be an `indexed marker`, " ++
      s!"but `{qualified marker}` is not one"
  if !decide capabilities.Nodup then
    return s!"the capability list of the implementation `{name}` names a capability twice"
  if representation == .affineDescriptor then failure
  if !capabilities.isEmpty then
    return s!"the `{form}` implementation `{name}` must have an empty capability list"
  let own : Option String := match representation with
    | .scalarBase .smooth .complex =>
      some s!"the `scalar_base` implementation `{name}` has the setting `smooth`, which must have the kind `real`"
    | .linearDescriptor base coefficient =>
      match scalarBaseProfile env base with
      | none => some <| s!"the base of the `linear_descriptor` implementation `{name}` must be an " ++
          s!"`indexed global` of a `scalar_base` implementation, but `{qualified base}` is not one"
      | some (baseMarker, .scheme, baseCoefficient) =>
        if coefficient != baseCoefficient then
          some <| s!"the linear implementation `{name}` over the `scheme` base `{qualified base}` must have " ++
            s!"the kind `{kindSpelling baseCoefficient}` of the implementation of its base, " ++
            s!"but it has the kind `{kindSpelling coefficient}`"
        else if marker != baseMarker then
          some <| s!"the linear implementation `{name}` over the `scheme` base `{qualified base}` must have " ++
            s!"the marker `{qualified baseMarker}` of the implementation of its base, " ++
            s!"but it has the marker `{qualified marker}`"
        else none
      | some (baseMarker, .smooth, baseCoefficient) =>
        if baseCoefficient != .real then
          some <| s!"the `smooth` base `{qualified base}` of the linear implementation `{name}` must have " ++
            "the kind `real`"
        else match coefficient with
          | .real =>
            if marker != baseMarker then
              some <| s!"the `real` linear implementation `{name}` over the `smooth` base `{qualified base}` " ++
                s!"must have the marker `{qualified baseMarker}` of the implementation of its base, " ++
                s!"but it has the marker `{qualified marker}`"
            else none
          | .complex =>
            if marker == baseMarker then
              some <| s!"the `complex` linear implementation `{name}` over the `smooth` base " ++
                s!"`{qualified base}` must have another marker than `{qualified marker}`, " ++
                "the marker of the implementation of its base"
            else none
    | _ => none
  if let some rule := own then return rule
  let kind ← representation.coefficient
  let (other, otherRepresentation, otherKind) ← env.findSome? fun other => match other.declaration with
    | .implementation otherMarker otherRepresentation _ =>
      if otherMarker == marker then
        otherRepresentation.coefficient.bind fun otherKind =>
          if otherKind != kind then some (other.id, otherRepresentation, otherKind) else none
      else none
    | _ => none
  return s!"the implementations of the marker `{qualified marker}` must have one coefficient kind, " ++
    s!"but `{name}` {kindClause representation kind} and `{qualified other}` " ++
    s!"{kindClause otherRepresentation otherKind}"

/-- How the source spells the binding of a primitive declaration. -/
private def bindingSpelling : Option Body → String
  | some (.primitive primitive) => primitive.op
  | some (.morphism ..) => "morphism"
  | some (.iso ..) => "iso"
  | some (.cartesian ..) => "cartesian"
  | _ => "primitive"

/-- Presentation only: the rule of `Entry.Valid` that an invalid entry breaks,
as a code and a message. -/
def entryRule (env : Environment) (ranks : List (DeclId × Nat)) (entry : Entry) : Option Rule :=
  ((implementationRule env entry).map ("E_TYPE", ·)).orElse fun _ =>
    (classificationRule env ranks entry).orElse fun _ =>
      (globalRule env entry).orElse fun _ => familyRule env entry

/-- Presentation only: the diagnostic for declarations that
`Core.validDeclarations` rejects. It is at the first declaration that fails
its own check, and its message is the rule that the declaration breaks, where
`entryRule`, `packageRule` or `primitiveRule` finds one. A size limit of a
declaration is `E_LIMIT`, every other rule `E_TYPE`. Acceptance is
`Core.validDeclarations` alone. -/
def invalidDeclaration (p : Program) (env : Core.Declarations) : Diagnostic :=
  let general := "invalid indexed declaration, package, or primitive contract"
  let source (id : DeclId) : Option Declaration := (p.owned.find? (·.1 == id)).map (·.2)
  let span (id : DeclId) : Span := ((source id).map (·.span)).getD {}
  let ranks := classRanks env.indexed
  match env.indexed.find? (fun entry => !validEntry env.indexed ranks entry) with
  | some entry =>
    let (code, message) := (entryRule env.indexed ranks entry).getD ("E_TYPE", general)
    { code, message, span := span entry.id }
  | none =>
    match env.packages.find? (fun declaration => !decide (declaration.Valid env.indexed)) with
    | some declaration =>
      let (code, message) := (packageRule env.indexed declaration).getD ("E_TYPE", general)
      { code, message, span := span declaration.id }
    | none =>
      match env.primitives.find? (fun declaration => !validPrimitiveBinding env.indexed declaration.binding) with
      | some declaration =>
        let op := bindingSpelling ((source declaration.id).map (·.body))
        { code := "E_TYPE", span := span declaration.id,
          message := (primitiveRule env.indexed declaration.id op declaration.binding).getD general }
      | none => { code := "E_TYPE", message := general }

def checkDeclarations (p : Program) : Except Diagnostic (CheckedDeclarations p) := do
  -- At the first declaration beyond the limit.
  if p.owned.length > 4096 then
    Namespace.problem ((p.owned[4096]?.map (·.2.span)).getD {}) "E_LIMIT" "more than 4096 indexed declarations"
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
            else .error (invalidDeclaration p resolved.declarations)
          else Namespace.problem {} "E_OWNER" "indexed declaration identity audit failed"
        else Namespace.problem {} "E_OWNER" "indexed declaration reference audit failed"
    else Namespace.problem {} "E_DUPLICATE" "duplicate declaration owner"

end VastitasKernel.Indexed.Source
