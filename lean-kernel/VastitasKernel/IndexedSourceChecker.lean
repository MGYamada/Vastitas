import VastitasKernel.FiniteProjection
import VastitasKernel.IndexedPrimitiveFamilies
import VastitasKernel.NamespaceChecker
import VastitasKernel.IndexedTypeAudit
import VastitasKernel.IndexedAlgebraSource
import VastitasKernel.IndexedSmoothSource
import VastitasKernel.IndexedMetricSource
import VastitasKernel.IndexedFrameSource
import VastitasKernel.IndexedNatureSource
import VastitasKernel.IndexedSpectralSource
import VastitasKernel.IndexedModelSource
import VastitasKernel.IndexedErrorbarSource
import VastitasKernel.IndexedDeclarationRules
import VastitasKernel.IndexedGluingSource

namespace VastitasKernel.Indexed.Source

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

/-- The one object of a spectral declaration `form<X>` (Stage 5). -/
def spectralObject (span : Span) (what form : String) (indices : List DeclId) : ResolveM DeclId :=
  match indices with
  | [object] => pure object
  | _ => Namespace.problem span "E_SPECTRAL" <|
      s!"{what} names one object, as in `{form}<X>`, but {indices.length} are given"

/-- The one object of a Stage 6 declaration `form<X>` (#841), with the code
of its module: `E_SPECTRAL` for a transition average, `E_MODEL` for a model
and `E_ERRORBAR` for a calibration, a dataset or a comparison. -/
def stage6Object (code : String) (span : Span) (what form : String) (indices : List DeclId) : ResolveM DeclId :=
  match indices with
  | [object] => pure object
  | _ => Namespace.problem span code <|
      s!"{what} names one object, as in `{form}<X>`, but {indices.length} are given"

def resolveBody (p : Namespace.Indexed) (graphs : GraphSources) (projections : ProjectionCache)
    (owner : DeclId) (span : Span) (body : Body)
    (env : Core.Declarations) : ResolveM Core.Declarations := do
  let scope := owner.scope
  let add (declaration : Indexed.Declaration) := { env with indexed := env.indexed ++ [⟨owner, declaration⟩] }
  match body with
  | .marker => return add .marker
  | .finiteCarrier tags =>
      if tags.length > FiniteTables.limit then Namespace.problem span "E_LIMIT" "finite carrier exceeds 4096 tags"
      let mut seen : Std.HashSet String := {}
      for tag in tags do
        unless FiniteTables.validCarrier [tag.name] do Namespace.problem tag.span "E_NAME" "invalid finite carrier tag"
        if seen.contains tag.name then Namespace.problem tag.span "E_DUPLICATE" s!"duplicate finite tag '{tag.name}'"
        seen := seen.insert tag.name
      return add (.finiteCarrier (tags.map (·.name)))
  | .finiteTable inputs output rows =>
      return add (.finiteTable (← inputs.mapM (resolveFinitePath p graphs projections scope)) (← resolveFinitePath p graphs projections scope output)
        (rows.map fun r => (r.key.map (·.name), r.value.name)))
  | .categorySchema => return add .categorySchema
  | .functorSchema => return add .functorSchema
  | .natTransSchema => return add .natTransSchema
  | .monadSchema => return add .monadSchema
  | .kleisliSchema kind base => return add (.kleisliSchema kind (← resolveId p scope base))
  | .finiteKleisli kind schema monad =>
      return add (.finiteKleisli kind (← resolveId p scope schema) (← resolveId p scope monad))
  | .finiteMonad schema fields =>
      return add (.finiteMonad (← resolveId p scope schema) (← fields.mapM (resolveId p scope)))
  | .finiteNatTrans schema n =>
      return add (.finiteNatTrans (← resolveId p scope schema)
        ⟨← resolveId p scope n.source, ← resolveId p scope n.target,
         ← resolveFinitePath p graphs projections scope n.components⟩)
  | .finiteFunctor schema maps =>
      return add (.finiteFunctor (← resolveId p scope schema)
        ⟨← resolveId p scope maps.source, ← resolveId p scope maps.target,
         ← resolveFinitePath p graphs projections scope maps.objects,
         ← resolveFinitePath p graphs projections scope maps.arrows⟩)
  | .composableTable inputs output src dst rows =>
      return add (.composableTable (← inputs.mapM (resolveFinitePath p graphs projections scope)) (← resolveFinitePath p graphs projections scope output)
        (← resolveFinitePath p graphs projections scope src) (← resolveFinitePath p graphs projections scope dst) (rows.map fun r => (r.key.map (·.name), r.value.name)))
  | .finiteCategory schema graph =>
      return add (.finiteCategory (← resolveId p scope schema) (← graph.mapM (resolveFinitePath p graphs projections scope)))
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
      match definition with
      | .restrict morphism | .tracePower morphism _ | .charCoefficient morphism _ =>
        let _ ← resolveId p scope morphism
      | _ => pure ()
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
  /- Spectral declarations (Stage 5). Every path is resolved here; the rows,
  the certificates and the polynomials are elaborated once the objects are
  known (`elaborateSpectral`). -/
  | .freeModule family indices basis => do
      let family ← resolveId p scope family
      let object ← spectralObject span "a free module" "FreeModule" (← indices.mapM (resolveId p scope))
      return add (.freeModule family object basis)
  | .endomorphism family indices module _ symmetric => do
      let family ← resolveId p scope family
      let object ← spectralObject span "an endomorphism" "Endomorphism" (← indices.mapM (resolveId p scope))
      return add (.endomorphism family object (← resolveId p scope module) [] symmetric)
  | .spectrum family indices endomorphism fiber => do
      let family ← resolveId p scope family
      let object ← spectralObject span "a spectrum" "Spectrum" (← indices.mapM (resolveId p scope))
      return add (.spectrum family object (← resolveId p scope endomorphism) fiber ⟨[], [], []⟩)
  | .branch family indices spectrum _ _ exponent => do
      let family ← resolveId p scope family
      let object ← spectralObject span "a branch" "Branch" (← indices.mapM (resolveId p scope))
      return add (.branch family object (← resolveId p scope spectrum) [] [] exponent [])
  /- Stage 6 declarations (#841). Every path is resolved here; the basis and
  coordinate names, the closed forms, the values and the certificates are
  elaborated once the objects are known (`elaborateAverages`,
  `elaborateModels`, `elaborateErrorbars`). -/
  | .transitionAverage family indices branch _ _ _ _ => do
      let family ← resolveId p scope family
      let object ← stage6Object "E_SPECTRAL" span "a transition average" "TransitionAverage"
        (← indices.mapM (resolveId p scope))
      return add (.transitionAverage family object (← resolveId p scope branch) 0 0 [] [] ⟨[], [], 0⟩)
  | .convention value => return add (.convention value)
  | .model family indices hamiltonian reading convention _ _ predicts regime => do
      let family ← resolveId p scope family
      let object ← stage6Object "E_MODEL" span "a model" "Model" (← indices.mapM (resolveId p scope))
      let hamiltonian ← resolveId p scope hamiltonian
      let reading ← resolveId p scope reading
      let convention ← resolveId p scope convention
      return add (.model family object hamiltonian reading convention 0 0 (← resolveId p scope predicts) regime)
  | .calibration family indices _ method reference revision => do
      let family ← resolveId p scope family
      let object ← stage6Object "E_ERRORBAR" span "a calibration" "Calibration" (← indices.mapM (resolveId p scope))
      return add (.calibration family object [] method reference revision)
  | .dataset family indices model calibration _ _ => do
      let family ← resolveId p scope family
      let object ← stage6Object "E_ERRORBAR" span "a dataset" "Dataset" (← indices.mapM (resolveId p scope))
      let model ← resolveId p scope model
      return add (.dataset family object model (← resolveId p scope calibration) 0 [])
  | .comparison family indices dataset calibration fingerprint verdict => do
      let family ← resolveId p scope family
      let object ← stage6Object "E_ERRORBAR" span "a comparison" "Comparison" (← indices.mapM (resolveId p scope))
      let dataset ← resolveId p scope dataset
      return add (.comparison family object dataset (← resolveId p scope calibration) fingerprint verdict)
  /- Gluing (Stage 7, #878). Every path is resolved here; the images, the
  coefficients, the witnesses and the chart entries are elaborated once the
  opens and their charts are known (`elaborateGluing`). -/
  | .glued implementation opens _ _ => do
      let implementation ← resolveId p scope implementation
      let opens ← opens.mapM (resolveId p scope)
      let [first, second] := opens
        | Namespace.problem span "E_GLUE" <| s!"a gluing of this profile has exactly two charts, but " ++
            (if opens.length == 1 then "1 open is given" else s!"{opens.length} opens are given") ++
            (if opens.length > 2 then
              "; three or more charts need cocycle checks on triple overlaps, which the profile does not implement"
            else "")
      return add (.glued implementation first second [] [])
  | .cover object opens _ => do
      return add (.cover (← resolveId p scope object) (← opens.mapM (resolveId p scope)) [])
  | .separated glued _ _ => return add (.separated (← resolveId p scope glued) [])
  | .manifold glued dimension _ _ => return add (.manifold (← resolveId p scope glued) dimension [])
  | .projective glued homogeneous charts => do
      let glued ← resolveId p scope glued
      let charts ← charts.mapM fun chart => do
        let id ← resolveId p scope chart.chart
        pure ({ chart := id, dehomogenized := 0, image := [], inverse := [] } :
          GluingDeclarations.ProjectiveChart)
      return add (.projective glued homogeneous charts)

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
  let owned := p.owned
  let graphs := graphSources owned
  let action : ResolveM Core.Declarations := do
    let projections ← buildProjectionCache index graphs owned
    owned.foldlM (fun env entry =>
      resolveBody index graphs projections entry.1 entry.2.span entry.2.body env) ⟨[], [], []⟩
  let (declarations, references) ← action.run []
  let sources := p.owned.map fun (owner, d) => (owner, d.span, d.body)
  checkSmoothImplementations sources declarations
  let declarations ← elaborateSmoothOpens sources declarations
  let declarations ← elaborateAffine sources declarations
  let declarations ← elaborateSmooth sources declarations
  let declarations ← elaborateMetrics sources declarations
  let declarations ← elaborateFrames sources declarations
  let declarations ← elaborateNature sources declarations
  -- The endomorphism or spectrum that each spectral invariant names.
  let spectralTargets ← p.owned.filterMapM fun (owner, d) => match d.body with
    | .morphism _ _ (.tracePower target _) | .morphism _ _ (.charCoefficient target _) => do
      let resolved ← Namespace.resolve index owner.scope target.path target.span
      pure (some (owner, resolved.owner))
    | _ => pure none
  let declarations ← elaborateSpectral sources spectralTargets declarations
  let declarations ← elaborateAverages sources declarations
  let declarations ← elaborateModels sources declarations
  let declarations ← elaborateErrorbars sources declarations
  let restrictTargets ← p.owned.filterMapM fun (owner, d) => match d.body with
    | .morphism _ _ (.restrict morphism) => do
      let target ← Namespace.resolve index owner.scope morphism.path morphism.span
      pure (some (owner, target.owner))
    | _ => pure none
  let declarations ← elaborateRelative sources declarations restrictTargets
  let declarations ← elaborateGluing sources declarations
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
here; they are composed by the public entry point `ResourceSource.Wire.check`. -/
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

/-- Explain an independently rejected finite table using the original row and
tag spans. Acceptance remains the check on the complete Core environment. -/
private def tableDiagnostic (env : Environment) (entry : Entry) (source : Declaration) :
    Option Diagnostic := do
  let named := FiniteCategories.view env
  let issue := fun (span : Span) (message : String) => ({ code := "E_FINITE_TABLE", message, span } : Diagnostic)
  if let .composableTable inputs out src dst rows := entry.declaration then
    let .composableTable _ _ s t sourceRows := source.body | none
    if inputs != [out, out] then return issue source.span "composition requires the same arrow carrier twice and as result"
    if (FiniteCategories.unary named src out).isNone then return issue s.span "source must map the arrow carrier to objects"
    let some e := FiniteCategories.endpoints named out src dst | return issue t.span "source and destination must share their arrow and object carriers"
    let some pairs := e.pairs | return { code := "E_LIMIT", span := source.span, message := "finite composability check exceeds the profile or depends on an invalid endpoint table" }
    let allowed := Std.HashSet.ofList pairs
    let tags := Std.HashSet.ofList e.arrows
    let mut seen : Std.HashSet (List String) := {}
    for ((key, value), row) in rows.zip sourceRows do
      if !allowed.contains key then return issue row.span "this pair of arrows is not composable"
      if seen.contains key then return issue row.span "duplicate composition row"
      if !tags.contains value then return issue row.value.span "composition result must name an arrow"
      seen := seen.insert key
    return issue source.span "composition table is missing a composable pair"
  if let .finiteCategory schema fields := entry.declaration then
    let .finiteCategory schemaPath paths := source.body | none
    let problem := fun (sp : Span) (msg : String) => ({ span := sp, code := "E_CATEGORY", message := msg } : Diagnostic)
    if named schema != some .categorySchema then return problem schemaPath.span "instance must select a finite category schema"
    let some g := FiniteCategories.graph named schema fields
      | return problem source.span "finite graph fields do not have the declared nominal endpoints or composition domain"
    let some pairs := g.toEndpoints.pairs
      | return { span := paths.comp.span, code := "E_LIMIT", message := "finite category key comparison exceeds the bounded profile" }
    if pairs.length * g.arrows.length > Limits.elaborationWork then
      return { span := paths.comp.span, code := "E_LIMIT", message := "finite category law checks exceed the bounded profile" }
    if let some obj := g.objects.find? (!g.identityAt ·) then return problem paths.ids.span s!"identity of '{obj}' has incorrect endpoints"
    if let some arr := g.arrows.find? (!g.units ·) then return problem paths.comp.span s!"left or right identity law fails for '{arr}'"
    for key in pairs do
      if let [m, f] := key then
        if !g.ends m f then return problem paths.comp.span s!"composition of '{m}' after '{f}' has incorrect endpoints"
        if let some h := g.arrows.find? (fun h => g.composable h m && !g.assoc h m f) then
          return problem paths.comp.span s!"associativity fails at ('{h}', '{m}', '{f}')"
    return problem source.span "invalid finite category instance"
  if let .finiteFunctor schema maps := entry.declaration then
    let .finiteFunctor schemaPath paths := source.body | none
    let problem := fun (sp : Span) (msg : String) => ({ span := sp, code := "E_FUNCTOR", message := msg } : Diagnostic)
    if named schema != some .functorSchema then return problem schemaPath.span "instance must select a finite functor schema"
    let some (c, _) := FiniteFunctors.category named maps.source
      | return problem paths.source.span "functor source endpoint must name a finite category"
    let some (d, _) := FiniteFunctors.category named maps.target
      | return problem paths.target.span "functor target endpoint must name a finite category"
    if (FiniteFunctors.mapping named maps.objects c.objects d.objects).isNone then
      return problem paths.objects.span "object map must be unary with the selected nominal object carriers"
    if (FiniteFunctors.mapping named maps.arrows c.arrows d.arrows).isNone then
      return problem paths.arrows.span "arrow map must be unary with the selected nominal arrow carriers"
    let some m := FiniteFunctors.model named schema maps | return problem source.span "invalid finite functor fields"
    let some pairs := m.source.toEndpoints.pairs
      | return { span := paths.source.span, code := "E_LIMIT", message := "functor source composability exceeds the bounded profile" }
    if m.source.objects.length > FiniteTables.limit then
      return { span := paths.source.span, code := "E_LIMIT", message := "functor source exceeds the object tag limit" }
    if let some f := m.source.arrows.find? (!m.endpointsAt ·) then
      return problem paths.arrows.span s!"arrow map does not preserve endpoints of '{f}'"
    if let some x := m.source.objects.find? (!m.identityAt ·) then
      return problem paths.arrows.span s!"functor does not preserve the identity of '{x}'"
    for key in pairs do
      if let [g, f] := key then
        if !m.compositionAt g f then return problem paths.arrows.span s!"functor does not preserve composition of '{g}' after '{f}'"
    return problem source.span "invalid finite functor instance"
  if let .finiteNatTrans schema n := entry.declaration then
    let .finiteNatTrans schemaPath paths := source.body | none
    let problem := fun (sp : Span) (msg : String) => ({ span := sp, code := "E_NAT_TRANS", message := msg } : Diagnostic)
    if named schema != some .natTransSchema then return problem schemaPath.span "instance must select a finite natural transformation schema"
    let some f := FiniteNatTrans.functorFields named n.source
      | return problem paths.source.span "transformation source must name a finite functor"
    let some g := FiniteNatTrans.functorFields named n.target
      | return problem paths.target.span "transformation target must name a finite functor"
    if !FiniteNatTrans.parallel f g then
      return problem paths.target.span "the two functors must have the same nominal source and target categories"
    let some (.finiteCategory _ c) := named f.source | return problem paths.source.span "invalid functor source category"
    let some (.finiteCategory _ d) := named f.target | return problem paths.source.span "invalid functor target category"
    if (FiniteFunctors.mapping named n.components c.objects d.arrows).isNone then
      return problem paths.components.span "components must be unary with the nominal source object and target arrow carriers"
    let some m := FiniteNatTrans.model named schema n | return problem source.span "invalid selected finite functor fields"
    if !FiniteNatTrans.bounded m then
      return { span := paths.source.span, code := "E_LIMIT", message := "naturality check exceeds the finite carrier limits" }
    if let some x := m.domain.objects.find? (!m.endpointsAt ·) then
      return problem paths.components.span s!"component at '{x}' has incorrect endpoints"
    if let some f := m.domain.arrows.find? (!m.naturalAt ·) then
      return problem paths.components.span s!"naturality fails on arrow '{f}'"
    return problem source.span "invalid finite natural transformation"
  if let .kleisliSchema .. := entry.declaration then
    let .kleisliSchema _ base := source.body | none
    return { code := "E_KLEISLI", span := base.span, message := "a Kleisli schema requires a named finite Monad schema" }
  if let .finiteKleisli kind schema _ := entry.declaration then
    let .finiteKleisli _ schemaPath monadPath := source.body | none
    if !(named schema).any (fun d => match d with
        | .kleisliSchema k _ => k == kind
        | _ => false) then
      return { code := "E_KLEISLI", span := schemaPath.span, message := "instance must select a Kleisli schema of the same kind" }
    return { code := "E_KLEISLI", span := monadPath.span, message := "view requires a named Monad of its schema's exact Monad schema" }
  if let .finiteMonad schema fields := entry.declaration then
    let .finiteMonad schemaPath paths := source.body | none
    let problem := fun (sp : Span) (msg : String) => ({ span := sp, code := "E_MONAD", message := msg } : Diagnostic)
    match FiniteMonads.select named schema fields with
    | .error .schema => return problem schemaPath.span "instance must select a finite Monad schema"
    | .error .category => return problem paths.category.span "Monad requires a named finite category"
    | .error .functor => return problem paths.functor.span "Monad requires an endofunctor on the exact selected nominal category"
    | .error .unit => return problem paths.unit.span "unit must be a natural transformation from an identity functor to the exact selected endofunctor"
    | .error .multiplication => return problem paths.multiplication.span "multiplication must be a natural transformation from a square functor to the exact selected endofunctor"
    | .ok m =>
      if !FiniteMonads.bounded m then
        return { span := paths.category.span, code := "E_LIMIT", message := "Monad diagrams exceed the finite carrier limits" }
      if !m.category.objects.all (FiniteMonads.identityAt m.identityObjects) ||
          !m.category.arrows.all (FiniteMonads.identityAt m.identityArrows) then
        return problem paths.unit.span "unit source must act as the identity on every object and arrow"
      if !m.category.objects.all (FiniteMonads.squareAt m.squareObjects m.objects) ||
          !m.category.arrows.all (FiniteMonads.squareAt m.squareArrows m.arrows) then
        return problem paths.multiplication.span "multiplication source must act as the square of the selected functor on every object and arrow"
      if let some x := m.category.objects.find? (!m.unitAt ·) then
        return problem paths.unit.span s!"Monad unit law fails at '{x}'"
      if let some x := m.category.objects.find? (!m.assocAt ·) then
        return problem paths.multiplication.span s!"Monad associativity fails at '{x}'"
      return problem source.span "invalid finite Monad instance"
  let .finiteTable inputs output _ := entry.declaration | none
  let .finiteTable paths result rows := source.body | none
  let mut domains := []
  for (id, path) in inputs.zip paths do
    let some tags := FiniteTables.carrier env id | return issue path.span "table input must name a finite carrier"
    domains := domains ++ [tags]
  let some range := FiniteTables.carrier env output | return issue result.span "table output must name a finite carrier"
  let some _ := FiniteTables.keys domains
    | return { code := "E_LIMIT", span := source.span, message := "finite table key product exceeds the bounded profile" }
  let allowed := domains.map Std.HashSet.ofList
  let outputs := Std.HashSet.ofList range
  let mut seen : Std.HashSet (List String) := {}
  for row in rows do
    if row.key.length != allowed.length then return issue row.span "finite table row has the wrong arity"
    for (tag, tags) in row.key.zip allowed do
      if !tags.contains tag.name then return issue tag.span s!"unknown input tag '{tag.name}' for this carrier"
    if !outputs.contains row.value.name then return issue row.value.span s!"unknown result tag '{row.value.name}' for this carrier"
    let key := row.key.map (·.name)
    if seen.contains key then return issue row.span "duplicate finite table row"
    seen := seen.insert key
  return issue source.span "finite table has missing rows for the declared product"

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
    if let some d := (source entry.id).bind (tableDiagnostic env.indexed entry) then d else
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
