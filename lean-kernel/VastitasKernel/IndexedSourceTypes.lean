import VastitasKernel.IndexedSourceChecker

/-! Declaration-driven type elaboration shared by all public source protocols.
Type names choose canonical declarations, never a privileged geometric
meaning. Local object indices come from actual supplied Core bindings. -/
namespace VastitasKernel.Indexed.Source

structure Binding where
  name : String
  parameter : Core.Parameter
  span : Span := {}
  deriving Repr, Inhabited

abbrev TypeContext := List Binding

def TypeContext.core (ctx : TypeContext) : Core.Typing.Context := ctx.map (·.parameter)

def TypeContext.lookup (ctx : TypeContext) (name : String) : Option Core.Parameter :=
  (ctx.find? fun binding => binding.name == name).map (·.parameter)

def ContextValid (program : Source.Program) (env : Core.Declarations)
    (scope : Namespace.Scope) (ctx : TypeContext) : Prop :=
  scope ∈ program.toNamespace.scopes ∧ (ctx.map (·.name)).Nodup ∧
    (ctx.map (·.parameter.symbol)).Nodup ∧ ∀ binding ∈ ctx,
      binding.parameter.result.Valid env ∧
      (Namespace.binder program.indexed scope binding.name binding.span).isOk = true

instance (program : Source.Program) (env : Core.Declarations)
    (scope : Namespace.Scope) (ctx : TypeContext) : Decidable (ContextValid program env scope ctx) := by
  unfold ContextValid
  infer_instance

/-- `span` is the place of the indexed type, for a literal, which has no place
of its own. -/
def resolveTypeArgument (program : Namespace.Indexed) (scope : Namespace.Scope)
    (ctx : TypeContext) (expected : Indexed.Parameter) (argument : TypeArgument) (span : Span := {}) :
    ResolveM Index := do
  match expected, argument with
  | .natural, .natural value => return .natural value
  | .object _, .name path =>
      if let [name] := path.path then
        if let some binding := ctx.lookup name then
          let .object _ := binding.result.type
            | Namespace.problem path.span "E_TYPE" "an object index requires an object value"
          let some reference := binding.result.reference
            | Namespace.problem path.span "E_TYPE" "object binding has no nominal reference"
          return .object reference
      return .object (.global (← resolveId program scope path))
  | .domain, .name path => return .domain (← resolveId program scope path)
  | .marker, .name path => return .marker (← resolveId program scope path)
  -- A frame index names a frame declaration; `Parameter.Accepts` checks its family.
  | .frame _, .name path => return .frame (← resolveId program scope path)
  | _, .name path => Namespace.problem path.span "E_TYPE" "natural index requires a literal"
  | _, .natural _ => Namespace.problem span "E_TYPE" "natural literal used at a non-natural index"

def resolveTypeArguments (program : Namespace.Indexed) (scope : Namespace.Scope)
    (ctx : TypeContext) (parameters : List Indexed.Parameter) (arguments : List TypeArgument)
    (span : Span) : ResolveM (List Index) := do
  if parameters.length != arguments.length then
    Namespace.problem span "E_TYPE" "indexed type has the wrong number of arguments"
  (parameters.zip arguments).mapM fun (parameter, argument) =>
    resolveTypeArgument program scope ctx parameter argument span

def geometryBase (name : String) : ResolveM BaseKind :=
  match name with
  | "QQ" => pure .qq | "CInfReal" => pure .cinfReal
  | _ => Namespace.problem {} "E_RING" "unknown compatibility coefficient marker"

def geometryIndex (profile : GeometryProfile DeclId) (ctx : TypeContext) : RawIndex → ResolveM Indexed.ObjectRef
  | .base name => return .global (profile.setting (← geometryBase name)).baseObject
  | .name name => do
    let some binding := ctx.lookup name
      | Namespace.problem {} "E_TYPE" "legacy object index requires an in-scope object, not a coefficient marker"
    let .object _ := binding.result.type | Namespace.problem {} "E_TYPE" "legacy index is not an object"
    let some ref := binding.result.reference | Namespace.problem {} "E_TYPE" "object index has no nominal reference"
    return ref

def legacyDataType (profile : GeometryProfile DeclId) (ctx : TypeContext) : RawType → ResolveM Core.DataType
  | .named "Scheme" => pure (.object profile.scheme.objectType)
  | .named "CInfScheme" => pure (.object profile.smooth.objectType)
  | .point target source => return .indexed ⟨profile.point,
      [.object (← geometryIndex profile ctx target), .object (← geometryIndex profile ctx source)]⟩
  | .morphism source target => return .indexed ⟨profile.morphism,
      [.object (← geometryIndex profile ctx source), .object (← geometryIndex profile ctx target)]⟩
  | .pointed setting marker => do
    let base ← geometryBase marker
    unless (setting == "Scheme" && base == .qq) || (setting == "CInfScheme" && base == .cinfReal) do
      Namespace.problem {} "E_BASE" "Pointed setting and coefficient base disagree"
    return .package (profile.package base)
  | _ => Namespace.problem {} "E_TYPE" "unsupported legacy geometry annotation"

/-- Resolve the visible owner of a category projection. A private underlying
Monad or category stays accessible only through its checked public view. -/
def projectedMonadCategory? (program : Namespace.Indexed) (scope : Namespace.Scope)
    (env : Environment) (path : Path) : Option (Path × Namespace.Target × DeclId) := do
  let "category" :: rest := path.path.reverse | none
  let base : Path := ⟨rest.reverse, path.span⟩
  let target ← (Namespace.resolve program scope base.path base.span).toOption
  guard (target.kind == .indexedDeclaration)
  let model ← FiniteSort.monadOwner? env target.owner
  let .finiteMonad _ fields ← lookup env model | none
  return (base, target, fields.category)

/-- Object indices carry the owner of their finite carrier through ordinary name resolution. -/
def homEndpoint (program : Namespace.Indexed) (scope : Namespace.Scope)
    (path : Path) (env : Indexed.Environment) (g : FiniteCategories.Graph) : ResolveM String := do
  let tag :: head :: tail := path.path.reverse
    | Namespace.problem path.span "E_TYPE" "expected an object carrier and tag"
  let carrier : Path := ⟨(head :: tail).reverse, path.span⟩
  let projected := Id.run do
    let "objects" :: model :: rest := head :: tail | return none
    let base : Path := ⟨(model :: rest).reverse, path.span⟩
    let selected := do
      if let some p := projectedMonadCategory? program scope env base then return p
      let resolved ← (Namespace.resolve program scope base.path base.span).toOption
      guard (resolved.kind == .indexedDeclaration)
      if let some owner := KleisliViews.selected (FiniteCategories.view env) .category resolved.owner then
        let .finiteMonad _ fields ← lookup env owner | none
        return (base, resolved, fields.category)
      return (base, resolved, resolved.owner)
    let some (visible, resolved, cat) := selected | return none
    let some (.finiteCategory _ fields) := Indexed.lookup env cat | return none
    return some (visible, resolved, fields.objects)
  let id ← match projected with
    | some (base, resolved, objects) => do
      modify (⟨scope, base, resolved⟩ :: ·)
      pure objects
    | none => resolveId program scope carrier
  unless id == g.objectId && g.objects.contains tag do
    Namespace.problem path.span "E_TYPE" "endpoint is not an object of the selected finite category"
  return tag

private structure HomCategory where
  owner : DeclId
  graph : FiniteCategories.Graph
  targetAction : Option FiniteCategories.Table := none

private def homCategory (program : Namespace.Indexed) (scope : Namespace.Scope) (env : Environment)
    (category : Path) : ResolveM HomCategory := do
  let owner ← do
    if let some (base, target, cat) := projectedMonadCategory? program scope env category then
      modify (⟨scope,base,target⟩ :: ·)
      pure cat
    else resolveId program scope category
  if let some monad := KleisliViews.selected (FiniteCategories.view env) .category owner then
    let some (fields, m) := FiniteSort.monad? env monad
      | Namespace.problem category.span "E_MONAD" "Kleisli category requires its selected finite Monad"
    return ⟨fields.category, m.category, some m.objects⟩
  let some (_, g) := FiniteSort.selected env owner
    | Namespace.problem category.span "E_TYPE" "Hom requires a named finite category instance"
  return ⟨owner, g, none⟩

/-- A concrete static object action resolves the named Monad in the original
scope and checks that its category is the selected Hom category. The internal
angle-bracket marker cannot be an identifier in an ordinary path. -/
private def mappedEndpoint (program : Namespace.Indexed) (scope : Namespace.Scope)
    (env : Environment) (owner : DeclId) (g : FiniteCategories.Graph) (path : Path) : ResolveM String :=
  visit (Limits.typeNesting + 1) path.path
where
  visit : Nat → List String → ResolveM String
    | 0, _ => Namespace.problem path.span "E_LIMIT" "Monad object action exceeds the type nesting limit"
    | fuel+1, parts => do
      let (base, suffix) := parts.span (· != "T<>")
      if let _ :: arg := suffix then
        if base.isEmpty then Namespace.problem path.span "E_TYPE" "object action requires a named Monad"
        let authority ← resolveId program scope ⟨base, path.span⟩
        let some (fields,m) := (FiniteSort.monadOwner? env authority).bind (FiniteSort.monad? env)
          | Namespace.problem path.span "E_MONAD" "object action requires a named finite Monad"
        unless fields.category == owner do Namespace.problem path.span "E_TYPE" "object action belongs to a different category"
        let x ← visit fuel arg
        let some tx := FiniteFunctors.image m.objects x
          | Namespace.problem path.span "E_TYPE" "object action has no value at this endpoint"
        return tx
      homEndpoint program scope ⟨parts,path.span⟩ env g

def elaborateDataType (program : Namespace.Indexed) (env : Core.Declarations)
    (scope : Namespace.Scope) (ctx : TypeContext) (input : Source.DataType)
    (geometry : Option (GeometryProfile DeclId) := none) : ResolveM Core.DataType := do
  match input with
  | .pure type => return .pure type
  | .object type => return .object (← resolveType program scope type)
  | .legacy type =>
      let some profile := geometry
        | Namespace.problem {} "E_TYPE" "legacy geometry syntax requires exactly one explicit library compatibility export"
      legacyDataType profile ctx type
  | .inferredPackage => Namespace.problem {} "E_TYPE" "an inferred package is only valid in legacy pack syntax"
  | .finiteHom category source target =>
      let cat ← homCategory program scope env.indexed category
      let x ← mappedEndpoint program scope env.indexed cat.owner cat.graph source
      let y ← mappedEndpoint program scope env.indexed cat.owner cat.graph target
      let targetTag ← match cat.targetAction with
        | none => pure y
        | some action => match FiniteFunctors.image action y with
          | some ty => pure ty
          | none => Namespace.problem target.span "E_TYPE" "Kleisli target has no image under the selected Monad"
      return .finite (.hom cat.owner x targetTag)
  | .application path arguments =>
      let id ← resolveId program scope path
      match Indexed.lookup env.indexed id with
      | some (.finiteCarrier _) =>
          unless arguments.isEmpty do Namespace.problem path.span "E_TYPE" "finite carrier takes no indices"
          return .finite id
      | some (.family family) => return .indexed ⟨id,
          ← resolveTypeArguments program scope ctx family.parameters arguments path.span⟩
      | _ =>
        if env.packages.any (·.id == id) then
          return .package ⟨id,
            ← resolveTypeArguments program scope ctx [.domain, .marker] arguments path.span⟩
        else Namespace.problem path.span "E_TYPE" "expected an indexed family or existential package"

structure ResolvedDataType where
  type : Core.DataType
  references : List Source.Reference
  deriving Repr, Inhabited

def lowerDataType (program : Source.Program) (env : Core.Declarations) (scope : Namespace.Scope)
    (ctx : TypeContext) (input : Source.DataType) : Namespace.Result ResolvedDataType := do
  let (type, references) ← (do
    let geometry ← resolveGeometry program env
    elaborateDataType program.indexed env scope ctx input geometry).run []
  return ⟨type, references.reverse⟩

/-- Indexed by the actual declaration certificate, scope, bindings and input.
This does not establish that arbitrary supplied bindings arise from execution;
the future term checker must derive them and check every actual body. -/
structure CheckedDataType {program : Source.Program} (declarations : CheckedDeclarations program)
    (scope : Namespace.Scope) (ctx : TypeContext) (input : Source.DataType) where
  resolved : ResolvedDataType
  contextValid : ContextValid program declarations.resolved.declarations scope ctx
  lowered : lowerDataType program declarations.resolved.declarations scope ctx input = .ok resolved
  valid : resolved.type.Valid declarations.resolved.declarations
  withinScope : resolved.type.Scoped (Core.Typing.contextRefs ctx.core)
  referencesValid : ∀ reference ∈ resolved.references, reference.Valid program.indexed

def checkDataType {program : Source.Program} (declarations : CheckedDeclarations program)
    (scope : Namespace.Scope) (ctx : TypeContext) (input : Source.DataType) :
    Except Diagnostic (CheckedDataType declarations scope ctx input) := do
  let env := declarations.resolved.declarations
  if contextValid : ContextValid program env scope ctx then
    match lowered : lowerDataType program env scope ctx input with
    | .error error => .error error
    | .ok resolved =>
      if valid : resolved.type.Valid env then
        if withinScope : resolved.type.Scoped (Core.Typing.contextRefs ctx.core) then
          if referencesValid : ∀ reference ∈ resolved.references, reference.Valid program.indexed then
            return ⟨resolved, contextValid, lowered, valid, withinScope, referencesValid⟩
          else Namespace.problem {} "E_OWNER" "indexed type reference audit failed"
        else Namespace.problem {} "E_SCOPE" "indexed type contains an out-of-scope object"
      else Namespace.problem {} "E_TYPE" "invalid indexed type contract, argument kind or object association"
  else Namespace.problem {} "E_CONTEXT" "invalid type binding, shadowed name or undeclared module"

end VastitasKernel.Indexed.Source
