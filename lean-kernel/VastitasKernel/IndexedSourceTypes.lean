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

def resolveTypeArgument (program : Namespace.Indexed) (scope : Namespace.Scope)
    (ctx : TypeContext) (expected : Indexed.Parameter) (argument : TypeArgument) : ResolveM Index := do
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
  | _, .name path => Namespace.problem path.span "E_TYPE" "natural index requires a literal"
  | _, .natural _ => Namespace.problem {} "E_TYPE" "natural literal used at a non-natural index"

def resolveTypeArguments (program : Namespace.Indexed) (scope : Namespace.Scope)
    (ctx : TypeContext) (parameters : List Indexed.Parameter) (arguments : List TypeArgument)
    (span : Span) : ResolveM (List Index) := do
  if parameters.length != arguments.length then
    Namespace.problem span "E_TYPE" "indexed type has the wrong number of arguments"
  (parameters.zip arguments).mapM fun (parameter, argument) =>
    resolveTypeArgument program scope ctx parameter argument

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
  | .application path arguments =>
      let id ← resolveId program scope path
      match Indexed.lookup env.indexed id with
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
