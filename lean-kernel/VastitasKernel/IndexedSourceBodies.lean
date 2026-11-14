import VastitasKernel.IndexedSourceDiagnostics
import VastitasKernel.NamespaceQuery

/-! Internal data-function elaboration. The public protocol-7 entry point must
also compose Fn specialization, finite dispatch and edit authority. This adapter
rejects those unsupported envelopes instead of silently dropping their bodies. -/
namespace VastitasKernel.Indexed.Source.Bodies

structure Signature where
  id : Nat
  owner : DeclId
  source : Source.Function
  context : TypeContext
  result : Core.DataType
  deriving Repr, Inhabited

structure CallReference where
  scope : Namespace.Scope
  path : Path
  target : Namespace.Target
  id : Nat
  deriving Repr, Inhabited

structure State where
  nextSymbol : Nat := 1
  origins : Diagnostics.Origins := {}
  references : List Source.Reference := []
  calls : List CallReference := []
  queries : Option Namespace.QuerySession := none
  deriving Inhabited

abbrev M := StateT State Namespace.Result

def lookupPath (index : Namespace.Indexed) (scope : Namespace.Scope) (path : Source.Path)
    (describe : Diagnostic → Diagnostic := id) : M Namespace.Target := do
  let before ← get
  let session := before.queries.getD {index}
  let (target, after) ← (session.query scope path.path path.span).mapError describe
  set {before with queries := some after}
  return target

structure Input where
  index : Namespace.Indexed
  declarations : Core.Declarations
  signatures : Std.HashMap DeclId Signature := {}
  geometry : Option (GeometryProfile DeclId) := none

def fail (span : Span) (code message : String) (notes : List DiagnosticNote := []) : M α :=
  throw { code, message, span, notes }

def checkingBudgetExceeded (span : Span) : M α :=
  fail span "E_LIMIT" s!"function exceeds the checking budget of {Limits.bodyChecking} units along one checking path"

def fresh : M Nat := do
  let symbol := (← get).nextSymbol
  modify fun state => { state with nextSymbol := symbol + 1 }
  return symbol

def rememberObject (reference : ObjectRef) (span : Span) (reason : String)
    (name : Option String := none) : M Unit := do
  if let .local _ brand := reference then
    modify fun state => { state with origins := state.origins.insert brand ⟨name, span, reason⟩ }

def freshObject (type : Indexed.ObjectType) (span : Span) (reason : String) : M ObjectRef := do
  let reference := ObjectRef.local type (← fresh)
  rememberObject reference span reason
  return reference

def nameObject (reference : Option ObjectRef) (name : String) : M Unit := do
  if let some (.local _ brand) := reference then
    if let some source := (← get).origins[brand]? then
      if source.name.isNone then
        modify fun state => { state with origins := state.origins.insert brand { source with name := some name } }

def typeLabel (input : Input) (type : Core.DataType) : M String := do
  return Diagnostics.typeLabel input.declarations input.geometry (← get).origins type

def objectNotes (input : Input) (refs : List ObjectRef) : M (List DiagnosticNote) := do
  return Diagnostics.objectNotes input.declarations input.geometry (← get).origins refs

/-- Origin notes for every object in `values`, then the generativity help. -/
def endpointNotes (input : Input) (values : List Core.Result) (span : Span) : M (List DiagnosticNote) := do
  let refs := values.flatMap Core.Result.refs
  return (← objectNotes input refs) ++ Diagnostics.generativeNotes (← get).origins refs span

def endpointFailure (input : Input) (values : List Core.Result) (span : Span) (message : String) : M α := do
  let labels ← values.mapM fun value => typeLabel input value.type
  fail span "E_ENDPOINT" (message ++ ": " ++ String.intercalate ", " labels) (← endpointNotes input values span)

/-- Restrict dependent type indices, not bare object values. An object leaving a
block retains its opening/construction identity; the Core freshness audit still
checks that identity, and ordinary object-returning calls are generative. -/
def checkEscape (input : Input) (ctx : TypeContext) (type : Core.DataType) (span : Span) : M Unit := do
  let escaped := type.refs.filter fun ref => !decide (ref.Scoped (Core.Typing.contextRefs ctx.core))
  unless escaped.isEmpty do
    fail span "E_ESCAPE" s!"{← typeLabel input type} contains a local object index; package its witness and fields before returning"
      (← objectNotes input escaped)

def bindName (input : Input) (scope : Namespace.Scope) (ctx : TypeContext)
    (name : String) (span : Span) : M Unit := do
  let _ ← Namespace.binder input.index scope name span
  if (ctx.lookup name).isSome then fail span "E_DUPLICATE" s!"binding '{name}' is already in scope"

/-- Reuse the actual type elaborator with the once-built namespace index. The
contexts here are built by parameter/let/unpack elaboration, not wire metadata. -/
def type (input : Input) (scope : Namespace.Scope) (ctx : TypeContext)
    (raw : Source.DataType) (span : Span) : M Core.DataType := do
  -- A diagnostic without a place of its own, such as one for a type of the
  -- core syntax, has the place of the annotation.
  let (type, references) ← match (elaborateDataType input.index input.declarations scope ctx raw input.geometry).run [] with
    | .ok result => pure result
    | .error diagnostic => throw (if diagnostic.span == {} then { diagnostic with span } else diagnostic)
  -- An indexed type `F<…>` has the place of the path of its family. The
  -- request has no place for `Object<D, K>` or a type of the core syntax.
  let place := match raw with | .application path _ => path.span | _ => span
  unless type.Valid input.declarations do
    let code := match raw with | .legacy (.point ..) | .legacy (.morphism ..) => "E_BASE" | _ => "E_TYPE"
    fail place code s!"invalid indexed annotation {← typeLabel input type}"
  unless type.Scoped (Core.Typing.contextRefs ctx.core) do
    fail place "E_SCOPE" "annotation contains a local object outside its scope"
  for reference in references do
    let actual ← lookupPath input.index reference.scope reference.path
    unless actual == reference.target do fail reference.path.span "E_PROTOCOL" "indexed annotation resolution differs"
  modify fun state => { state with references := references ++ state.references }
  return type

def expect (input : Input) (expected : Option Core.DataType) (value : Core.Term) (span : Span) : M Core.Term := do
  if let some expected := expected then
    unless Core.Typing.Compatible input.declarations value.result.type expected do
      let pairNotes := match expected, value with
        | .pure (.pair .nat), .pair .int (.integer first) (.integer second) =>
          if first >= 0 && second >= 0 then
            [{ span, message := "help: pair infers its operands independently; bind and annotate Nat operands first, for example let a: Nat = 0; let b: Nat = 1; pair(a, b)" }]
          else []
        | _, _ => []
      fail span "E_TYPE" s!"expected {← typeLabel input expected}, found {← typeLabel input value.result.type}"
        ((← objectNotes input (expected.refs ++ value.result.type.refs)) ++ pairNotes ++
          if expected == .pure .int && value.result.type == .pure .nat then
            [{ span, message := "help: convert explicitly with int(...); Nat values are never converted implicitly" }] else [])
  return value

def literalLike : Source.Expr → Bool
  | .integer .. => true
  | .unary "-" value _ => literalLike value
  | .binary op left right _ => ["+", "-", "*"].contains op && literalLike left && literalLike right
  | _ => false

def blockLiteralLike : Source.Block → Bool
  | .mk _ result _ => literalLike result

def integerType : Core.DataType → Bool
  | .pure .nat | .pure .int => true
  | _ => false

/-- The integer literal case of `expression`, before its `expect`. The public
body elaborator calls it as well. -/
def integerLiteral (value : String) (span : Span) (expected : Option Core.DataType) : M Core.Term := do
  unless !value.isEmpty && value.toList.all (fun c => c >= '0' && c <= '9') do
    fail span "E_LITERAL" "integer literal must contain only decimal digits"
  let some value := decimalNat? value | fail span "E_LITERAL" "invalid decimal integer"
  pure (if expected == some (.pure .nat) then .natural value else .integer (Int.ofNat value))

def primitiveResult : ValueType → Core.Result
  | .natural => ⟨.pure .nat, none⟩
  | .object type reference => ⟨.object type, some reference⟩
  | .indexed application => ⟨.indexed application, none⟩
  | .boolean => ⟨.pure .bool, none⟩
  | .integer => ⟨.pure .int, none⟩
  | .integerPair => ⟨.pure (.pair .int), none⟩

/-- Both declared calls and the legacy syntax adapter use this same primitive
contract check. The final independent Core audit remains mandatory. A rejected
call is explained from its resolved binding and actual operand types; when no
cause is established, the message lists the operand types instead. -/
def emitPrimitive (input : Input) (ctx : TypeContext) (id : DeclId)
    (values : List Core.Term) (span : Span) : M Core.Term := do
  let some binding := input.declarations.primitive? id | fail span "E_TYPE" "unknown declared primitive"
  let some operands := (values.map Core.Term.result).mapM Core.Result.primitiveType?
    | fail span "E_TYPE" "primitive operand shape mismatch"
  let brand ← if binding.allocates then fresh else pure 0
  let some output := inferPrimitiveResult input.declarations.indexed binding brand operands
    | fail span "E_TYPE" "primitive operand shape mismatch"
  let allowed := Core.Typing.contextRefs ctx.core
  unless validPrimitive input.declarations.indexed binding allowed brand operands output do
    let results := values.map Core.Term.result
    match Diagnostics.explainPrimitive input.declarations.indexed binding allowed brand operands output with
    | some failure =>
      let message := Diagnostics.explainFailure input.declarations input.geometry (← get).origins id.name
        (← typeLabel input (primitiveResult output).type) failure
      fail span "E_ENDPOINT" message (← endpointNotes input results span)
    | none => endpointFailure input results span "primitive capability, endpoint or coefficient contract failed"
  if binding.allocates then
    if let .object _ reference := output then
      let legacy := input.geometry.any fun profile => id == profile.scheme.affine || id == profile.smooth.affine
      rememberObject reference span (if legacy then "Affine" else s!"primitive '{id.name}'")
  return .primitive id values (primitiveResult output)

def requireGeometry (input : Input) (span : Span) : M (GeometryProfile DeclId) := do
  let some profile := input.geometry
    | fail span "E_TYPE" "legacy geometry syntax requires exactly one explicit library compatibility export"
  return profile

def geometryOf (input : Input) (profile : GeometryProfile DeclId) (value : Core.Term) (span : Span) : M BaseKind := do
  let .object type := value.result.type | fail span "E_TYPE" "legacy operation requires a geometric object"
  let some base := profile.baseOf input.declarations.indexed type
    | fail span "E_TYPE" "object is outside the declared legacy geometry profile"
  return base

def legacyPackage (input : Input) (witness : Core.Term) (span : Span) : M Application := do
  let profile ← requireGeometry input span
  return profile.package (← geometryOf input profile witness span)

def legacyOperation (path : List String) : Bool :=
  [["Affine"], ["Base"], ["origin"], ["id"], ["dimension"], ["compose"], ["apply"]].contains path

/-- Decided from the structured name tables, never from a diagnostic code. A
module may take the name of a geometric operation; it does not hide the
operation, because a module is not callable. -/
def legacyFallback (input : Input) (scope : Namespace.Scope) (path : Path) : Bool :=
  match path.path with
  | [name] => legacyOperation [name] &&
      (Namespace.unboundName input.index scope name || Namespace.childModule input.index scope name)
  | _ => false

/-- The fallback never hides a declaration that a call could reach: the name
resolves to nothing, or to a module. -/
theorem legacyFallback_uncallable (input : Input) (scope : Namespace.Scope) (path : Path)
    (fallback : legacyFallback input scope path = true) (target : Namespace.Target)
    (resolved : Namespace.resolve input.index scope path.path path.span = .ok target) :
    target.kind = .module := by
  unfold legacyFallback at fallback
  split at fallback
  · rename_i name single
    rw [single] at resolved
    simp only [Bool.and_eq_true, Bool.or_eq_true] at fallback
    rcases fallback.2 with unbound | child
    · obtain ⟨diagnostic, failed, _⟩ := Namespace.resolve_unboundName _ _ _ path.span unbound
      rw [failed] at resolved
      cases resolved
    · exact Namespace.resolve_childModule _ _ _ _ child target resolved
  · cases fallback

def legacyMarker (name : String) (span : Span) : M BaseKind :=
  match name with
  | "QQ" => pure .qq | "CInfReal" => pure .cinfReal
  | _ => fail span "E_RING" "Affine/Base requires QQ or CInfReal as a coefficient marker"

def emitLegacy (input : Input) (ctx : TypeContext) (name : String) (base : Option BaseKind)
    (values : List Core.Term) (span : Span) : M Core.Term := do
  let profile ← requireGeometry input span
  let id ← match name, base, values with
    | "Affine", some base, [_] => pure (profile.setting base).affine
    | "Base", some base, [] => pure (profile.setting base).base
    | "compose", none, [_, _] => pure profile.compose
    | "apply", none, [_, _] => pure profile.apply
    | "origin", none, [value] => do pure (profile.setting (← geometryOf input profile value span)).origin
    | "id", none, [value] => do pure (profile.setting (← geometryOf input profile value span)).identity
    | "dimension", none, [value] => do pure (profile.setting (← geometryOf input profile value span)).dimension
    | _, _, _ => fail span "E_ARITY" "wrong legacy geometry argument count"
  emitPrimitive input ctx id values span

/-- The restricted internal adapter must reject features whose actual bodies
or authority state it cannot compose. Public source uses the later combined
authority/Fn/dispatch checker, including source adaptation for protocols 2–6. -/
def dataOnly (p : Source.Program) : Namespace.Result Unit := do
  if p.extended || p.editable || p.authority || p.packages.any (fun pkg => pkg.modules.any fun m =>
      !m.module.functions.isEmpty || !m.module.generics.isEmpty || !m.module.methods.isEmpty ||
      !m.module.abstractTypes.isEmpty || !m.module.subtypes.isEmpty || !m.module.abstractMethods.isEmpty ||
      !m.module.grants.isEmpty || !m.module.delegations.isEmpty || !m.module.transfers.isEmpty ||
      !m.module.contributions.isEmpty || m.module.assembly.isSome) then
    Namespace.problem {} "E_STAGE" "indexed source body adapter requires data functions; full function/dispatch/edit composition is pending"

def generatedLets : Core.Term → Nat
  | .primitive _ arguments _ | .call _ arguments _ _ => (arguments.map generatedLets).sum
  | .unary _ value _ | .project _ _ value | .natToInt value | .ascribe _ value | .scope value => generatedLets value
  | .binary _ left right _ | .pair _ left right => generatedLets left + generatedLets right
  | .branch condition yes no _ => generatedLets condition + generatedLets yes + generatedLets no
  | .pack _ witness fields => generatedLets witness + (fields.map generatedLets).sum
  | .unpack _ fields value body => 2 + fields.length + generatedLets value + generatedLets body
  | .letE _ value body => 1 + generatedLets value + generatedLets body
  | _ => 0

end VastitasKernel.Indexed.Source.Bodies
