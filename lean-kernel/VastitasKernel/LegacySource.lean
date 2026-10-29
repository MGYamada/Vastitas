import VastitasKernel.NamespaceProtocol
import VastitasKernel.IndexedAcceptance
import VastitasKernel.NamespaceDiagnostics

/-! Protocols 2–6 retain their original wire schemas. This syntax adapter converts
those decoded inputs to the declaration-driven source checker; it does not run
the old geometry elaborator or accept a legacy checked Core as evidence. -/
namespace VastitasKernel.Indexed.LegacySource

inductive Input where
  | flat (program : Surface.Program)
  | package (program : Namespace.Program)
  deriving Inhabited

def decode (json : Lean.Json) : Except String Input := do
  let version ← json.getObjValAs? Nat "version"
  if version == 3 || version == 5 || version == 6 ||
      (version == 4 && (json.getObjValAs? String "input").toOption == some "package") then
    return .package (← decodeNamespaceProgram json)
  return .flat (← decodeSurfaceModule json)

private def problem (span : Span) (code message : String) : Except Diagnostic α :=
  .error { code, message, span }

private def path (flat : Bool) (name : String) (span : Span) : Except Diagnostic Source.Path := do
  let parts := name.splitOn "::"
  if parts.any (·.startsWith DispatchChecker.privatePrefix) then
    problem span "E_RESERVED" "'__vastitas_' is reserved for compiler-generated names"
  if parts.isEmpty || parts.any String.isEmpty then problem span "E_NAME" "empty source path"
  if flat && parts.length != 1 then
    problem span "E_NAME" "qualified module paths require package input"
  return ⟨parts, span⟩

private def dataType (type : RawType) (span : Span) : Except Diagnostic Source.DataType :=
  match type with
  | .named "Nat" => .ok (.pure .nat)
  | .named "Int" => .ok (.pure .int)
  | .named "Bool" => .ok (.pure .bool)
  | .named "Unit" => .ok (.pure .unit)
  | .pair "Nat" => .ok (.pure (.pair .nat))
  | .pair "Int" => .ok (.pure (.pair .int))
  | .named "Scheme" | .named "CInfScheme" | .point .. | .morphism .. | .pointed .. => .ok (.legacy type)
  | _ => problem span "E_TYPE" "unsupported data type; abstract selectors are not value types"

private def fnType (type : Surface.TypeExpr) (span : Span) : Except Diagnostic FunctionSource.FnType :=
  match type with
  | .data type => return .data (← dataType type span)
  | .function .. =>
    if type.callableData && type.withinDepth Limits.typeNesting then .ok (.function type)
    else problem span "E_TYPE" "Fn signatures contain only scalars and recursive Fn types"

private def parameter (p : Surface.Param) : Except Diagnostic FunctionSource.Param :=
  return ⟨p.name, ← fnType p.ty p.span, p.span⟩

mutual
  private def expression (flat : Bool) : Nat → Surface.Expr → Except Diagnostic FunctionSource.Expr
    | 0, term => problem term.span "E_LIMIT" "source expression nesting exceeds the supported limit"
    | fuel + 1, term => match term with
      | .integer value span => .ok (.integer value span)
      | .boolean value span => .ok (.boolean value span)
      | .unit span => .ok (.unit span)
      | .variable name span => do
        let reference ← path flat name span
        return if reference.path.length == 1 then .variable name span else .functionValue reference span
      | .call name args span => return .call (← path flat name span) (← args.mapM (expression flat fuel)) span
      | .invoke callee args span => return .invoke (← expression flat fuel callee) (← args.mapM (expression flat fuel)) span
      | .lambda params result body span => return .lambda (← params.mapM parameter) (← fnType result span) (← block flat fuel body) span
      | .reference _ span => problem span "E_PROTOCOL" "backend-only function reference in source input"
      | .unary operator value span => return .unary operator (← expression flat fuel value) span
      | .binary operator left right span => return .binary operator (← expression flat fuel left) (← expression flat fuel right) span
      | .ite condition yes no span => return .branch (← expression flat fuel condition) (← block flat fuel yes) (← block flat fuel no) span
      | .block body span => return .block (← block flat fuel body) span
      | .pack witness point span => return .pack .inferredPackage (← expression flat fuel witness) [← expression flat fuel point] span
  private def statement (flat : Bool) : Nat → Surface.Stmt → Except Diagnostic FunctionSource.Stmt
    | 0, .letE _ _ _ span | 0, .unpack _ _ _ span => problem span "E_LIMIT" "source statement nesting exceeds the supported limit"
    | fuel + 1, .letE name annotation value span =>
      return .letE name (← annotation.mapM (fnType · span)) (← expression flat fuel value) span
    | fuel + 1, .unpack value witness point span => return .unpack (← expression flat fuel value) witness [point] span
  private def block (flat : Bool) : Nat → Surface.Block → Except Diagnostic FunctionSource.Block
    | 0, .mk _ _ span => problem span "E_LIMIT" "source block nesting exceeds the supported limit"
    | fuel + 1, .mk statements result span =>
      return .mk (← statements.mapM (statement flat fuel)) (← expression flat fuel result) span
end

private def function (flat : Bool) (f : Namespace.Function) : Except Diagnostic FunctionSource.Function := do
  return {
    name := f.name, params := ← f.params.mapM parameter, result := ← fnType f.result f.span,
    body := ← block flat Limits.sourceNesting f.body, isPublic := f.isPublic, span := f.span }

private def method (flat : Bool) (m : Surface.Method) : Except Diagnostic DispatchSource.Method := do
  let .data result := m.result | problem m.span "E_TYPE" "function values are not dispatch results"
  let .pure result ← dataType result m.span | problem m.span "E_TYPE" "method results require scalar or homogeneous Pair types"
  return {
    target := ← path flat m.name m.span, params := m.params, result, requirements := m.requirements,
    body := ← block flat Limits.sourceNesting m.body, span := m.span }

private def contribution (c : Namespace.Contribution) : Except Diagnostic DispatchSource.Contribution := do
  return {
    name := c.name, target := ⟨c.target, c.span⟩, methods := ← c.methods.mapM (method false),
    span := c.span, isPublic := c.isPublic }

private def module (flat : Bool) (m : Namespace.Module) : Except Diagnostic DispatchSource.Module := do
  return {
    module := { m with functions := [], methods := [], contributions := [] }, declarations := [],
    functions := ← m.functions.mapM (function flat), methods := ← m.methods.mapM (method flat),
    contributions := ← m.contributions.mapM contribution }

/-- Adapter-owned identities are independent of display filenames. The original
namespace must validate before these private implementation packages are added. -/
def profileId : Namespace.PackageId := ⟨"vastitas:compat:2-6", "legacy_geometry", "1.0.0"⟩
def flatId : Namespace.PackageId := ⟨"vastitas:compat:flat", "legacy_flat", "1.0.0"⟩

private def rootModule : Namespace.Module := {
  path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {} }

private def reference (name : String) : Source.Path := ⟨[name], {}⟩
private def declaration (name : String) (body : Source.Body) : Source.Declaration := ⟨name, body, true, {}⟩
private def setting (base : BaseKind) : GeometrySetting Source.Path :=
  let suffix := if base == .qq then "QQ" else "Smooth"
  ⟨reference (if base == .qq then "Scheme" else "CInfScheme"),
   reference (if base == .qq then "QQ" else "CInfReal"), reference ("Base" ++ suffix),
   reference ("affine" ++ suffix), reference ("base" ++ suffix), reference ("origin" ++ suffix),
   reference ("identity" ++ suffix), reference ("dimension" ++ suffix)⟩

def geometryProfile : GeometryProfile Source.Path :=
  ⟨setting .qq, setting .cinfReal, reference "Point", reference "Morphism", reference "Pointed",
   reference "compose", reference "apply"⟩

private def settingDeclarations (base : BaseKind) : List Source.Declaration :=
  let s := setting base
  let implementation := reference (if base == .qq then "GridQQ" else "GridSmooth")
  let type : Source.ObjectType := ⟨s.domain, s.marker⟩
  [declaration s.marker.name .marker,
   declaration implementation.name (.implementation s.marker .affineDescriptor [.origin, .dimension]),
   declaration s.domain.name (.classification [reference "Objects"] [implementation]),
   declaration s.baseObject.name (.global implementation),
   declaration s.affine.name (.primitive (.descriptor implementation)),
   declaration s.base.name (.primitive (.global s.baseObject)),
   declaration s.origin.name (.primitive (.origin type geometryProfile.point s.baseObject)),
   declaration s.identity.name (.primitive (.identity type geometryProfile.morphism)),
   declaration s.dimension.name (.primitive (.dimension type))]

/-- Explicit closed declarations for old wire schemas that cannot carry library
metadata. Every declaration and role is checked by the common checker. -/
def profilePackage : DispatchSource.Package := {
  id := profileId, dependencies := [], geometryCompat := some geometryProfile,
  modules := [{ module := rootModule, declarations :=
    settingDeclarations .qq ++ settingDeclarations .cinfReal ++
    [declaration "Objects" (.classification [] [reference "GridQQ", reference "GridSmooth"]),
     declaration "Point" (.family ⟨[.object (reference "Objects"), .object (reference "Objects")], [.sameBase 0 1], .point⟩),
     declaration "Morphism" (.family ⟨[.object (reference "Objects"), .object (reference "Objects")], [.sameBase 0 1], .morphism⟩),
     declaration "Pointed" (.package ([.qq, .cinfReal].map fun base =>
       let s := setting base
       ⟨⟨s.domain, s.marker⟩, [⟨reference "Point", [.witness, .global s.baseObject]⟩]⟩)),
     declaration "compose" (.primitive (.compose (reference "Morphism"))),
     declaration "apply" (.primitive (.apply (reference "Morphism") (reference "Point")))] }] }

def Input.namespace : Input → Namespace.Program
  | .package p => p
  | .flat p => {
      file := p.file, root := flatId.source, extended := p.version == 4,
      packages := [{ id := flatId, dependencies := [], modules := [{ rootModule with
        functions := p.functions.map fun f => { toFunction := f, isPublic := true },
        generics := p.generics.map fun g => { toRawGeneric := g, isPublic := true },
        methods := p.methods,
        abstractTypes := p.abstractTypes.map fun t => { toRawAbstractType := t, isPublic := true },
        subtypes := p.subtypes, abstractMethods := p.abstractMethods }] }] }

def adapt (input : Input) : Except Diagnostic DispatchSource.Program := do
  if let .flat source := input then
    let headers := Surface.headers source
    let _ ← (DispatchChecker.validateProgram headers |>.run {}).map Prod.fst
    let nominals ← (Abstract.prepare headers.abstractTypes headers.subtypes |>.run {}).map Prod.fst
    for method in source.methods do
      for parameter in method.params do
        if parameter.ty.isFunction then problem parameter.span "E_TYPE" "function values are not dispatch selectors"
        let _ ← (Abstract.selector nominals parameter.ty.core parameter.span |>.run {}).map Prod.fst
  let source := input.namespace
  Namespace.validate source.indexed
  if source.packages.any (·.id.source == profileId.source) then
    problem {} "E_PROTOCOL" "source package collides with the reserved compatibility profile"
  let flat := match input with | .flat _ => true | _ => false
  let packages ← source.packages.mapM fun pkg => do
    return {
      id := pkg.id, dependencies := pkg.dependencies,
      modules := ← pkg.modules.mapM (module flat) : DispatchSource.Package }
  return {
    file := source.file, root := source.root, packages := packages ++ [profilePackage],
    extended := true, editable := true, authority := true }

structure CheckedInput (json : Lean.Json) (requireMain : Bool) where
  source : Input
  decoded : decode json = .ok source
  adapted : DispatchSource.Program
  adaptedFrom : adapt source = .ok adapted
  checked : AuthoritySource.CheckedProgram adapted requireMain
  accepted : AuthoritySource.checkProgram adapted requireMain = .ok checked

/-- Error presentation only: restore the original source names, without feeding
the old elaborator's body checks or Core into acceptance. -/
def describeDiagnostic (input : Input) (diagnostic : Diagnostic) : Diagnostic := Id.run do
  let diagnostic := match Namespace.lower input.namespace.indexed with
    | .ok lowered => Namespace.describeDiagnostic input.namespace lowered diagnostic false
    | .error _ => diagnostic
  match input with
  | .package _ => return diagnostic
  | .flat _ =>
    let rewrite (message : String) := message.replace (flatId.name ++ "::") ""
    return { diagnostic with
      message := rewrite diagnostic.message,
      notes := diagnostic.notes.map fun note => { note with message := rewrite note.message } }

def check (json : Lean.Json) (requireMain : Bool) : Except Diagnostic (CheckedInput json requireMain) := do
  match decoded : decode json with
  | .error message => .error { code := "E_PROTOCOL", message }
  | .ok source =>
    match adaptedFrom : adapt source with
    | .error diagnostic => .error diagnostic
    | .ok adapted =>
      match accepted : AuthoritySource.checkProgram adapted requireMain with
      | .error diagnostic => .error (describeDiagnostic source diagnostic)
      | .ok checked => .ok ⟨source, decoded, adapted, adaptedFrom, checked, accepted⟩

end VastitasKernel.Indexed.LegacySource
