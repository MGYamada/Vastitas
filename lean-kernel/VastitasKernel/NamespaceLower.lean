import VastitasKernel.NamespaceValidate

/-! References, memberships and the lowering of a namespace program to Surface,
for the namespace checker (`NamespaceChecker.lean`). -/
namespace VastitasKernel.Namespace
open Surface
-- The namespace checker uses `lexOrd` as a local instance from `ImportKey`
-- (`NamespaceResolve.lean`) on.
attribute [local instance] lexOrd

structure Reference where
  scope : Scope
  path : List String
  span : Span
  target : Target
  method : Bool := false
  membership : Bool := false
  deriving Repr, Inhabited, DecidableEq

structure Lowered where
  surface : Surface.Program
  references : List Reference
  deriving Repr, Inhabited

def Authorized (reference : Reference) : Prop :=
  (reference.method = true → reference.target.kind = .generic ∧ reference.target.owner.scope = reference.scope) ∧
  (reference.membership = true → reference.target.kind = .abstractType ∧ reference.target.owner.scope = reference.scope)

def ReferencesValid (p : Indexed) (lowered : Lowered) : Prop :=
  ∀ reference ∈ lowered.references,
    (resolve p reference.scope reference.path reference.span).toOption = some reference.target ∧ Authorized reference

instance (p : Indexed) (lowered : Lowered) : Decidable (ReferencesValid p lowered) := by
  unfold ReferencesValid Authorized
  infer_instance

abbrev M := StateT (List Reference) Result

/-- Resolve a structured path component-wise; wire path lists are never
rejoined into a string and split again. -/
def lookupPath (p : Indexed) (scope : Scope) (path : List String) (span : Span) (method := false)
    (membership := false) : M Target := do
  let target ← resolve p scope path span
  if method && (target.kind != .generic || target.owner.scope != scope) then
    problem span "E_OWNER" "only the exact module defining a generic may add methods"
  if membership && (target.kind != .abstractType || target.owner.scope != scope) then
    problem span "E_OWNER" "only the exact module defining an abstract type may add scalar memberships"
  modify (⟨scope, path, span, target, method, membership⟩ :: ·)
  return target

def lookup (p : Indexed) (scope : Scope) (name : String) (span : Span) (method := false) (membership := false) : M Target :=
  lookupPath p scope (name.splitOn "::") span method membership

def binder (p : Indexed) (scope : Scope) (name : String) (span : Span) : Result String := do
  sourceName name span
  let some m := moduleLookupAt p scope | problem span "E_NAME" "unknown module"
  let some pkg := p.byPackage[scope.package.source]? | problem span "E_NAME" "unknown package"
  if p.byOwner.contains ⟨scope, name⟩ || m.imports.contains name ||
      pkg.dependencies.contains name then
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
  if target.kind != .function && target.kind != .generic then
    problem span "E_NAME" "this declaration is not a function or generic value"
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
      -- An array keeps rewriting linear in the number of statements.
      let mut output : Array Stmt := #[]
      for statement in statements do
        match statement with
        | .letE name annotation value s =>
          let renamed ← binder p scope name s
          let value ← expression fuel p scope bound value
          output := output.push (.letE renamed (annotation.map type) value s)
          bound := name :: bound
        | .unpack value scheme point s =>
          let value ← expression fuel p scope bound value
          let scheme' ← binder p scope scheme s
          let point' ← binder p scope point s
          output := output.push (.unpack value scheme' point' s)
          bound := point :: scheme :: bound
      return .mk output.toList (← expression fuel p scope bound result) span
end

def function (p : Indexed) (scope : Scope) (f : Surface.Function) (target : Target) : M Surface.Function := do
  return { f with
    name := symbol p.toProgram target
    params := ← parameters p scope f.params
    result := type f.result
    body := ← block Limits.namespaceNesting p scope (f.params.map (·.name)) f.body }

def abstractPath (p : Indexed) (scope : Scope) (path : TypePath) (membership := false) : M TypePath := do
  if path.path.length == 1 && Abstract.builtins.contains path.name then
    if membership then problem path.span "E_OWNER" "builtin subtype relations cannot be edited"
    return path
  let target ← lookup p scope path.name path.span false membership
  if target.kind != .abstractType then problem path.span "E_TYPE" "expected an abstract type declaration"
  return { path with path := [symbol p.toProgram target] }

def selectorType (p : Indexed) (scope : Scope) (ty : TypeExpr) (span : Span) : M TypeExpr := do
  match ty with
  | .data (.named name) =>
    let path ← abstractPath p scope ⟨name.splitOn "::", span⟩
    return .data (.named path.name)
  | _ => return ty

/-- Origins are reconstructed from enclosing decoded package/module declarations,
never from caller-supplied owner fields. -/
structure AbstractOrigin where
  scope : Scope
  declaration : RawAbstractType
  deriving Repr, Inhabited

structure MembershipOrigin where
  scope : Scope
  membership : RawSubtype
  deriving Repr, Inhabited

structure MembershipGraph where
  declarations : List AbstractOrigin
  memberships : List MembershipOrigin
  deriving Repr, Inhabited

def membershipGraph (p : Indexed) : Result MembershipGraph := do
  let mut declarations := []
  let mut memberships := []
  for pkg in p.packages do
    for m in pkg.modules do
      let scope : Scope := ⟨pkg.id, m.path⟩
      for declaration in m.abstractTypes do
        let parents ← declaration.parents.mapM fun path => do
          if path.path.length == 1 && Abstract.builtins.contains path.name then return path
          let target ← resolve p scope path.path path.span
          if target.kind != .abstractType then problem path.span "E_TYPE" "expected an abstract type declaration"
          return { path with path := [symbol p.toProgram target] }
        let target : Target := ⟨⟨scope, declaration.name⟩, .abstractType, declaration.isPublic⟩
        declarations := { scope, declaration := { declaration.toRawAbstractType with
          name := symbol p.toProgram target, parents } } :: declarations
      for membership in m.subtypes do
        if (Dispatch.parseScalar membership.scalar).isNone then
          problem membership.span "E_TYPE" "subtype membership requires Nat, Int, Bool, or Unit"
        let target ← resolve p scope membership.target.path membership.target.span
        if target.kind != .abstractType || target.owner.scope != scope then
          problem membership.span "E_OWNER" "only the exact module defining an abstract type may add scalar memberships"
        memberships := { scope, membership := { membership with target :=
          { membership.target with path := [symbol p.toProgram target] } } } :: memberships
  if declarations.length + Abstract.builtins.length > Limits.nominalTypes then
    problem ((declarations.head?).map (·.declaration.span) |>.getD {}) "E_LIMIT"
      s!"nominal hierarchy exceeds {Limits.nominalTypes} types including the six builtins"
  return { declarations := declarations.reverse, memberships := memberships.reverse }

def MembershipGraph.rawDeclarations (graph : MembershipGraph) : List RawAbstractType :=
  graph.declarations.map (·.declaration)

def MembershipGraph.names (graph : MembershipGraph) : List String :=
  Abstract.canonicalNames graph.rawDeclarations

def MembershipGraph.hierarchy (graph : MembershipGraph) : Dispatch.Hierarchy :=
  Abstract.build graph.rawDeclarations (graph.memberships.map (·.membership))

/-- Only abstract inheritance is used for a support path. Scalar edges cannot
circularly justify their own authority. -/
def MembershipGraph.inheritance (graph : MembershipGraph) : Dispatch.Hierarchy :=
  Abstract.build graph.rawDeclarations []

def MembershipSupported (graph : MembershipGraph) (inheritance : Dispatch.Hierarchy)
    (ancestor : AbstractOrigin) (scalar : Nat) : Prop :=
  ∃ support ∈ graph.memberships,
    support.scope = ancestor.scope ∧
    Dispatch.parseScalar support.membership.scalar = some scalar ∧
    inheritance.subtype (graph.names.idxOf support.membership.target.name)
      (graph.names.idxOf ancestor.declaration.name) = true

instance : Decidable (MembershipSupported graph inheritance ancestor scalar) := by
  unfold MembershipSupported
  infer_instance

def MembershipsAuthorized (graph : MembershipGraph) : Prop :=
  let hierarchy := graph.hierarchy
  let inheritance := graph.inheritance
  ∀ ancestor ∈ graph.declarations, ∀ scalar ∈ [0, 1, 2, 3],
    hierarchy.subtype scalar (graph.names.idxOf ancestor.declaration.name) = true →
      MembershipSupported graph inheritance ancestor scalar

instance : Decidable (MembershipsAuthorized graph) := by
  unfold MembershipsAuthorized
  infer_instance

def membershipAuthorityDiagnostic (graph : MembershipGraph) : Diagnostic := Id.run do
  let hierarchy := graph.hierarchy
  let inheritance := graph.inheritance
  for ancestor in graph.declarations do
    for scalar in [0, 1, 2, 3] do
      if hierarchy.subtype scalar (graph.names.idxOf ancestor.declaration.name) &&
          !decide (MembershipSupported graph inheritance ancestor scalar) then
        let cause := graph.memberships.find? fun m =>
          Dispatch.parseScalar m.membership.scalar == some scalar &&
          inheritance.subtype (graph.names.idxOf m.membership.target.name)
            (graph.names.idxOf ancestor.declaration.name)
        return {
          code := "E_OWNER"
          message := s!"inherited {Dispatch.nominalName scalar} membership lacks authorization from the ancestor's exact defining module"
          span := cause.map (·.membership.span) |>.getD ancestor.declaration.span
          notes := [{ span := ancestor.declaration.span, message := "this abstract selector's owner must independently declare the scalar membership" }] }
  return { code := "E_OWNER", message := "inherited scalar membership lacks owner authorization" }


def lower (p : Indexed) : Result Lowered := do
  validate p
  let action : M Surface.Program := do
    -- Arrays keep lowering linear in the number of declarations.
    let mut functions : Array Surface.Function := #[]
    let mut generics : Array RawGeneric := #[]
    let mut methods : Array Surface.Method := #[]
    let mut abstractTypes : Array RawAbstractType := #[]
    let mut subtypes : Array RawSubtype := #[]
    let mut abstractMethods : Array RawAbstractMethod := #[]
    for pkg in p.packages do
      for m in pkg.modules do
        let scope : Scope := ⟨pkg.id, m.path⟩
        for declaration in m.abstractTypes do
          let target : Target := ⟨⟨scope, declaration.name⟩, .abstractType, declaration.isPublic⟩
          abstractTypes := abstractTypes.push { declaration.toRawAbstractType with
            name := symbol p.toProgram target
            parents := ← declaration.parents.mapM (abstractPath p scope) }
        for membership in m.subtypes do
          subtypes := subtypes.push { membership with target := ← abstractPath p scope membership.target true }
        for f in m.functions do
          functions := functions.push (← function p scope f.toFunction ⟨⟨scope, f.name⟩, .function, f.isPublic⟩)
        for g in m.generics do
          let params ← g.params.mapM fun param => do
            return { param with name := ← binder p scope param.name param.span }
          generics := generics.push { g.toRawGeneric with
            name := symbol p.toProgram ⟨⟨scope, g.name⟩, .generic, g.isPublic⟩, params }
        for contract in m.abstractMethods do
          let target ← lookup p scope contract.name contract.span true
          let params ← contract.params.mapM fun param => do
            let ty ← selectorType p scope (.data param.ty) param.span
            return { param with name := ← binder p scope param.name param.span, ty := ty.core }
          let domain ← contract.domain.mapM fun clause => clause.mapM (abstractPath p scope)
          abstractMethods := abstractMethods.push { contract with
            name := symbol p.toProgram target, params, domain }
        for method in m.methods do
          let target ← lookup p scope method.name method.span true
          let params ← method.params.mapM fun param => do
            return { param with ty := ← selectorType p scope param.ty param.span }
          let f ← function p scope { method.toFunction with params } target
          methods := methods.push { f with requirements := method.requirements }
    return {
      version := if p.extended then 4 else 2, file := p.file, functions := functions.toList
      generics := generics.toList, methods := methods.toList, abstractTypes := abstractTypes.toList
      subtypes := subtypes.toList, abstractMethods := abstractMethods.toList }
  let (surface, references) ← action.run []
  return { surface, references }

end VastitasKernel.Namespace
