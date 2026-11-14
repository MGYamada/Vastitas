import VastitasKernel.IndexedSourceTypes
import VastitasKernel.IndexedShapeSoundness

/-! Source provenance is presentation metadata only. Object equality and scope
continue to use the independently checked nominal references, never these names. -/
namespace VastitasKernel.Indexed.Source.Diagnostics

structure Origin where
  name : Option String := none
  span : Span
  reason : String
  deriving Inhabited

abbrev Origins := Std.HashMap Nat Origin

def origin (origins : Origins) : ObjectRef → Option Origin
  | .local _ brand => origins[brand]?
  | .global _ => none

def objectTypeLabel (env : Core.Declarations) (geometry : Option (GeometryProfile DeclId)) (type : Indexed.ObjectType) : String :=
  match geometry.bind (·.baseOf env.indexed type) with
  | some base => base.settingName
  | none => type.domain.name ++ "<" ++ type.marker.name ++ ">"

def objectLabel (env : Core.Declarations) (geometry : Option (GeometryProfile DeclId))
    (origins : Origins) : ObjectRef → String
  | .global id =>
    match geometry with
    | some profile =>
      if id == profile.scheme.baseObject then "Base(QQ)"
      else if id == profile.smooth.baseObject then "Base(CInfReal)" else id.name
    | none => id.name
  | .local type brand =>
    match origins[brand]? with
    | some source => source.name.getD
        s!"{objectTypeLabel env geometry type} from {source.reason} at {source.span.line}:{source.span.column}"
    | none => s!"{objectTypeLabel env geometry type} object {brand}"

def indexLabel (env : Core.Declarations) (geometry : Option (GeometryProfile DeclId))
    (origins : Origins) : Index → String
  | .domain id | .marker id | .frame id => id.name
  | .natural value => toString value
  | .object reference => objectLabel env geometry origins reference

def typeLabel (env : Core.Declarations) (geometry : Option (GeometryProfile DeclId))
    (origins : Origins) : Core.DataType → String
  | .pure .nat => "Nat" | .pure .int => "Int" | .pure .bool => "Bool" | .pure .unit => "Unit"
  | .pure (.pair .nat) => "Pair<Nat>" | .pure (.pair .int) => "Pair<Int>"
  | .object type => objectTypeLabel env geometry type
  | .indexed app | .package app =>
    let name := match geometry with
      | some profile =>
        if app.family == profile.point then "Point"
        else if app.family == profile.morphism then "Morphism"
        else if app.family == profile.pointed then "Pointed" else app.family.name
      | none => app.family.name
    name ++ "<" ++ String.intercalate ", " (app.indices.map (indexLabel env geometry origins)) ++ ">"

def objectNotes (env : Core.Declarations) (geometry : Option (GeometryProfile DeclId))
    (origins : Origins) (refs : List ObjectRef) : List DiagnosticNote := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut notes := #[]
  for ref in refs do
    if let .local _ brand := ref then
      unless seen.contains brand do
        seen := seen.insert brand
        if let some source := origins[brand]? then
          notes := notes.push {
            span := source.span,
            message := s!"object {objectLabel env geometry origins ref} was introduced here by {source.reason}" }
  return notes.toList

def generativeNotes (origins : Origins) (refs : List ObjectRef) (span : Span) : List DiagnosticNote := Id.run do
  for left in refs do
    if let some a := origin origins left then
      if a.name.isNone && (a.reason == "Affine" || a.reason.startsWith "function call '" || a.reason.startsWith "primitive '") then
        for right in refs do
          if left != right then
            if let some b := origin origins right then
              if b.name.isNone && a.reason == b.reason then
                return [{ span, message := "help: each construction or call returning an object creates a fresh object, even with equal arguments; bind the object once with let and reuse that binding" }]
  return []

/-! ## Rejected primitive calls

`validPrimitive` remains the only acceptance check. Only after it rejects a call
does `explainPrimitive` name one failed requirement, chosen from the resolved
binding and the actual operand types, never from the call's source spelling. -/

/-- The role table of each primitive binding, for the actual operand types:
the requirements of the binding's shape (`Shape.roles`). -/
def roleTable (env : Environment) (binding : PrimitiveBinding) (operands : List ValueType) :
    List RoleRequirement :=
  Shape.roles env binding.contract.shape operands

/-- Every requirement in the role table is part of the association contract, so
a reported requirement is a genuine failure of that contract: `Shape.roles_sound`
at the binding's shape. -/
theorem roleTable_sound {env : Environment} {binding : PrimitiveBinding} {allowed : List ObjectRef}
    {brand : Nat} {operands : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env binding allowed brand operands result) :
    ∀ requirement ∈ roleTable env binding operands, requirement.holds env = true :=
  Shape.roles_sound association

/-- Why `validPrimitive` rejected a call. -/
inductive PrimitiveFailure where
  /-- The declared binding is not a valid capability or family contract. -/
  | binding
  /-- An operand violates this requirement of the role table. -/
  | role (requirement : RoleRequirement)
  /-- No role requirement fails, but the result is not a valid type. -/
  | result
  deriving Repr, Inhabited, DecidableEq

/-- The precedence is the binding, then the role table in its order, then the
result. `none` means that no cause was established, including for every
accepted call. -/
def explainPrimitive (env : Environment) (binding : PrimitiveBinding) (allowed : List ObjectRef)
    (brand : Nat) (operands : List ValueType) (result : ValueType) : Option PrimitiveFailure :=
  if validPrimitive env binding allowed brand operands result then none
  else if !validPrimitiveBinding env binding then some .binding
  else match (roleTable env binding operands).find? (!·.holds env) with
    | some requirement => some (.role requirement)
    | none => if validValueType env result then none else some .result

theorem explainPrimitive_rejected {env : Environment} {binding : PrimitiveBinding}
    {allowed : List ObjectRef} {brand : Nat} {operands : List ValueType} {result : ValueType}
    {failure : PrimitiveFailure}
    (explained : explainPrimitive env binding allowed brand operands result = some failure) :
    validPrimitive env binding allowed brand operands result = false := by
  cases accepted : validPrimitive env binding allowed brand operands result
  · rfl
  · simp [explainPrimitive, accepted] at explained

theorem explainPrimitive_binding {env : Environment} {binding : PrimitiveBinding}
    {allowed : List ObjectRef} {brand : Nat} {operands : List ValueType} {result : ValueType}
    (explained : explainPrimitive env binding allowed brand operands result = some .binding) :
    validPrimitiveBinding env binding = false := by
  unfold explainPrimitive at explained
  revert explained
  split
  · simp
  · split
    · simp_all
    · split
      · simp
      · split <;> simp

theorem explainPrimitive_role {env : Environment} {binding : PrimitiveBinding}
    {allowed : List ObjectRef} {brand : Nat} {operands : List ValueType} {result : ValueType}
    {requirement : RoleRequirement}
    (explained : explainPrimitive env binding allowed brand operands result = some (.role requirement)) :
    requirement ∈ roleTable env binding operands ∧ requirement.holds env = false ∧
      ¬ PrimitiveAssociation env binding allowed brand operands result := by
  unfold explainPrimitive at explained
  split at explained
  · cases explained
  split at explained
  · cases explained
  split at explained
  · rename_i found
    simp only [Option.some.injEq, PrimitiveFailure.role.injEq] at explained
    rw [explained] at found
    have member := List.mem_of_find?_eq_some found
    have fails : requirement.holds env = false := by simpa using List.find?_some found
    refine ⟨member, fails, fun association => ?_⟩
    simp [roleTable_sound association requirement member] at fails
  · split at explained <;> cases explained

theorem explainPrimitive_result {env : Environment} {binding : PrimitiveBinding}
    {allowed : List ObjectRef} {brand : Nat} {operands : List ValueType} {result : ValueType}
    (explained : explainPrimitive env binding allowed brand operands result = some .result) :
    validValueType env result = false := by
  unfold explainPrimitive at explained
  revert explained
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split <;> simp_all

private def withArticle (role : String) : String :=
  (if "aeiou".contains role.front then "an " else "a ") ++ role

/-- Labels for two declarations; equal short names are qualified until they differ. -/
private def declarationLabels (expected actual : DeclId) : String × String :=
  if expected == actual || expected.name != actual.name then (expected.name, actual.name)
  else if expected.qualified != actual.qualified then (expected.qualified, actual.qualified)
  else (s!"{expected.qualified} in {expected.scope.package.source}",
    s!"{actual.qualified} in {actual.scope.package.source}")

/-- Labels for two objects; distinct objects with equal labels are told apart
by their declarations or introduction sites. -/
private def objectLabels (env : Core.Declarations) (geometry : Option (GeometryProfile DeclId))
    (origins : Origins) (expected actual : ObjectRef) : String × String :=
  let label := objectLabel env geometry origins
  if expected == actual || label expected != label actual then (label expected, label actual)
  else match expected, actual with
    | .global e, .global a => declarationLabels e a
    | _, _ =>
      let precise (reference : ObjectRef) := match reference with
        | .global id => id.qualified
        | .local _ brand => match origins[brand]? with
          | some source => s!"{label reference} introduced at {source.span.line}:{source.span.column}"
          | none => s!"{label reference} (object {brand})"
      (precise expected, precise actual)

/-- The primary message for an explained failure of the primitive `primitive`. -/
def explainFailure (env : Core.Declarations) (geometry : Option (GeometryProfile DeclId))
    (origins : Origins) (primitive resultLabel : String) : PrimitiveFailure → String
  | .binding => s!"{primitive} is not bound to a valid capability or family contract"
  | .result => s!"{primitive} would produce {resultLabel}, which is not a valid type"
  | .role (.family role expected actual) =>
    let (wanted, found) := declarationLabels expected actual
    s!"{primitive} requires {withArticle role} of family {wanted}, but the supplied {role} has family {found}"
  | .role (.object role field expected actual reason) =>
    let (wanted, found) := objectLabels env geometry origins expected actual
    let coefficient := match expected.type? env.indexed, actual.type? env.indexed with
      | some wantedType, some foundType =>
        if wantedType.marker == foundType.marker then ""
        else s!", whose coefficient marker {foundType.marker.name} differs from {wantedType.marker.name}"
      | _, _ => ""
    s!"{primitive} requires {withArticle role} with {field} {wanted} ({reason}), " ++
      s!"but the supplied {role} has {field} {found}{coefficient}"
  | .role (.marker role reference expected actual) =>
    let (wanted, found) := declarationLabels expected actual
    s!"{primitive} requires {withArticle role} with coefficient marker {wanted}, " ++
      s!"but the supplied {role} {objectLabel env geometry origins reference} has coefficient marker {found}"
  | .role (.domain role reference expected actual) =>
    let (wanted, found) := declarationLabels expected.domain actual.domain
    s!"{primitive} requires {withArticle role} whose domain lies within {wanted}, " ++
      s!"but the supplied {role} {objectLabel env geometry origins reference} has domain {found}"
  | .role (.frame role field expected actual reason) =>
    let (wanted, found) := declarationLabels expected actual
    s!"{primitive} requires {withArticle role} with {field} {wanted} ({reason}), " ++
      s!"but the supplied {role} has {field} {found}"
  | .role (.bound role field name frame index dimension) =>
    s!"{primitive} reads {name} {index} of {withArticle role} with {field} {frame.name}, but {frame.name} " ++
      s!"is a frame of a {dimension}-dimensional object, so the {name} must be below {dimension}"

end VastitasKernel.Indexed.Source.Diagnostics
